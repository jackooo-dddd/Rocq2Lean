#!/usr/bin/env python3
"""rocq2lean pilot driver.

    rocq2lean doctor
    rocq2lean inspect   --manifest SOURCE_MANIFEST --roots ROOTS
    rocq2lean export    --manifest SOURCE_MANIFEST --roots ROOTS --out RUN_DIR
    rocq2lean translate --input SOURCE_IR --out RUN_DIR
    rocq2lean verify    --run RUN_DIR
    rocq2lean status    --run RUN_DIR      (is the VERIFIED result still current? read-only)

ROOTS is a comma-separated list of fully qualified Rocq names. A SOURCE_MANIFEST is JSON:

    {"name": "...",
     "load_paths": [["-Q", "relative/dir", "Logical.Prefix"]],
     "files": ["relative/dir/A.v", ...],          # compiled in this order
     "requires": ["Logical.Prefix.A", ...]}         # loaded by the export process

Paths are relative to the manifest. Data goes to RUN_DIR; logs to RUN_DIR/logs. Every command
exits non-zero when it rejects its input.
"""

import argparse
import hashlib
import json
import os
import platform
import re
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LOCK = ROOT / "toolchains.lock.json"
EXPORTER = ROOT / "rocq" / "exporter"
HOME = Path.home()


class Rejected(Exception):
    def __init__(self, status, msg):
        super().__init__(msg)
        self.status = status
        self.msg = msg


def sha256_file(p):
    h = hashlib.sha256()
    with open(p, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def load_lock():
    return json.loads(LOCK.read_text())


def lock_sha():
    return sha256_file(LOCK)


_OPAM_ENV = None


def opam_env():
    """Environment of the pinned Rocq switch, as reported by opam itself."""
    global _OPAM_ENV
    if _OPAM_ENV is None:
        sw = load_lock()["rocq"]["opam_switch"]
        base = dict(os.environ, PATH=f"{HOME}/.local/bin:" + os.environ.get("PATH", ""))
        out = subprocess.run(["opam", "exec", f"--switch={sw}", "--", "env", "-0"],
                             capture_output=True, env=base, check=True).stdout
        _OPAM_ENV = dict(kv.split("=", 1) for kv in out.decode().split("\0") if "=" in kv)
    return _OPAM_ENV


def lean_env():
    env = dict(os.environ)
    env["PATH"] = f"{HOME}/.elan/bin:" + env.get("PATH", "")
    return env


def run(cmd, log, cwd=None, env=None, check=True):
    """Run a command, appending its command line and output to `log`."""
    log.parent.mkdir(parents=True, exist_ok=True)
    t0 = time.time()
    p = subprocess.run(cmd, cwd=cwd, env=env, capture_output=True, text=True)
    with open(log, "a") as f:
        f.write(f"$ {' '.join(map(str, cmd))}   (cwd={cwd or os.getcwd()})\n")
        f.write(p.stdout)
        f.write(p.stderr)
        f.write(f"[exit {p.returncode}, {time.time() - t0:.1f}s]\n\n")
    if check and p.returncode != 0:
        raise Rejected("COMMAND_FAILED", f"{cmd[0]} exited with {p.returncode}; see {log}")
    return p


# ---------------------------------------------------------------- doctor

def doctor(write_report=True, quiet=False):
    lock = load_lock()
    problems, env_report = [], {}
    log = ROOT / "reports" / "logs" / "doctor.log"
    if log.exists():
        log.unlink()

    tc = (ROOT / "lean-toolchain").read_text().strip()
    if tc != lock["lean"]["toolchain"]:
        problems.append(f"lean-toolchain is {tc!r}, lock requires {lock['lean']['toolchain']!r}")
    p = run(["lake", "-d", str(ROOT), "env", "lean", "--version"], log, env=lean_env(), check=False)
    lean_line = p.stdout.strip()
    if lean_line != lock["lean"]["version_line"]:
        problems.append(f"lean --version is {lean_line!r}")
    env_report["lean"] = {"toolchain": tc, "version": lean_line,
                          "lean_path": run(["lake", "-d", str(ROOT), "env", "which", "lean"], log,
                                           env=lean_env(), check=False).stdout.strip()}

    oenv = opam_env()
    p = run(["rocq", "--version"], log, env=oenv, check=False)
    lines = p.stdout.strip().splitlines()
    if not lines or lines[0] != lock["rocq"]["version_line"]:
        problems.append(f"rocq --version is {lines!r}")
    if len(lines) < 2 or lines[1] != f"compiled with OCaml {lock['rocq']['ocaml']}":
        problems.append(f"rocq OCaml line is {lines[1:]!r}")
    env_report["rocq"] = {"version": lines,
                          "rocq_path": run(["which", "rocq"], log, env=oenv, check=False).stdout.strip()}

    sw = lock["rocq"]["opam_switch"]
    p = run(["opam", "list", f"--switch={sw}", "--installed", "--columns=name,version", "--short",
             "--color=never"], log, env=oenv, check=False)
    installed = dict(l.split()[:2] for l in p.stdout.splitlines() if len(l.split()) >= 2)
    for pkg, ver in lock["rocq"]["opam_packages"].items():
        if installed.get(pkg) != ver:
            problems.append(f"opam package {pkg} is {installed.get(pkg)!r}, lock requires {ver!r}")
    p = run(["opam", "pin", "list", f"--switch={sw}", "--color=never"], log, env=oenv, check=False)
    pins = {}
    for l in p.stdout.splitlines():
        m = re.match(r"^(\S+?)\.\S+\s+git\s+\S+\s+\(at ([0-9a-f]{40})\)", l)
        if m:
            pins[m.group(1)] = m.group(2)
    for pkg, commit in lock["rocq"]["opam_git_pins"].items():
        if pins.get(pkg) != commit:
            problems.append(f"opam pin {pkg} is at {pins.get(pkg)!r}, lock requires {commit}")
    env_report["opam"] = {"switch": sw, "packages": {k: installed.get(k) for k in lock["rocq"]["opam_packages"]},
                          "git_pins": pins}

    report = {
        "schema": "rocq2lean-environment/1",
        "status": "OK" if not problems else "BLOCKED_ENVIRONMENT",
        "problems": problems,
        "toolchains_lock_sha256": lock_sha(),
        "platform": {"system": platform.system(), "release": platform.release(),
                     "machine": platform.machine(), "python": platform.python_version()},
        "checking": {"lean_insertion": "Environment.addDeclCore (doCheck := true); debug.skipKernelTC refused",
                     "rocq_flags": "per-declaration typing flags exported and audited"},
        **env_report,
    }
    if write_report:
        (ROOT / "reports").mkdir(exist_ok=True)
        (ROOT / "reports" / "environment.json").write_text(json.dumps(report, indent=2) + "\n")
    if problems:
        raise Rejected("BLOCKED_ENVIRONMENT", "; ".join(problems))
    if not quiet:
        print("doctor: OK (Lean %s; %s)" % (lean_line.split()[2].rstrip(","), lines[0]))
    return report


# ---------------------------------------------------------------- run-state helpers

IMPL_GLOBS = ["Rocq2Lean.lean", "Rocq2Lean/*.lean", "tools/*.py", "rocq/exporter/src/*.ml",
              "rocq/exporter/src/*.mlg", "rocq/exporter/src/*.mlpack", "rocq/exporter/src/META.*",
              "rocq/exporter/theories/*.v", "rocq/exporter/Makefile*", "rocq/exporter/_RocqProject",
              "rocq/roundtrip/RtEq.v", "lakefile.lean", "lake-manifest.json", "lean-toolchain",
              "toolchains.lock.json"]


def impl_files():
    files = set()
    for g in IMPL_GLOBS:
        files.update(p for p in ROOT.glob(g) if p.is_file())
    return sorted(files)


def impl_tree_sha256():
    """Content hash of the implementation (independent of git state)."""
    h = hashlib.sha256()
    for p in impl_files():
        h.update(str(p.relative_to(ROOT)).encode() + b"\0" + sha256_file(p).encode() + b"\n")
    return h.hexdigest()


_TOOLCHAIN_FP = None


def toolchain_fingerprint():
    """Content digests of the toolchain components that produce or check the artifacts, beyond the
    version strings `doctor` compares: the Lean executable, `lake` and the shared library that
    contains the kernel; the `rocq` executable; the MetaRocq Template plugins and theories. (The
    Rocq libraries the exported declarations come from are hashed per library in the snapshot.)"""
    global _TOOLCHAIN_FP
    if _TOOLCHAIN_FP is None:
        sysroot = subprocess.run(["lake", "-d", str(ROOT), "env", "printenv", "LEAN_SYSROOT"], capture_output=True,
                                 text=True, env=lean_env(), check=True).stdout.strip()
        oenv = opam_env()
        sw = load_lock()["rocq"]["opam_switch"]
        lib = Path(subprocess.run(["opam", "var", f"--switch={sw}", "lib"], capture_output=True, text=True, env=oenv,
                                  check=True).stdout.strip())
        rocq = subprocess.run(["which", "rocq"], capture_output=True, text=True, env=oenv, check=True).stdout.strip()
        files = {"lean:bin/lean": Path(sysroot) / "bin" / "lean", "lean:bin/lake": Path(sysroot) / "bin" / "lake",
                 "lean:lib/lean/libleanshared.so": Path(sysroot) / "lib" / "lean" / "libleanshared.so",
                 "rocq:bin/rocq": Path(rocq)}
        for p in sorted(lib.glob("rocq-metarocq-template-*/*.cmxs")):
            files[f"metarocq:{p.relative_to(lib)}"] = p
        for p in sorted((lib / "coq" / "user-contrib" / "MetaRocq").rglob("*.vo")):
            files[f"metarocq:{p.relative_to(lib)}"] = p
        digests = {k: sha256_file(p) for k, p in sorted(files.items())}
        h = hashlib.sha256()
        for k, d in digests.items():
            h.update(k.encode() + b"\0" + d.encode() + b"\n")
        _TOOLCHAIN_FP = {"digest": h.hexdigest(), "files": len(digests),
                         "components": {k: v for k, v in digests.items() if not k.endswith(".vo")}}
    return _TOOLCHAIN_FP


def git_identity():
    def g(*a):
        return subprocess.run(["git", "-C", str(ROOT), *a], capture_output=True, text=True).stdout.strip()
    return {"commit": g("rev-parse", "HEAD"), "dirty_paths": len(g("status", "--porcelain").splitlines())}


def atomic_write_json(path, obj):
    path = Path(path)
    tmp = path.with_name(f".{path.name}.{os.getpid()}.tmp")
    with open(tmp, "w") as f:
        f.write(json.dumps(obj, indent=2) + "\n")
        f.flush()
        os.fsync(f.fileno())
    os.replace(tmp, path)


class RunLock:
    """Exclusive lock on a run directory: concurrent writers are rejected, not interleaved."""

    def __init__(self, run):
        self.path = Path(run) / ".rocq2lean.lock"

    def __enter__(self):
        import fcntl
        self.path.parent.mkdir(parents=True, exist_ok=True)
        self.f = open(self.path, "w")
        try:
            fcntl.flock(self.f, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            raise Rejected("RUN_BUSY", f"another rocq2lean process holds {self.path}")
        return self

    def __exit__(self, *exc):
        self.f.close()


# Artifacts a phase invalidates when it starts (anything downstream of it).
DOWNSTREAM = {
    "export": ["source.ndjson", "source_snapshot.json", "contract.json", "roundtrip.json", "translation_report.json",
               "translation_manifest.json", "audit.json", "consumer_result.json", "verify.json", "lean"],
    "translate": ["translation_report.json", "translation_manifest.json", "audit.json", "consumer_result.json",
                  "verify.json", "lean"],
    "verify": ["audit.json", "consumer_result.json", "verify.json", "lean/Rocq2LeanConsumer.lean",
               "lean/Rocq2LeanConsumer.olean", "lean/Rocq2LeanConsumer.ilean"],
}


def invalidate(run, phase):
    import shutil
    for name in DOWNSTREAM[phase]:
        p = Path(run) / name
        if p.is_dir():
            shutil.rmtree(p)
        elif p.exists():
            p.unlink()


# ---------------------------------------------------------------- export

def load_manifest(path):
    path = Path(path).resolve()
    m = json.loads(path.read_text())
    base = path.parent
    lp = []
    for flag, d, logical in m.get("load_paths", []):
        if flag not in ("-Q", "-R"):
            raise Rejected("EXPORT_VALIDATION_FAILED", f"unsupported load-path flag {flag}")
        lp += [flag, str((base / d).resolve()), logical]
    files = [(base / f).resolve() for f in m.get("files", [])]
    return m, path, lp, files


def build_exporter(log):
    run(["make", "-C", str(EXPORTER)], log, env=opam_env())
    return EXPORTER / "src" / "rocq2lean_export_plugin.cmxs"


def check_request(raw):
    """Normalize the request once (strip surrounding whitespace) and reject empty or duplicate
    roots after normalization. Returns the normalized list; both lists are recorded."""
    roots = [r.strip() for r in raw]
    if not roots or any(not r for r in roots):
        raise Rejected("ROOT_CONTRACT_REJECTED", "empty root request (or an empty root name)")
    dups = sorted({r for r in roots if roots.count(r) > 1})
    if dups:
        raise Rejected("ROOT_CONTRACT_REJECTED", f"duplicate requested roots (after whitespace normalization): {dups}")
    return roots


def export(manifest, raw_roots, out, log_name="export.log"):
    roots = check_request(raw_roots)
    out = Path(out).resolve()
    with RunLock(out):
        invalidate(out, "export")          # before anything else: no earlier result survives
        doctor(write_report=False, quiet=True)
        return _export(manifest, roots, list(raw_roots), out, log_name)


def _export(manifest, roots, raw_roots, out, log_name):
    sys.path.insert(0, str(ROOT / "tools"))
    import contract as contract_mod
    m, mpath, lp, files = load_manifest(manifest)
    (out / "logs").mkdir(parents=True, exist_ok=True)
    log = out / "logs" / log_name
    if log.exists():
        log.unlink()
    plugin = build_exporter(log)
    oenv = opam_env()
    for f in files:
        run(["rocq", "compile", *lp, str(f)], log, env=oenv)
    export_v = out / "Export.v"
    ir = out / "source.ndjson"
    lines = ["From Rocq2LeanExport Require Import Loader."]
    lines += [f"Require {r}." for r in m.get("requires", [])]
    lines.append(f'Rocq2Lean Export "{ir}" {" ".join(roots)}.')
    export_v.write_text("\n".join(lines) + "\n")
    p = run(["rocq", "compile", "-I", str(EXPORTER / "src"), "-Q", str(EXPORTER / "theories"), "Rocq2LeanExport",
             *lp, str(export_v)], log, env=oenv, check=False)
    blockers = ir.with_name(ir.name + ".blockers.json")
    if p.returncode != 0 and blockers.exists():
        b = json.loads(blockers.read_text())
        raise Rejected("UNSUPPORTED_FEATURE", f"{b['reason']}; " + "; ".join(
            f"root {r['requested']} via {' -> '.join(r['path'])}" for r in b["roots"]))
    if p.returncode != 0 or not ir.exists():
        raise Rejected("EXPORT_VALIDATION_FAILED", f"export process failed (exit {p.returncode}); see {log}")
    first = json.loads(ir.open().readline())
    libs = []
    with ir.open() as fh:
        for line in fh:
            d = json.loads(line)
            if d["kind"] == "libraries":
                for l in d["libraries"]:
                    libs.append({"dirpath": l["dirpath"], "vo": l["vo"],
                                 "sha256": sha256_file(l["vo"]) if l["vo"] else None})
                break
    rt = run([sys.executable, "-I", str(ROOT / "tools" / "roundtrip.py"), str(ir), str(out), *lp, "--",
              *m.get("requires", [])], log, env=oenv, check=False)
    rt_status = json.loads((out / "roundtrip.json").read_text())["status"] if (out / "roundtrip.json").exists() \
        else "NOT_RUN"
    if rt.returncode != 0 or rt_status != "OK":
        raise Rejected("EXPORT_VALIDATION_FAILED",
                       f"independent round trip failed (exit {rt.returncode}, status {rt_status}); see {out / 'roundtrip.json'}")
    try:
        con = contract_mod.build(ir, roots)
    except contract_mod.ContractError as e:
        raise Rejected("ROOT_CONTRACT_REJECTED", str(e))
    atomic_write_json(out / "contract.json", con)
    snapshot = {
        "schema": "rocq2lean-source-snapshot/3",
        "run_id": con["run_id"],
        "manifest": str(mpath), "manifest_sha256": sha256_file(mpath),
        "request": roots,
        "request_raw": raw_roots,
        "request_normalization": "strip surrounding whitespace",
        "ir": str(ir), "ir_sha256": sha256_file(ir),
        "contract_sha256": sha256_file(out / "contract.json"),
        "roundtrip": rt_status, "roundtrip_sha256": sha256_file(out / "roundtrip.json"),
        "frontend": first["frontend"], "rocq_version": first["rocq_version"],
        "exporter_plugin_sha256": sha256_file(plugin),
        "sources": [{"file": str(f), "sha256": sha256_file(f)} for f in files],
        "libraries": libs,
        "toolchains_lock_sha256": lock_sha(),
        "toolchain_fingerprint": toolchain_fingerprint(),
        "impl_tree_sha256": impl_tree_sha256(),
    }
    atomic_write_json(out / "source_snapshot.json", snapshot)
    return ir


def inspect(manifest, roots):
    import tempfile
    sys.path.insert(0, str(ROOT / "tools"))
    import preflight
    with tempfile.TemporaryDirectory(prefix="rocq2lean-inspect-") as td:
        unquotable = {}
        try:
            ir = export(manifest, roots, td)
        except Rejected:
            bp = Path(td) / "source.ndjson.blockers.json"
            if not bp.exists():
                raise
            b = json.loads(bp.read_text())
            unquotable = {r["requested"]: {"status": "UNSUPPORTED_FEATURE", "reasons": [b["reason"]],
                                           "dependency_path": r["path"], "blocked_declaration": r["path"][-1],
                                           "locations": {b["reason"]: "<declaration>"}} for r in b["roots"]}
            rest = [r for r in roots if r.strip() not in unquotable]
            ir = export(manifest, rest, Path(td) / "rest") if rest else None
        report = preflight.preflight(ir) if ir else {"schema": "rocq2lean-preflight/2", "roots": {}, "declarations": {}}
        report["roots"].update(unquotable)
    print(json.dumps(report, indent=2))
    blocked = [r for r, v in report["roots"].items() if v["status"] != "CANDIDATE_SUPPORTED"]
    if blocked:
        raise Rejected("UNSUPPORTED_FEATURE", "preflight blockers for roots: " + "; ".join(
            f"{r} ({', '.join(report['roots'][r]['reasons'])} in {report['roots'][r]['blocked_declaration']})" for r in blocked))
    return report


# ---------------------------------------------------------------- translate

def lean_build_sha256():
    """Digest of the built translator oleans used by the generated module."""
    h = hashlib.sha256()
    for p in sorted((ROOT / ".lake" / "build" / "lib" / "lean").glob("Rocq2Lean*.olean")) + \
            sorted((ROOT / ".lake" / "build" / "lib" / "lean" / "Rocq2Lean").glob("*.olean")):
        h.update(p.name.encode() + sha256_file(p).encode())
    return h.hexdigest()


def translate(inp, out):
    inp, out = Path(inp).resolve(), Path(out).resolve()
    with RunLock(out):
        invalidate(out, "translate")
        doctor(write_report=False, quiet=True)
        return _translate(inp, out)


def _translate(inp, out):
    lean_dir = out / "lean"
    lean_dir.mkdir(parents=True, exist_ok=True)
    (out / "logs").mkdir(parents=True, exist_ok=True)
    log = out / "logs" / "translate.log"
    if log.exists():
        log.unlink()
    report = out / "translation_report.json"
    in_sha = sha256_file(inp)
    con_p = out / "contract.json"
    run_id = None
    if con_p.exists():
        con = json.loads(con_p.read_text())
        if con["ir_sha256"] == in_sha:
            run_id = con["run_id"]
    run_id = run_id or f"translate-only-{in_sha[:16]}"
    run(["lake", "-d", str(ROOT), "build", "Rocq2Lean"], log, env=lean_env())
    mod = lean_dir / "Rocq2LeanOut.lean"
    mod.write_text(f'import Rocq2Lean\n#rocq2lean_import "{inp}" "{report}" "{in_sha}" "{run_id}"\n')
    p = run(["lake", "-d", str(ROOT), "env", "lean", str(mod), "-o", str(lean_dir / "Rocq2LeanOut.olean"),
             "-i", str(lean_dir / "Rocq2LeanOut.ilean")], log, cwd=lean_dir, env=lean_env(), check=False)
    if not report.exists():
        raise Rejected("TRANSLATION_FAILED", f"no report written (exit {p.returncode}); see {log}")
    rep = json.loads(report.read_text())
    if rep.get("input_sha256") != in_sha or rep.get("run_id") != run_id:
        raise Rejected("TRANSLATION_FAILED", "report is not bound to this input/run")
    if rep.get("status") == "ROOT_CONTRACT_REJECTED":
        raise Rejected("ROOT_CONTRACT_REJECTED", f"translator refused the recorded request: {rep.get('reason')}")
    if con_p.exists() and run_id == json.loads(con_p.read_text())["run_id"]:
        want = [(r["requested"], r["canonical"]) for r in json.loads(con_p.read_text())["roots"]]
        got = [(r.get("requested"), r.get("name")) for r in rep["roots"]]
        if want != got:
            raise Rejected("ROOT_CONTRACT_REJECTED", f"report roots {got} differ from the contract roots {want}")
    rep_roots = {r["name"]: r["status"] for r in rep["roots"]}
    for name, st in rep_roots.items():
        print(f"{st:24} {name}")
    if p.returncode != 0:
        bad = sorted({st for st in rep_roots.values() if st != "TRANSLATED_AND_CHECKED"})
        raise Rejected(bad[0] if bad else "TRANSLATION_FAILED", f"translation rejected (exit {p.returncode}); see {log}")
    atomic_write_json(out / "translation_manifest.json", {
        "schema": "rocq2lean-translation-manifest/1",
        "run_id": run_id, "input": str(inp), "input_sha256": in_sha,
        "report_sha256": sha256_file(report),
        "module_lean_sha256": sha256_file(mod),
        "module_olean_sha256": sha256_file(lean_dir / "Rocq2LeanOut.olean"),
        "module_ilean_sha256": sha256_file(lean_dir / "Rocq2LeanOut.ilean"),
        "translator_build_sha256": lean_build_sha256(),
        "impl_tree_sha256": impl_tree_sha256(),
        "toolchain_sha256": toolchain_fingerprint()["digest"],
        "lean_exit": p.returncode,
    })
    return rep


# ---------------------------------------------------------------- verify

def verify(run_dir):
    run_dir = Path(run_dir).resolve()
    with RunLock(run_dir):
        invalidate(run_dir, "verify")
        try:
            doctor(write_report=False, quiet=True)
            return _verify(run_dir)
        except Rejected as e:
            atomic_write_json(run_dir / "verify.json", {"schema": "rocq2lean-verify/2", "status": e.status,
                                                        "reason": e.msg, "impl_tree_sha256": impl_tree_sha256()})
            raise


def _need(p, what):
    if not Path(p).exists():
        raise Rejected("AUDIT_REJECTED", f"missing {what}: {p}")
    return Path(p)


def bound_hashes(run_dir, snap, tm):
    """Every artifact the verdict is bound to, recomputed from disk."""
    lean_dir = run_dir / "lean"
    h = {"ir": sha256_file(snap["ir"]),
         "contract": sha256_file(run_dir / "contract.json"),
         "roundtrip": sha256_file(run_dir / "roundtrip.json"),
         "manifest": sha256_file(snap["manifest"]),
         "translation_report": sha256_file(run_dir / "translation_report.json"),
         "module_lean": sha256_file(lean_dir / "Rocq2LeanOut.lean"),
         "module_olean": sha256_file(lean_dir / "Rocq2LeanOut.olean"),
         "module_ilean": sha256_file(lean_dir / "Rocq2LeanOut.ilean"),
         "toolchains_lock": lock_sha(),
         "impl_tree": impl_tree_sha256(),
         "translator_build": lean_build_sha256(),
         "exporter_plugin": sha256_file(EXPORTER / "src" / "rocq2lean_export_plugin.cmxs"),
         "toolchain": toolchain_fingerprint()["digest"]}
    for lib in snap["libraries"]:
        if lib["vo"]:
            h["vo:" + lib["dirpath"]] = sha256_file(lib["vo"])
    for s in snap["sources"]:
        h["src:" + s["file"]] = sha256_file(s["file"])
    return h


def check_source_instances(run_dir, snap, rep, log):
    """R2B-P obligation (docs/UNIVERSE_TRANSLATION.md): for every row that relaxed a native `Set < m`
    on a proof-local level m, the Lean solution must denote a Rocq level (0 -> Set, u_l -> l) and the
    source declaration must be accepted by Rocq's kernel with m at that level, in a fresh Rocq
    process. Returns the number of declarations checked; raises on any failure (fail closed)."""
    rows = [r for r in rep["results"] if r.get("status") == "TRANSLATED_AND_CHECKED" and r.get("r2bp_levels")]
    # a level of the statement (not proof-local) makes the row a specialization of the source
    # statement at the checked instance: allowed for dependencies, never for a requested root
    roots = {r.get("name") for r in rep.get("roots", [])}
    spec = [r["source"] for r in rows if r["source"] in roots and any(x.get("in_type") for x in r["r2bp_levels"])]
    if spec:
        raise Rejected("AUDIT_REJECTED", f"requested roots whose statement would be specialized (R2B-P on a type level): {spec}")
    if not rows:
        return 0
    levels = []
    with open(snap["ir"]) as fh:
        for line in fh:
            d = json.loads(line)
            if d.get("kind") == "universe_facts":
                levels = d["levels"]
                break
    back = {"u_" + l.replace(".", "_"): l for l in levels}
    problems, cmds = [], []
    for r in rows:
        subst = []
        for x in r["r2bp_levels"]:
            sg = x["sigma"]
            if sg == {"k": "zero"}:
                subst.append(f"{x['level']}=Set")
            elif sg.get("k") == "param" and sg["n"] in back:
                subst.append(f"{x['level']}={back[sg['n']]}")
            else:
                problems.append(f"{r['source']}: solution {sg} of {x['level']} denotes no Rocq level (R2B-P restricted)")
        cmds.append(f'Rocq2Lean CheckInstance "{r["source"]}" "{";".join(subst)}".')
    if problems:
        raise Rejected("AUDIT_REJECTED", "; ".join(problems))
    m, _, lp, _ = load_manifest(snap["manifest"])
    v = run_dir / "SourceInstances.v"
    v.write_text("\n".join(["From Rocq2LeanExport Require Import Loader."] + [f"Require {q}." for q in m.get("requires", [])]
                           + cmds) + "\n")
    p = run(["rocq", "compile", "-I", str(EXPORTER / "src"), "-Q", str(EXPORTER / "theories"), "Rocq2LeanExport",
             *lp, str(v)], log, env=opam_env(), check=False)
    got = {}
    for line in (p.stdout + p.stderr).splitlines():
        if line.startswith("INSTANCE "):
            _, key, res = line.split(" ", 2)
            got[key] = res
    bad = [f"{r['source']}: {got.get(r['source'], 'not checked')}" for r in rows if got.get(r["source"]) != "INSTANCE_OK"]
    atomic_write_json(run_dir / "source_instances.json", {"checked": {r["source"]: got.get(r["source"]) for r in rows}})
    if p.returncode != 0 or bad:
        raise Rejected("AUDIT_REJECTED", "R2B-P source instance rejected by Rocq's kernel: " + "; ".join(bad))
    return len(rows)


def _verify(run_dir):
    log = run_dir / "logs" / "verify.log"
    (run_dir / "logs").mkdir(exist_ok=True)
    if log.exists():
        log.unlink()
    snap = json.loads(_need(run_dir / "source_snapshot.json", "source snapshot").read_text())
    if snap.get("schema") != "rocq2lean-source-snapshot/3":
        raise Rejected("AUDIT_REJECTED", f"unknown snapshot schema {snap.get('schema')}")
    con_p = _need(run_dir / "contract.json", "coverage contract")
    tm = json.loads(_need(run_dir / "translation_manifest.json", "translation manifest").read_text())
    report_p = _need(run_dir / "translation_report.json", "translation report")
    _need(run_dir / "roundtrip.json", "round-trip result")
    for f in ("Rocq2LeanOut.lean", "Rocq2LeanOut.olean", "Rocq2LeanOut.ilean"):
        _need(run_dir / "lean" / f, "generated module artifact")
    h0 = bound_hashes(run_dir, snap, tm)
    problems = []
    # Source anchoring.
    if snap["roundtrip"] != "OK" or h0["roundtrip"] != snap["roundtrip_sha256"]:
        problems.append("source round trip not verified or changed since export")
    if h0["contract"] != snap["contract_sha256"]:
        problems.append("coverage contract changed since export")
    if h0["ir"] != snap["ir_sha256"]:
        problems.append("source IR changed since export")
    if h0["manifest"] != snap["manifest_sha256"]:
        problems.append("source manifest changed since export")
    if h0["toolchains_lock"] != snap["toolchains_lock_sha256"]:
        problems.append("toolchain lock changed since export")
    if h0["toolchain"] != snap["toolchain_fingerprint"]["digest"]:
        problems.append("toolchain binaries (Lean, Rocq, MetaRocq) changed since export")
    for lib in snap["libraries"]:
        if lib["vo"] and h0["vo:" + lib["dirpath"]] != lib["sha256"]:
            problems.append(f"library {lib['dirpath']} changed since export")
    for s in snap["sources"]:
        if h0["src:" + s["file"]] != s["sha256"]:
            problems.append(f"source file {s['file']} changed since export")
    con = json.loads(con_p.read_text())
    if con["run_id"] != snap["run_id"] or con["ir_sha256"] != snap["ir_sha256"] or con["request"] != snap["request"]:
        problems.append("contract is not bound to this export (run id / IR digest / request)")
    if problems:
        raise Rejected("AUDIT_REJECTED", "; ".join(problems))
    # Artifact freshness: translation bound to this export and still current.
    rep = json.loads(report_p.read_text())
    if tm["run_id"] != con["run_id"] or rep.get("run_id") != con["run_id"]:
        problems.append("translation belongs to a different run")
    if tm["input_sha256"] != con["ir_sha256"] or rep.get("input_sha256") != con["ir_sha256"]:
        problems.append("translation input digest differs from the contract")
    for k, hk in (("report_sha256", "translation_report"), ("module_lean_sha256", "module_lean"),
                  ("module_olean_sha256", "module_olean"), ("module_ilean_sha256", "module_ilean"),
                  ("impl_tree_sha256", "impl_tree"), ("translator_build_sha256", "translator_build"),
                  ("toolchain_sha256", "toolchain")):
        if tm[k] != h0[hk]:
            problems.append(f"{hk} changed since translation (stale artifact or implementation)")
    if snap["impl_tree_sha256"] != h0["impl_tree"]:
        problems.append("implementation changed since export")
    if problems:
        raise Rejected("AUDIT_REJECTED", "; ".join(problems))
    # Fresh-process consumer, driven by the contract.
    lean_dir = run_dir / "lean"
    cons = lean_dir / "Rocq2LeanConsumer.lean"
    cres = run_dir / "consumer_result.json"
    cons.write_text(f'import Rocq2LeanOut\nimport Rocq2Lean.Verify\n'
                    f'#rocq2lean_verify "{con_p}" "{report_p}" "{cres}"\n')
    lp = run(["lake", "-d", str(ROOT), "env", "printenv", "LEAN_PATH"], log, env=lean_env()).stdout.strip()
    env = dict(lean_env(), LEAN_PATH=f"{lp}:{lean_dir}")
    p = run([f"{HOME}/.elan/bin/lean", str(cons)], log, cwd=lean_dir, env=env, check=False)
    consumer = json.loads(cres.read_text()) if cres.exists() else {"status": "NOT_RUN", "detectors": {}}
    if p.returncode != 0 or consumer.get("status") != "OK":
        raise Rejected("AUDIT_REJECTED", f"consumer check failed (exit {p.returncode}): "
                       f"{[d for d, v in consumer.get('detectors', {}).items() if v != 'OK']}; see {cres}")
    # Independent structural audit, driven by the contract.
    p = run([sys.executable, "-I", str(ROOT / "tools" / "audit.py"), snap["ir"], str(con_p), str(report_p),
             str(run_dir / "audit.json"), str(cres)], log, check=False)
    audit = json.loads((run_dir / "audit.json").read_text()) if (run_dir / "audit.json").exists() else {}
    if p.returncode != 0 or audit.get("status") != "OK":
        raise Rejected("AUDIT_REJECTED", f"structural audit failed (exit {p.returncode}); see {run_dir / 'audit.json'}")
    # Source-side obligations of the cumulativity tier (R2B-P): each relaxed proof-local level's
    # solution must denote a Rocq level at which Rocq's kernel accepts the source declaration.
    n_inst = check_source_instances(run_dir, snap, rep, log)
    # Re-hash everything before publishing: nothing may have changed during verification.
    h1 = bound_hashes(run_dir, snap, tm)
    if h1 != h0:
        changed = sorted(k for k in h0 if h0[k] != h1.get(k))
        raise Rejected("AUDIT_REJECTED", f"artifacts changed during verification: {changed}")
    result = {
        "schema": "rocq2lean-verify/2", "status": "VERIFIED", "run_id": con["run_id"],
        "request": con["request"], "roots": con["roots"],
        "required_closure_size": len(con["required_closure"]), "extra_exported": con["extra_exported"],
        "gates": {
            "source_anchoring": "OK (snapshot hashes, round trip, contract binding)",
            "root_and_closure_coverage": f"OK (consumer coverage detector; audit {audit.get('coverage', {})})",
            "kernel_insertion": "OK (every accepted declaration was added through addDeclCore doCheck=true at translation)",
            "fresh_readback": "OK (separate Lean process imported the module and re-checked type/value/levels against the report)",
            "assumptions": "OK (collectAxioms empty for every accepted declaration)",
            "structural_audit": "OK",
            "source_instances": f"OK ({n_inst} R2B-P declaration(s) re-checked by Rocq's kernel at their instances)",
            "artifact_freshness": "OK (all bound hashes equal before and after verification)",
        },
        "consumer_detectors": consumer.get("detectors"),
        "audit_summary": audit.get("coverage"),
        "bound_sha256": h1,
        "toolchain_fingerprint": snap["toolchain_fingerprint"],
        "git": git_identity(),
        "note": "fresh_readback imports the .olean; it does not re-typecheck declarations from scratch "
                "(kernel checking happened at insertion; a clean rebuild is separate evidence)",
    }
    atomic_write_json(run_dir / "verify.json", result)
    print("VERIFIED", run_dir)
    return result


# ---------------------------------------------------------------- status

def status(run_dir):
    """Is the run's VERIFIED result still current? Read-only: recomputes every digest the verdict
    is bound to (sources, libraries, IR, contract, round trip, report, generated module,
    implementation, translator build, exporter plugin, toolchain) and compares them with
    verify.json. Exit 0 only for VERIFIED_CURRENT."""
    run_dir = Path(run_dir).resolve()
    with RunLock(run_dir):
        vp = run_dir / "verify.json"
        if not vp.exists():
            raise Rejected("NOT_VERIFIED", f"no verification result in {run_dir}")
        v = json.loads(vp.read_text())
        if v.get("status") != "VERIFIED":
            raise Rejected("NOT_VERIFIED", f"last verification ended with {v.get('status')}: {v.get('reason', '')}")
        try:
            snap = json.loads((run_dir / "source_snapshot.json").read_text())
            tm = json.loads((run_dir / "translation_manifest.json").read_text())
            h = bound_hashes(run_dir, snap, tm)
        except (OSError, KeyError, ValueError) as e:
            raise Rejected("STALE", f"an artifact the verdict is bound to is missing or unreadable: {e}")
        old = v.get("bound_sha256", {})
        changed = sorted(k for k in set(h) | set(old) if h.get(k) != old.get(k))
        if changed:
            raise Rejected("STALE", f"artifacts changed since verification: {changed}")
        print(json.dumps({"status": "VERIFIED_CURRENT", "run_id": v["run_id"], "request": v["request"],
                          "bound_artifacts": len(h)}, indent=2))


# ---------------------------------------------------------------- main

def main(argv=None):
    ap = argparse.ArgumentParser(prog="rocq2lean")
    sub = ap.add_subparsers(dest="cmd", required=True)
    sub.add_parser("doctor")
    for name in ("inspect", "export"):
        s = sub.add_parser(name)
        s.add_argument("--manifest", required=True)
        s.add_argument("--roots", required=True)
        if name == "export":
            s.add_argument("--out", required=True)
    s = sub.add_parser("translate")
    s.add_argument("--input", required=True)
    s.add_argument("--out", required=True)
    s = sub.add_parser("verify")
    s.add_argument("--run", required=True)
    s = sub.add_parser("status")
    s.add_argument("--run", required=True)
    a = ap.parse_args(argv)
    try:
        if a.cmd == "doctor":
            doctor()
        elif a.cmd == "inspect":
            inspect(a.manifest, a.roots.split(","))
        elif a.cmd == "export":
            print(export(a.manifest, a.roots.split(","), a.out))
        elif a.cmd == "translate":
            translate(a.input, a.out)
        elif a.cmd == "verify":
            verify(a.run)
        elif a.cmd == "status":
            status(a.run)
    except Rejected as e:
        print(f"{e.status}: {e.msg}", file=sys.stderr)
        return 2
    except Exception as e:  # tool failure, distinguished from a rejection
        print(f"TOOL_FAILURE: {type(e).__name__}: {e}", file=sys.stderr)
        return 3
    return 0


if __name__ == "__main__":
    sys.exit(main())

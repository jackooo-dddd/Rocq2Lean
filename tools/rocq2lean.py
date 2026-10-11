#!/usr/bin/env python3
"""rocq2lean pilot driver.

    rocq2lean doctor
    rocq2lean inspect   --manifest SOURCE_MANIFEST --roots ROOTS
    rocq2lean export    --manifest SOURCE_MANIFEST --roots ROOTS --out RUN_DIR
    rocq2lean translate --input SOURCE_IR --out RUN_DIR
    rocq2lean verify    --run RUN_DIR
    rocq2lean validate  --run RUN_DIR      (statement mode: validate the statement library)
    rocq2lean tasks     --run RUN_DIR [--out FILE]          (statement mode: proof tasks)
    rocq2lean check-proof --run RUN_DIR --task ID --file PROOF.lean [--allow-axioms A,B]
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
              "toolchains.lock.json", "tools/protected_interface.pin.json"]


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
               "translation_manifest.json", "audit.json", "consumer_result.json", "verify.json", "validate.json",
               "lean"],
    "translate": ["translation_report.json", "translation_manifest.json", "audit.json", "consumer_result.json",
                  "verify.json", "validate.json", "lean"],
    "verify": ["audit.json", "consumer_result.json", "verify.json", "lean/Rocq2LeanConsumer.lean",
               "lean/Rocq2LeanConsumer.olean", "lean/Rocq2LeanConsumer.ilean"],
    "validate": ["audit.json", "consumer_result.json", "validate.json", "lean/Rocq2LeanConsumer.lean",
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


def export(manifest, raw_roots, out, log_name="export.log", mode="proof"):
    roots = check_request(raw_roots)
    out = Path(out).resolve()
    with RunLock(out):
        invalidate(out, "export")          # before anything else: no earlier result survives
        doctor(write_report=False, quiet=True)
        return _export(manifest, roots, list(raw_roots), out, log_name, mode)


def _export(manifest, roots, raw_roots, out, log_name, mode="proof"):
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
    # statement mode (docs/STATEMENT_ONLY_DESIGN.md): proof bodies omitted, proof subterms of kept terms
    # extracted as obligations by Rocq's kernel; the proof-preserving export is unchanged
    cmd = {"proof": "Export", "statement": "ExportStatements"}[mode]
    lines.append(f'Rocq2Lean {cmd} "{ir}" {" ".join(roots)}.')
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
    # P0: the pinned protected public interface, bound to this export's contract (refused when the
    # manifest is missing, altered or stale)
    sys.path.insert(0, str(ROOT / "tools"))
    import protection
    try:
        with ir.open() as fh:
            names = [json.loads(l)["name"] for l in fh if l.startswith('{"kind":"constant"') or l.startswith('{"kind":"inductive"')]
        prot = protection.binding(names)
    except protection.ProtectionError as e:
        raise Rejected("EXPORT_VALIDATION_FAILED", f"protection: {e}")
    try:
        con = contract_mod.build(ir, roots, protection=prot)
    except contract_mod.ContractError as e:
        raise Rejected("ROOT_CONTRACT_REJECTED", str(e))
    atomic_write_json(out / "contract.json", con)
    snapshot = {
        "schema": "rocq2lean-source-snapshot/3",
        "mode": mode,
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
    # P0: the contract (when this run's export wrote one for this IR) carries the protection binding
    # that the translator enforces; a translate-only run has none (protection: null, not verifiable)
    prot_args = f' "{con_p}" "{sha256_file(con_p)}"' if run_id and not run_id.startswith("translate-only") else ""
    mod.write_text(f'import Rocq2Lean\n#rocq2lean_import "{inp}" "{report}" "{in_sha}" "{run_id}"{prot_args}\n')
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
    # statement mode: the module of the claimed rows exists and can be validated; untranslated roots
    # still make translate fail
    if rep.get("status") == "ROOTS_NOT_TRANSLATED":
        n = sum(1 for st in rep_roots.values() if st not in ("TRANSLATED_AND_CHECKED", "STATEMENT_KERNEL_CHECKED",
                                                             "PENDING_KERNEL_CHECKED", "STATEMENT_PENDING_KERNEL_CHECKED"))
        raise Rejected("ROOTS_NOT_TRANSLATED", f"{n} requested root(s) not translated; the claimed rows can be validated")
    return rep


# ---------------------------------------------------------------- verify

def _mode_guard(run_dir, mode):
    """Refuse a run of the other mode before anything is invalidated."""
    cp = run_dir / "contract.json"
    if cp.exists():
        got = json.loads(cp.read_text()).get("mode", "proof")
        if got != mode:
            raise Rejected("AUDIT_REJECTED", f"a {got}-mode run cannot be checked by {'validate' if mode == 'statement' else 'verify'} "
                           f"(use {'verify' if got == 'proof' else 'validate'})")


def verify(run_dir):
    run_dir = Path(run_dir).resolve()
    with RunLock(run_dir):
        _mode_guard(run_dir, "proof")
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


def _verify(run_dir, mode="proof"):
    log = run_dir / "logs" / ("validate.log" if mode == "statement" else "verify.log")
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
    if (con.get("mode") == "statement") != (mode == "statement"):
        raise Rejected("AUDIT_REJECTED", f"a {con.get('mode', 'proof')}-mode run cannot be checked by "
                       f"{'validate' if mode == 'statement' else 'verify'} (use {'verify' if mode == 'statement' else 'validate'})")
    if con["run_id"] != snap["run_id"] or con["ir_sha256"] != snap["ir_sha256"] or con["request"] != snap["request"]:
        problems.append("contract is not bound to this export (run id / IR digest / request)")
    # P0: the protection binding is present and equals the one recomputed now from the pinned manifest
    # and the exported declarations (omitted, altered or stale protection data is refused)
    sys.path.insert(0, str(ROOT / "tools"))
    import protection
    try:
        want = protection.binding(con.get("exported", []))
        if con.get("protection") != want:
            problems.append("protection binding of the contract differs from the pinned protected interface "
                            "(omitted, altered or stale)")
    except protection.ProtectionError as e:
        problems.append(f"protection: {e}")
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
    if mode == "statement":
        return _validate_finish(run_dir, snap, tm, con, rep, consumer, audit, h0, log)
    # P0 interface protection (after the consumer and the audit, which check it independently): the
    # translation ran under this very contract's binding, and no protected row is specialized
    prot = rep.get("protection") or {}
    if prot.get("contract_sha256") != sha256_file(con_p) or prot.get("protected_in_export") != len(con["protection"]["protected"]):
        raise Rejected("AUDIT_REJECTED", "translation was not run under this contract's protection binding")
    pset = set(con["protection"]["protected"])
    narrowed = [r["source"] for r in rep["results"] if r["source"] in pset and r.get("status") == "TRANSLATED_AND_CHECKED"
                and (r.get("sort_lowered_levels") or any(x.get("in_type") for x in r.get("r2bp_levels") or []))]
    if narrowed:
        raise Rejected("AUDIT_REJECTED", f"protected public declarations translated with a specialized statement: {narrowed}")
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


# ---------------------------------------------------------------- validate (statement mode)

ACCEPTED_ST = ("TRANSLATED_AND_CHECKED", "BOOTSTRAP_RESOLVED", "STATEMENT_KERNEL_CHECKED")
PENDING_ST = ("PENDING_KERNEL_CHECKED", "STATEMENT_PENDING_KERNEL_CHECKED")


def validate(run_dir):
    """Statement mode (docs/STATEMENT_ONLY_DESIGN.md): the gates of `verify` (source anchoring,
    artifact freshness, fresh-process consumer, independent audit, interface protection) applied to
    the rows the translator claims — accepted definitions and statements, and pending artifacts —
    and a per-declaration verdict. Rows not claimed are reported (with their reasons), never
    accepted."""
    run_dir = Path(run_dir).resolve()
    with RunLock(run_dir):
        _mode_guard(run_dir, "statement")
        invalidate(run_dir, "validate")
        try:
            doctor(write_report=False, quiet=True)
            return _verify(run_dir, mode="statement")
        except Rejected as e:
            atomic_write_json(run_dir / "validate.json", {"schema": "rocq2lean-validate/1", "status": e.status,
                                                          "reason": e.msg, "impl_tree_sha256": impl_tree_sha256()})
            raise


def _validate_finish(run_dir, snap, tm, con, rep, consumer, audit, h0, log):
    prot = rep.get("protection") or {}
    if prot.get("contract_sha256") != sha256_file(run_dir / "contract.json") or \
            prot.get("protected_in_export") != len(con["protection"]["protected"]):
        raise Rejected("AUDIT_REJECTED", "translation was not run under this contract's protection binding")
    pset = set(con["protection"]["protected"])
    narrowed = [r["source"] for r in rep["results"] if r["source"] in pset and r.get("status") in ACCEPTED_ST + PENDING_ST
                and (r.get("sort_lowered_levels") or any(x.get("in_type") for x in r.get("r2bp_levels") or []))]
    if narrowed:
        raise Rejected("AUDIT_REJECTED", f"protected public declarations translated with a specialized statement: {narrowed}")
    # R2B-P source instances: checked for accepted definitions (as in verify); a pending artifact
    # with an R2B-P level is not validated (its instance would need the statement preparation)
    pend_r2bp = [r["source"] for r in rep["results"] if r.get("status") in PENDING_ST and r.get("r2bp_levels")]
    if pend_r2bp:
        raise Rejected("AUDIT_REJECTED", f"pending artifacts with R2B-P levels (source instance not checkable): {pend_r2bp}")
    n_inst = check_source_instances(run_dir, snap, rep, log)
    h1 = bound_hashes(run_dir, snap, tm)
    if h1 != h0:
        changed = sorted(k for k in h0 if h0[k] != h1.get(k))
        raise Rejected("AUDIT_REJECTED", f"artifacts changed during validation: {changed}")
    verdict = {}
    for v in audit.get("verdicts", []):
        st = v.get("status")
        if v.get("verdict") != "MATCH":
            verdict[v["source"]] = {"NOT_ACCEPTED": "NOT_TRANSLATED"}.get(v.get("verdict"), "AUDIT_REJECTED")
        elif v.get("leaf"):
            verdict[v["source"]] = "STATEMENT_AUDITED" if st == "STATEMENT_KERNEL_CHECKED" else "STATEMENT_AUDITED_PENDING"
        elif st in PENDING_ST:
            verdict[v["source"]] = "DEFINITION_AUDITED_PENDING"
        else:
            verdict[v["source"]] = "DEFINITION_AUDITED"
    rows = {r["source"]: r for r in rep["results"]}
    roots = [{"requested": r["requested"], "name": r["canonical"], "status": rows[r["canonical"]]["status"],
              "validation": verdict.get(r["canonical"]),
              "pending_prerequisites": rows[r["canonical"]].get("pending_hypotheses") or []} for r in con["roots"]]
    from collections import Counter
    result = {
        "schema": "rocq2lean-validate/1", "status": "STATEMENT_VALIDATED", "mode": "statement",
        "run_id": con["run_id"], "request": con["request"], "roots": roots,
        "declarations": len(rows), "by_validation": dict(sorted(Counter(verdict.values()).items())),
        "not_translated": {s: {"status": rows[s]["status"], "message": (rows[s].get("message") or "")[:300]}
                           for s, v in sorted(verdict.items()) if v == "NOT_TRANSLATED"},
        "gates": {
            "source_anchoring": "OK (snapshot hashes, round trip incl. statement preparation, contract binding)",
            "kernel_insertion": "OK (every claimed declaration was added through addDeclCore doCheck=true at translation)",
            "fresh_readback": "OK (separate Lean process re-read every claimed declaration against the report)",
            "assumptions": "OK (collectAxioms empty for every claimed declaration; no theorem, opaque or axiom)",
            "structural_audit": "OK (statements against the source types, definitions against the prepared bodies, "
                                "hypothesis telescopes against the recomputed prerequisites)",
            "interface": "OK (no protected declaration specialized)",
            "source_instances": f"OK ({n_inst} R2B-P definition(s) re-checked by Rocq's kernel at their instances)",
            "artifact_freshness": "OK (all bound hashes equal before and after validation)",
        },
        "consumer_detectors": consumer.get("detectors"),
        "audit_summary": audit.get("coverage"),
        "bound_sha256": h1,
        "toolchain_fingerprint": snap["toolchain_fingerprint"],
        "git": git_identity(),
        "note": "STATEMENT_VALIDATED certifies the claimed rows; proofs of the statements are tasks (PROOF_PENDING) "
                "for a separate proving agent and are never produced by Rocq2Lean",
    }
    atomic_write_json(run_dir / "validate.json", result)
    print("STATEMENT_VALIDATED", run_dir, json.dumps(result["by_validation"]))
    return result


# ---------------------------------------------------------------- proof tasks (statement mode)

DEFAULT_ALLOWED_AXIOMS = ["propext", "Quot.sound", "Classical.choice"]


def _current_validation(run_dir):
    """The run's STATEMENT_VALIDATED result, refused unless every artifact it is bound to is unchanged."""
    vp = run_dir / "validate.json"
    if not vp.exists():
        raise Rejected("NOT_VALIDATED", f"no statement validation in {run_dir} (run `rocq2lean validate`)")
    v = json.loads(vp.read_text())
    if v.get("status") != "STATEMENT_VALIDATED":
        raise Rejected("NOT_VALIDATED", f"last validation ended with {v.get('status')}: {v.get('reason', '')}")
    snap = json.loads((run_dir / "source_snapshot.json").read_text())
    tm = json.loads((run_dir / "translation_manifest.json").read_text())
    h = bound_hashes(run_dir, snap, tm)
    changed = sorted(k for k in set(h) | set(v["bound_sha256"]) if h.get(k) != v["bound_sha256"].get(k))
    if changed:
        raise Rejected("STALE", f"artifacts changed since validation: {changed}")
    return v


def _lean_in_run(run_dir, module_text, name, log, extra_path=()):
    lean_dir = run_dir / "lean"
    f = Path(extra_path[0]) / f"{name}.lean" if extra_path else lean_dir / f"{name}.lean"
    f.write_text(module_text)
    lp = run(["lake", "-d", str(ROOT), "env", "printenv", "LEAN_PATH"], log, env=lean_env()).stdout.strip()
    env = dict(lean_env(), LEAN_PATH=":".join([lp, str(lean_dir), *map(str, extra_path)]))
    return run([f"{HOME}/.elan/bin/lean", str(f), "-o", str(f.with_suffix(".olean"))], log, cwd=f.parent, env=env, check=False)


def tasks(run_dir, out=None):
    """PROOF_TASKS.jsonl of a validated statement run: one task per proof-task statement (theorem
    statement, extracted obligation, opaque data value), with its source identity, the Lean statement to
    prove, the reserved name, prerequisites, validation evidence, a stable id and a priority (how many
    pending definitions need it). Rocq2Lean states tasks; it never proves them."""
    run_dir = Path(run_dir).resolve()
    with RunLock(run_dir):
        v = _current_validation(run_dir)
        return build_tasks(run_dir, {"run_id": v["run_id"], "validate_sha256": sha256_file(run_dir / "validate.json")},
                           out, json.loads((run_dir / "source_snapshot.json").read_text())["ir"])


def build_tasks(run_dir, evidence, out=None, ir_path=None):
    """The task records of a run whose claimed rows were checked (consumer + audit); `evidence` is
    recorded in every task. Used by `tasks` (after a current validation) and by the corpus driver."""
    run_dir = Path(run_dir).resolve()
    log = run_dir / "logs" / "tasks.log"
    (run_dir / "logs").mkdir(exist_ok=True)
    rep = json.loads((run_dir / "translation_report.json").read_text())
    rows = {r["source"]: r for r in rep["results"]}
    ir = {}
    with open(ir_path or run_dir / "source.ndjson") as fh:
        for line in fh:
            d = json.loads(line)
            if d.get("kind") in ("constant", "inductive"):
                ir[d["name"]] = d
    audit = json.loads((run_dir / "audit.json").read_text())
    verdict = {x["source"]: x for x in audit["verdicts"]}
    inv = {}
    invp = ROOT / "reports" / "prosa_inventory" / "declarations.jsonl"
    if invp.exists():
        for line in open(invp):
            d = json.loads(line)
            inv[d["name"]] = d
    leaves = [n for n, r in rows.items() if r["status"] in ("STATEMENT_KERNEL_CHECKED", "STATEMENT_PENDING_KERNEL_CHECKED")
              and verdict.get(n, {}).get("verdict") == "MATCH"]
    lean_dir = run_dir / "lean"
    tin = lean_dir / "tasks_in.json"
    tout = lean_dir / "tasks_out.json"
    tin.write_text(json.dumps([{"statement_constant": rows[n]["target"], "hypotheses": len(rows[n].get("pending_hypotheses") or [])}
                               for n in leaves]))
    p = _lean_in_run(run_dir, f'import Rocq2LeanOut\nimport Rocq2Lean.Tasks\n#rocq2lean_render_tasks "{tin}" "{tout}"\n',
                     "Rocq2LeanTasks", log)
    if p.returncode != 0 or not tout.exists():
        raise Rejected("TOOL_FAILURE", f"task rendering failed; see {log}")
    rendered = {x["statement_constant"]: x for x in json.loads(tout.read_text())}
    need = {}
    sole = {}
    for n, r in rows.items():
        if r["status"] in ("PENDING_KERNEL_CHECKED", "STATEMENT_PENDING_KERNEL_CHECKED"):
            hs = r.get("pending_hypotheses") or []
            for h in hs:
                need.setdefault(h, set()).add(n)
            if len(hs) == 1:
                sole.setdefault(hs[0], set()).add(n)
    fam = lambda n: inv.get(n, {}).get("family", "external")
    recs = []
    for n in leaves:
        r, d = rows[n], ir[n]
        rd = rendered[r["target"]]
        st = d.get("body_state")
        if st == "obligation":
            kind = "obligation"
        elif st == "opaque_interface":
            kind = "opaque_value"
        elif inv.get(n, {}).get("nature") == "assumption":
            kind = "source_assumption"
        else:
            kind = "theorem_statement"
        ty_sha = hashlib.sha256(json.dumps(rd["task_type"], sort_keys=True).encode()).hexdigest()
        tid = hashlib.sha256(f"{n}\n{ty_sha}".encode()).hexdigest()
        comps = [c for part in n.split("/") for c in part.split(".")]
        src = inv.get(n, {})
        recs.append({
            "schema": "rocq2lean-proof-task/1", "task_id": tid, "status": "PROOF_PENDING", "kind": kind,
            "source": {"kernel_name": n, "family": fam(n), "module": src.get("module") or d.get("name").rsplit(".", 1)[0],
                       "file": src.get("file"), "line": (src.get("source") or {}).get("line"),
                       "keyword": (src.get("source") or {}).get("keyword"),
                       "obligation_of": (d.get("native") or {}).get("obligation", {}).get("of") if kind == "obligation" else None,
                       "counted_as_proved": False if kind == "source_assumption" else None},
            "lean": {"statement_constant": r["target"], "level_params": rd["level_params"],
                     "statement": rd["statement_pp"], "task_statement": rd["task_type_pp"],
                     "task_statement_sha256": ty_sha,
                     "reserved_name": "Rocq." + ".".join(comps),
                     "declaration_kind": "def or theorem (a value of the type)" if kind == "opaque_value" else "theorem",
                     "required_modules": ["Rocq2LeanOut"],
                     "output_module": "RocqProofs." + ".".join(comps), "output_file": "RocqProofs/" + "/".join(comps) + ".lean"},
            "prerequisites": {"pending": r.get("pending_hypotheses") or [], "proved": [],
                              "note": "the task statement is generalized over its prerequisites; they bind only the assembly"},
            "priority": {"pending_declarations_needing_it": len(need.get(n, ())),
                         "sole_prerequisite_of": len(sole.get(n, ())),
                         "in_scope_needing_it": sum(1 for x in need.get(n, ()) if fam(x) in ("modern", "classic"))},
            "validation": dict(evidence, row_status=r["status"], audit_verdict="MATCH"),
            "allowed_axioms": DEFAULT_ALLOWED_AXIOMS,
        })
    recs.sort(key=lambda x: (-x["priority"]["pending_declarations_needing_it"], x["source"]["kernel_name"]))
    text = "".join(json.dumps(x, sort_keys=True) + "\n" for x in recs)
    (run_dir / "PROOF_TASKS.jsonl").write_text(text)
    if out:
        Path(out).parent.mkdir(parents=True, exist_ok=True)
        Path(out).write_text(text)
    from collections import Counter
    print(f"{len(recs)} proof task(s): {dict(Counter(x['kind'] for x in recs))}")
    return recs


def check_proof(run_dir, task_id, file, allow_axioms=None):
    """Check a proof submitted for one task: compiled in a fresh Lean process against the validated
    statement library, then checked in another fresh process (`#rocq2lean_check_proof`). Rocq2Lean
    never writes proofs; this only verifies one."""
    run_dir = Path(run_dir).resolve()
    with RunLock(run_dir):
        _current_validation(run_dir)
        tp = run_dir / "PROOF_TASKS.jsonl"
        if not tp.exists():
            raise Rejected("NOT_VALIDATED", "no proof tasks in this run (run `rocq2lean tasks`)")
        task = next((json.loads(l) for l in open(tp) if json.loads(l)["task_id"] == task_id), None)
        if task is None:
            raise Rejected("PROOF_REJECTED", f"no task {task_id} in this run")
        d = run_dir / "proofs" / task_id
        if d.exists():
            import shutil
            shutil.rmtree(d)
        d.mkdir(parents=True)
        log = d / "check.log"
        (d / "Proof.lean").write_text(Path(file).read_text())
        allowed = DEFAULT_ALLOWED_AXIOMS if allow_axioms is None else [a for a in allow_axioms.split(",") if a]
        tj = {"task_id": task_id, "reserved_name": task["lean"]["reserved_name"],
              "statement_constant": task["lean"]["statement_constant"],
              "hypotheses": len(task["prerequisites"]["pending"]), "kind": task["kind"], "allowed_axioms": allowed}
        (d / "task.json").write_text(json.dumps(tj))
        res = {"schema": "rocq2lean-check-proof/1", "task_id": task_id, "file_sha256": sha256_file(d / "Proof.lean")}
        lean_dir = run_dir / "lean"
        lp = run(["lake", "-d", str(ROOT), "env", "printenv", "LEAN_PATH"], log, env=lean_env()).stdout.strip()
        env = dict(lean_env(), LEAN_PATH=":".join([lp, str(lean_dir), str(d)]))
        p = run([f"{HOME}/.elan/bin/lean", "Proof.lean", "-o", "Proof.olean"], log, cwd=d, env=env, check=False)
        if p.returncode != 0:
            res.update(status="PROOF_REJECTED", stage="compile", problems=["the submitted module does not compile; see check.log"])
        else:
            (d / "Check.lean").write_text(f'import Rocq2LeanOut\nimport Proof\nimport Rocq2Lean.Tasks\n'
                                          f'#rocq2lean_check_proof "{d / "task.json"}" "{d / "checker.json"}"\n')
            p = run([f"{HOME}/.elan/bin/lean", "Check.lean"], log, cwd=d, env=env, check=False)
            ck = json.loads((d / "checker.json").read_text()) if (d / "checker.json").exists() else {}
            res.update(status=ck.get("status", "PROOF_REJECTED") if p.returncode == 0 or ck.get("status") == "PROOF_REJECTED" else "PROOF_REJECTED",
                       stage="check", axioms=ck.get("axioms"), problems=ck.get("problems", ["checker did not run"]))
            if p.returncode != 0 and ck.get("status") == "LEAN_PROOF_KERNEL_VERIFIED":
                res.update(status="PROOF_REJECTED", problems=["checker process failed"])
        atomic_write_json(d / "result.json", res)
        print(res["status"], task_id, "; ".join(res.get("problems") or []))
        if res["status"] != "LEAN_PROOF_KERNEL_VERIFIED":
            raise Rejected("PROOF_REJECTED", "; ".join(res.get("problems") or []))
        return res


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
            s.add_argument("--mode", choices=["proof", "statement"], default="proof")
    s = sub.add_parser("translate")
    s.add_argument("--input", required=True)
    s.add_argument("--out", required=True)
    s = sub.add_parser("verify")
    s.add_argument("--run", required=True)
    s = sub.add_parser("status")
    s.add_argument("--run", required=True)
    s = sub.add_parser("validate")
    s.add_argument("--run", required=True)
    s = sub.add_parser("tasks")
    s.add_argument("--run", required=True)
    s.add_argument("--out")
    s = sub.add_parser("check-proof")
    s.add_argument("--run", required=True)
    s.add_argument("--task", required=True)
    s.add_argument("--file", required=True)
    s.add_argument("--allow-axioms")
    a = ap.parse_args(argv)
    try:
        if a.cmd == "doctor":
            doctor()
        elif a.cmd == "inspect":
            inspect(a.manifest, a.roots.split(","))
        elif a.cmd == "export":
            print(export(a.manifest, a.roots.split(","), a.out, mode=a.mode))
        elif a.cmd == "translate":
            translate(a.input, a.out)
        elif a.cmd == "verify":
            verify(a.run)
        elif a.cmd == "status":
            status(a.run)
        elif a.cmd == "validate":
            validate(a.run)
        elif a.cmd == "tasks":
            tasks(a.run, a.out)
        elif a.cmd == "check-proof":
            check_proof(a.run, a.task, a.file, a.allow_axioms)
    except Rejected as e:
        print(f"{e.status}: {e.msg}", file=sys.stderr)
        return 2
    except Exception as e:  # tool failure, distinguished from a rejection
        print(f"TOOL_FAILURE: {type(e).__name__}: {e}", file=sys.stderr)
        return 3
    return 0


if __name__ == "__main__":
    sys.exit(main())

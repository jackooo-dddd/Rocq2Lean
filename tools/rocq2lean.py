#!/usr/bin/env python3
"""rocq2lean pilot driver.

    rocq2lean doctor
    rocq2lean inspect   --manifest SOURCE_MANIFEST --roots ROOTS
    rocq2lean export    --manifest SOURCE_MANIFEST --roots ROOTS --out RUN_DIR
    rocq2lean translate --input SOURCE_IR --out RUN_DIR
    rocq2lean verify    --run RUN_DIR

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


def export(manifest, roots, out, log_name="export.log"):
    doctor(write_report=False, quiet=True)
    m, mpath, lp, files = load_manifest(manifest)
    out = Path(out).resolve()
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
    if ir.exists():
        ir.unlink()
    lines = ["From Rocq2LeanExport Require Import Loader."]
    lines += [f"Require {r}." for r in m.get("requires", [])]
    lines.append(f'Rocq2Lean Export "{ir}" {" ".join(roots)}.')
    export_v.write_text("\n".join(lines) + "\n")
    p = run(["rocq", "compile", "-I", str(EXPORTER / "src"), "-Q", str(EXPORTER / "theories"), "Rocq2LeanExport",
             *lp, str(export_v)], log, env=oenv, check=False)
    if p.returncode != 0 or not ir.exists():
        raise Rejected("EXPORT_VALIDATION_FAILED", f"export process failed; see {log}")
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
    snapshot = {
        "schema": "rocq2lean-source-snapshot/1",
        "manifest": str(mpath), "manifest_sha256": sha256_file(mpath),
        "roots": roots,
        "ir": str(ir), "ir_sha256": sha256_file(ir),
        "frontend": first["frontend"], "rocq_version": first["rocq_version"],
        "exporter_plugin_sha256": sha256_file(plugin),
        "sources": [{"file": str(f), "sha256": sha256_file(f)} for f in files],
        "libraries": libs,
        "toolchains_lock_sha256": lock_sha(),
    }
    rt = run([sys.executable, "-I", str(ROOT / "tools" / "roundtrip.py"), str(ir), str(out), *lp, "--",
              *m.get("requires", [])], log, env=oenv, check=False)
    snapshot["roundtrip"] = json.loads((out / "roundtrip.json").read_text())["status"] \
        if (out / "roundtrip.json").exists() else "NOT_RUN"
    (out / "source_snapshot.json").write_text(json.dumps(snapshot, indent=2) + "\n")
    if rt.returncode != 0:
        raise Rejected("EXPORT_VALIDATION_FAILED", f"independent round trip failed; see {out / 'roundtrip.json'}")
    return ir


def inspect(manifest, roots):
    import tempfile
    with tempfile.TemporaryDirectory(prefix="rocq2lean-inspect-") as td:
        ir = export(manifest, roots, td)
        sys.path.insert(0, str(ROOT / "tools"))
        import preflight
        report = preflight.preflight(ir)
    print(json.dumps(report, indent=2))
    return report


# ---------------------------------------------------------------- translate

def translate(inp, out):
    doctor(write_report=False, quiet=True)
    inp, out = Path(inp).resolve(), Path(out).resolve()
    lean_dir = out / "lean"
    lean_dir.mkdir(parents=True, exist_ok=True)
    (out / "logs").mkdir(parents=True, exist_ok=True)
    log = out / "logs" / "translate.log"
    if log.exists():
        log.unlink()
    report = out / "translation_report.json"
    for stale in [report, lean_dir / "Rocq2LeanOut.olean", lean_dir / "Rocq2LeanOut.ilean"]:
        if stale.exists():
            stale.unlink()
    run(["lake", "-d", str(ROOT), "build", "Rocq2Lean"], log, env=lean_env())
    mod = lean_dir / "Rocq2LeanOut.lean"
    mod.write_text(f'import Rocq2Lean\n#rocq2lean_import "{inp}" "{report}"\n')
    p = run(["lake", "-d", str(ROOT), "env", "lean", str(mod), "-o", str(lean_dir / "Rocq2LeanOut.olean"),
             "-i", str(lean_dir / "Rocq2LeanOut.ilean")], log, cwd=lean_dir, env=lean_env(), check=False)
    if not report.exists():
        raise Rejected("TRANSLATION_FAILED", f"no report written; see {log}")
    rep = json.loads(report.read_text())
    rep_roots = {r["name"]: r["status"] for r in rep["roots"]}
    for name, st in rep_roots.items():
        print(f"{st:24} {name}")
    if p.returncode != 0:
        bad = sorted({st for st in rep_roots.values() if st != "TRANSLATED_AND_CHECKED"})
        raise Rejected(bad[0] if bad else "TRANSLATION_FAILED", f"translation rejected; see {log}")
    return rep


# ---------------------------------------------------------------- verify

def verify(run_dir):
    doctor(write_report=False, quiet=True)
    run_dir = Path(run_dir).resolve()
    log = run_dir / "logs" / "verify.log"
    if log.exists():
        log.unlink()
    checks = {}
    snap_p = run_dir / "source_snapshot.json"
    if not snap_p.exists():
        raise Rejected("AUDIT_REJECTED", "no source snapshot in run directory")
    snap = json.loads(snap_p.read_text())
    problems = []
    if snap["toolchains_lock_sha256"] != lock_sha():
        problems.append("toolchain lock changed since export")
    if sha256_file(snap["ir"]) != snap["ir_sha256"]:
        problems.append("source IR changed since export")
    for lib in snap["libraries"]:
        if lib["vo"] and sha256_file(lib["vo"]) != lib["sha256"]:
            problems.append(f"library {lib['dirpath']} changed since export")
    for s in snap["sources"]:
        if sha256_file(s["file"]) != s["sha256"]:
            problems.append(f"source file {s['file']} changed since export")
    checks["snapshot"] = problems or "OK"
    if problems:
        raise Rejected("AUDIT_REJECTED", "; ".join(problems))

    report_p = run_dir / "translation_report.json"
    if not report_p.exists():
        raise Rejected("AUDIT_REJECTED", "no translation report in run directory")
    rep = json.loads(report_p.read_text())
    if Path(rep["source"]).resolve() != Path(snap["ir"]).resolve():
        raise Rejected("AUDIT_REJECTED", "translation report was produced from a different IR file")
    requested = set(snap["roots"])
    reported = {r["requested"] for r in json.loads(Path(snap["ir"]).open().readlines()[1])["roots"]}
    if requested != reported:
        raise Rejected("AUDIT_REJECTED", f"requested roots {requested} differ from exported roots {reported}")

    # Fresh-process consumer of the generated module.
    lean_dir = run_dir / "lean"
    cons = lean_dir / "Rocq2LeanConsumer.lean"
    cons.write_text(f'import Rocq2LeanOut\nimport Rocq2Lean.Verify\n#rocq2lean_verify "{report_p}"\n')
    lp = run(["lake", "-d", str(ROOT), "env", "printenv", "LEAN_PATH"], log, env=lean_env()).stdout.strip()
    env = dict(lean_env(), LEAN_PATH=f"{lp}:{lean_dir}")
    p = run([f"{HOME}/.elan/bin/lean", str(cons)], log, cwd=lean_dir, env=env, check=False)
    checks["consumer"] = "OK" if p.returncode == 0 else (p.stdout + p.stderr).strip()
    if p.returncode != 0:
        raise Rejected("AUDIT_REJECTED", f"consumer check failed; see {log}")

    # Independent structural audit.
    p = run([sys.executable, "-I", str(ROOT / "tools" / "audit.py"), snap["ir"], str(report_p),
             str(run_dir / "audit.json")], log, check=False)
    checks["structural_audit"] = "OK" if p.returncode == 0 else p.stdout.strip()
    if p.returncode != 0:
        raise Rejected("AUDIT_REJECTED", f"structural audit failed; see {run_dir / 'audit.json'}")

    result = {"schema": "rocq2lean-verify/1", "status": "VERIFIED", "checks": checks,
              "roots": rep["roots"], "summary": rep["summary"], "toolchains_lock_sha256": lock_sha()}
    (run_dir / "verify.json").write_text(json.dumps(result, indent=2) + "\n")
    print("VERIFIED", run_dir)
    return result


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
    except Rejected as e:
        print(f"{e.status}: {e.msg}", file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    sys.exit(main())

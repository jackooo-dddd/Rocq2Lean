"""Shared helpers for the stage test scripts (they drive the real CLI)."""
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
# The Rocq opam switch is the one of the toolchain lock (single source of truth).
SWITCH = json.loads((ROOT / "toolchains.lock.json").read_text())["rocq"]["opam_switch"]
CLI = [sys.executable, "-I", str(ROOT / "tools" / "rocq2lean.py")]
FAILS = []


def cli(*args):
    p = subprocess.run(CLI + list(map(str, args)), capture_output=True, text=True)
    return p.returncode, p.stdout + p.stderr


def check(cond, msg):
    print(("PASS " if cond else "FAIL ") + msg)
    if not cond:
        FAILS.append(msg)


def decls(ir):
    return {d["name"]: d for d in map(json.loads, open(ir)) if d["kind"] in ("constant", "inductive")}


def results(run):
    rep = json.load(open(Path(run) / "translation_report.json"))
    return {r["source"]: r for r in rep["results"]}, rep


def finish(stage):
    print(f"{stage}: {'OK' if not FAILS else f'{len(FAILS)} FAILURE(S)'}")
    sys.exit(1 if FAILS else 0)


def audit_report(run, rep, name):
    """Run the standalone auditor (source + contract + given report). Returns (exit, problems)."""
    run = Path(run)
    p2 = run / f"report_{name}.json"
    p2.write_text(json.dumps(rep))
    meta = [str(run / "consumer_result.json")] if (run / "consumer_result.json").exists() else []
    p = subprocess.run([sys.executable, "-I", str(ROOT / "tools" / "audit.py"), str(run / "source.ndjson"),
                        str(run / "contract.json"), str(p2), str(run / f"audit_{name}.json"), *meta],
                       capture_output=True, text=True)
    if p.returncode not in (0, 1):
        raise RuntimeError(f"auditor did not run ({p.returncode}): {p.stderr[-400:]}")
    out = json.loads((run / f"audit_{name}.json").read_text())
    return p.returncode, out["problems"]


def structurally_rejected(run, rep, name, decl):
    """True iff the auditor rejects the report through its structural detector on `decl`."""
    rc, probs = audit_report(run, rep, name)
    return rc == 1 and any(x["detector"] == "structure" and x["message"].startswith(decl + ":") for x in probs)


def forge_run(base, name, rep, prelude="", check_cmd="verify"):
    """A copy of run `base` whose report is `rep` and whose generated module is rebuilt from that
    report by kernel replay (`#rocq2lean_replay`, every declaration through addChecked), with the
    translation manifest re-synchronized: it simulates a translator that produced exactly `rep`.
    Returns (run dir, all replayed declarations kernel-accepted, verify exit, consumer result, audit)."""
    import hashlib
    import os
    import shutil
    base = Path(base)
    d = base.parent / f"{base.name}-forged-{name}"
    shutil.rmtree(d, ignore_errors=True)
    shutil.copytree(base, d, ignore=shutil.ignore_patterns(".rocq2lean.lock", "verify.json", "validate.json", "audit.json",
                                                           "consumer_result.json", "*-forged-*", "mut-*"))
    (d / "translation_report.json").write_text(json.dumps(rep))
    lean = d / "lean"
    for f in lean.glob("Rocq2LeanOut.*"):
        f.unlink()
    (lean / "Rocq2LeanOut.lean").write_text(
        f'import Rocq2Lean\n{prelude}\n#rocq2lean_replay "{d / "translation_report.json"}" "{lean / "replay.json"}"\n')
    env = dict(os.environ, PATH=f"{Path.home()}/.elan/bin:" + os.environ["PATH"])
    subprocess.run(["lake", "-d", str(ROOT), "env", "lean", "Rocq2LeanOut.lean", "-o", "Rocq2LeanOut.olean",
                    "-i", "Rocq2LeanOut.ilean"], cwd=lean, capture_output=True, text=True, env=env)
    replayed = json.loads((lean / "replay.json").read_text())["results"] if (lean / "replay.json").exists() else []
    sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
    tm = json.loads((d / "translation_manifest.json").read_text())
    tm.update(report_sha256=sha(d / "translation_report.json"), module_lean_sha256=sha(lean / "Rocq2LeanOut.lean"),
              module_olean_sha256=sha(lean / "Rocq2LeanOut.olean"), module_ilean_sha256=sha(lean / "Rocq2LeanOut.ilean"))
    (d / "translation_manifest.json").write_text(json.dumps(tm))
    rc, _ = cli(check_cmd, "--run", d)
    load = lambda f: json.loads((d / f).read_text()) if (d / f).exists() else {}
    return d, bool(replayed) and all(x["kernel"] == "ACCEPTED" for x in replayed), rc, load("consumer_result.json"), load("audit.json")

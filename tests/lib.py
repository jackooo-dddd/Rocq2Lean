"""Shared helpers for the stage test scripts (they drive the real CLI)."""
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
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

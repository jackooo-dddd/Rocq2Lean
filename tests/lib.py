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

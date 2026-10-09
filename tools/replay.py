#!/usr/bin/env python3
"""Replay a (possibly mutated) translation report into a fresh Lean module; print kernel outcomes.

    replay.py REPORT.json OUT_DIR  ->  OUT_DIR/replay.json, exit 0 iff every declaration is accepted
"""
import json
import os
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


def replay(report, out):
    out = Path(out)
    out.mkdir(parents=True, exist_ok=True)
    mod = out / "Replay.lean"
    res = out / "replay.json"
    if res.exists():
        res.unlink()
    mod.write_text(f'import Rocq2Lean\n#rocq2lean_replay "{Path(report).resolve()}" "{res.resolve()}"\n')
    env = dict(os.environ, PATH=f"{Path.home()}/.elan/bin:" + os.environ["PATH"])
    p = subprocess.run(["lake", "-d", str(ROOT), "env", "lean", str(mod)], capture_output=True, text=True, env=env)
    if not res.exists():
        raise RuntimeError(f"replay did not run (exit {p.returncode}): {p.stderr[-500:]}{p.stdout[-500:]}")
    return json.loads(res.read_text())["results"]


if __name__ == "__main__":
    rs = replay(sys.argv[1], sys.argv[2])
    for r in rs:
        print(r["kernel"], r["source"], r.get("message", "")[:120])
    sys.exit(0 if all(r["kernel"] == "ACCEPTED" for r in rs) else 1)

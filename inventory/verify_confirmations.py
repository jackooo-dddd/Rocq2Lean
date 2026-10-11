"""Continue every successful probe confirmation (runs/inv-confirm-*: export with round trip and
translate succeeded for the requested root) through `rocq2lean verify` and `rocq2lean status`, in
fresh processes. Failed confirmations keep their original request and result; nothing is re-run
on a subset under the same run. Results: runs/inv-probe-<fam>/verifications.jsonl.

    python3 -I inventory/verify_confirmations.py modern|classic
"""
import json
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
import os
TAG = os.environ.get("INVENTORY_PROBE_TAG", "")
CLI = [sys.executable, "-I", str(ROOT / "tools" / "rocq2lean.py")]


def one(c):
    d = ROOT / "runs" / c["run"]
    r = {"declaration": c["declaration"], "run": c["run"]}
    for step in ("verify", "status"):
        p = subprocess.run(CLI + [step, "--run", str(d)], capture_output=True, text=True)
        r[step] = p.returncode
        if step == "status":
            r["status_out"] = (p.stdout + p.stderr).strip()[-300:]
    v = d / "verify.json"
    r["verify_status"] = json.loads(v.read_text()).get("status") if v.exists() else None
    return r


def main(fam):
    out = ROOT / "runs" / f"inv-probe{TAG}-{fam}" / "verifications.jsonl"
    done = {json.loads(l)["run"] for l in open(out)} if out.exists() else set()
    rows = [json.loads(l) for l in open(ROOT / "runs" / f"inv-probe{TAG}-{fam}" / "confirmations.jsonl")]
    todo = [c for c in rows if c.get("translate") == 0 and c.get("status") == "TRANSLATED_AND_CHECKED" and c["run"] not in done]
    # sequential: three concurrent verifies in one tree once ended with a tool failure (exit 3)
    with ThreadPoolExecutor(1) as ex:
        for r in ex.map(one, todo):
            print(json.dumps(r)[:300], flush=True)
            with open(out, "a") as fh:
                fh.write(json.dumps(r) + "\n")


if __name__ == "__main__":
    main(sys.argv[1])

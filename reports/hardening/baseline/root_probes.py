"""Root-contract counterexamples from the review, as reproducible probes.

    root_probes.py RUN_DIR OUT_JSON [--contract]

Builds report variants from a genuine successful run and runs the standalone auditor on each.
Expected (after hardening): only the unmodified pair is accepted.
"""
import copy
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]


def variants(rep, root):
    out = {"correct": copy.deepcopy(rep)}
    v = copy.deepcopy(rep); v["roots"] = []; out["roots_empty"] = v
    v = copy.deepcopy(rep); v["roots"] = []
    r0 = next(r for r in v["results"] if r["source"] == root)
    r0.update(status="UNSUPPORTED_FEATURE", target=None, target_kind="", target_type=None, target_value=None)
    v["results"] = [r0]; out["no_roots_only_unsupported"] = v
    v = copy.deepcopy(rep)
    r0 = next(r for r in v["results"] if r["source"] == root)
    r0.update(status="UNSUPPORTED_FEATURE", target=None, target_kind="", target_type=None, target_value=None)
    out["root_success_result_unsupported"] = v
    v = copy.deepcopy(rep)
    v["roots"] = [dict(x, status="UNSUPPORTED_FEATURE") for x in v["roots"]]
    r0 = next(r for r in v["results"] if r["source"] == root)
    r0.update(status="UNSUPPORTED_FEATURE")
    out["root_and_result_fail"] = v
    return out


def main(run, out_path, extra=()):
    run = Path(run)
    rep = json.loads((run / "translation_report.json").read_text())
    root = rep["roots"][0]["name"]
    obs = {}
    for name, v in variants(rep, root).items():
        p = run / f"probe_{name}.json"
        p.write_text(json.dumps(v))
        r = subprocess.run([sys.executable, "-I", str(ROOT / "tools" / "audit.py"), str(run / "source.ndjson"),
                            str(p), str(run / f"probe_{name}_audit.json"), *extra], capture_output=True, text=True)
        obs[name] = {"exit": r.returncode, "verdict": "ACCEPT" if r.returncode == 0 else "REJECT",
                     "stdout": r.stdout.strip()[-300:]}
    Path(out_path).write_text(json.dumps(obs, indent=2))
    for k, v in obs.items():
        print(f"{k:34} {v['verdict']} (exit {v['exit']})")


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2], sys.argv[3:])

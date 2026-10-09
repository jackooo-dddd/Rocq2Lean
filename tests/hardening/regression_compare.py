"""Exact before/after comparison of historical M1–M3 coverage.

    regression_compare.py BASELINE_REPO HARDENED_REPO OUT.json

For each historical stage run, compares the root statuses and the set of accepted declarations
(TRANSLATED_AND_CHECKED) between the baseline revision (7adb40b) and the hardened revision.
Exit 0 iff no previously accepted root or declaration is lost.
"""
import json
import sys
from pathlib import Path

STAGES = ["smoke-idnat", "m1", "m2", "m3a", "m3b", "m3c", "m3d", "holdout", "m3-compute"]


def load(repo, stage):
    p = Path(repo) / "runs" / stage / "translation_report.json"
    if not p.exists():
        return None
    r = json.loads(p.read_text())
    return {"roots": {x["name"]: x["status"] for x in r["roots"]},
            "accepted": sorted(x["source"] for x in r["results"] if x["status"] == "TRANSLATED_AND_CHECKED"),
            "bootstrap": sorted(x["source"] for x in r["results"] if x["status"] == "BOOTSTRAP_RESOLVED")}


def main(base, hard, out):
    rows, lost = [], 0
    for st in STAGES:
        b, h = load(base, st), load(hard, st)
        if b is None or h is None:
            rows.append({"stage": st, "baseline": b is not None, "hardened": h is not None, "comparison": "MISSING_RUN"})
            lost += 1
            continue
        lost_roots = sorted(r for r, s in b["roots"].items() if s == "TRANSLATED_AND_CHECKED" and h["roots"].get(r) != s)
        lost_decls = sorted(set(b["accepted"]) - set(h["accepted"]))
        gained = sorted(set(h["accepted"]) - set(b["accepted"]))
        lost += len(lost_roots) + len(lost_decls)
        rows.append({"stage": st, "roots_before": len(b["roots"]), "roots_after": len(h["roots"]),
                     "accepted_before": len(b["accepted"]), "accepted_after": len(h["accepted"]),
                     "same_roots": b["roots"] == h["roots"], "same_accepted": b["accepted"] == h["accepted"],
                     "lost_roots": lost_roots, "lost_declarations": lost_decls, "gained_declarations": gained})
    Path(out).write_text(json.dumps({"schema": "rocq2lean-regression/1", "lost": lost, "stages": rows}, indent=2) + "\n")
    for r in rows:
        print(r["stage"], r.get("accepted_before"), "->", r.get("accepted_after"), "lost:", r.get("lost_roots", []) + r.get("lost_declarations", []))
    return 0 if lost == 0 else 1


if __name__ == "__main__":
    sys.exit(main(*sys.argv[1:4]))

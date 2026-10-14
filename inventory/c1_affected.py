"""Individual tracking of the protected declarations affected by the universe-specialization defect
(reports/statement_only/ITERATION_LOG.md, entry 4): the 701 protected statements the baseline
translator itself reported as defaulted, and every protected declaration the source-derived
generality check (C-1 repair audit) finds narrowed in the baseline (statements, and protected
definitions/inductives at a quantification range). For each: baseline, B-only and B+C-1 outcomes,
the B+C-1 root blockers, and its downstream protected dependents with their B+C-1 classes.

    python3 -I inventory/c1_affected.py TRANSITIONS_A_TO_C1 TRANSITIONS_A_TO_B OUT.json
"""
import json
import sys
from collections import Counter
from pathlib import Path


def main(tc, tb, out):
    C = json.loads(Path(tc).read_text())
    B = json.loads(Path(tb).read_text())
    dc, db = C["declarations"], B["declarations"]
    down = C["downstream_of_false_acceptances"]
    rows = {}
    for n, x in sorted(dc.items()):
        if not (x["old_self_reported_default"] or x["old_narrowed"]):
            continue
        rows[n] = {"family": x["family"],
                   "self_reported_default_in_baseline": x["old_self_reported_default"],
                   "narrowed_in_baseline_source_derived": x["old_narrowed"],
                   "baseline": x["old_status"], "baseline_category": x["old"],
                   "B_only": db[n]["new_status"], "B_only_category": db[n]["new"],
                   "B_C1": x["new_status"], "B_C1_category": x["new"], "class": x["class"],
                   "B_C1_root_blockers": x.get("new_root_blockers"), "B_C1_message": x.get("new_message"),
                   "downstream": down.get(n)}
    sel = lambda f: [r for r in rows.values() if f(r)]
    s701 = sel(lambda r: r["self_reported_default_in_baseline"])
    sall = sel(lambda r: r["narrowed_in_baseline_source_derived"])

    def summ(rs):
        return {"count": len(rs), "by_class": dict(Counter(r["class"] for r in rs)),
                "by_family_and_class": {f: dict(Counter(r["class"] for r in rs if r["family"] == f)) for f in ("modern", "classic")},
                "baseline_to_B_C1": dict(Counter(f'{r["baseline_category"]} -> {r["B_C1_category"]}' for r in rs)),
                "top_root_blockers": Counter(b for r in rs for b in (r["B_C1_root_blockers"] or [])[:1]).most_common(10)}
    res = {"schema": "rocq2lean-c1-affected/1",
           "self_reported_701": summ(s701),
           "source_derived_narrowed": summ(sall),
           "declarations": rows}
    Path(out).parent.mkdir(parents=True, exist_ok=True)
    Path(out).write_text(json.dumps(res, indent=1, sort_keys=True) + "\n")
    print(json.dumps({k: res[k] for k in ("self_reported_701", "source_derived_narrowed")}, indent=1))


if __name__ == "__main__":
    main(*sys.argv[1:4])

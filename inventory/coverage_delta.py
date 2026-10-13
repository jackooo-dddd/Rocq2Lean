"""Coverage of the fixed protected interface (4,474 Prosa v0.6 + Classic declarations,
reports/prosa_inventory/protected_interface.json) under one fixed set of criteria, and the delta
between two measurements (reports/statement_only/ITERATION_LOG.md).

Categories (per protected declaration, from a corpus run's translation report and its independent
audit; the consumer must be OK for the run to count at all):
* Accepted         — TRANSLATED_AND_CHECKED / STATEMENT_KERNEL_CHECKED / BOOTSTRAP_RESOLVED, audit MATCH;
* Audited Pending  — PENDING_KERNEL_CHECKED / STATEMENT_PENDING_KERNEL_CHECKED, audit MATCH;
* Blocked Dependency — BLOCKED_DEPENDENCY or OBLIGATIONS_PENDING (a dependency is not translated);
* Direct Failure   — anything else (a failure of the declaration itself, or a claimed row the audit
  does not MATCH).

    python3 -I inventory/coverage_delta.py snapshot RUN_DIR OUT.json [--label L]
    python3 -I inventory/coverage_delta.py compare BEFORE.json AFTER.json
"""
import json
import sys
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
ACC = ("TRANSLATED_AND_CHECKED", "STATEMENT_KERNEL_CHECKED", "BOOTSTRAP_RESOLVED")
PEND = ("PENDING_KERNEL_CHECKED", "STATEMENT_PENDING_KERNEL_CHECKED")
CATS = ("Accepted", "Audited Pending", "Blocked Dependency", "Direct Failure")


def category(status, verdict):
    if status in ACC and verdict == "MATCH":
        return "Accepted"
    if status in PEND and verdict == "MATCH":
        return "Audited Pending"
    if status in ("BLOCKED_DEPENDENCY", "OBLIGATIONS_PENDING"):
        return "Blocked Dependency"
    return "Direct Failure"


def snapshot(run, out, label=None):
    run = Path(run)
    rep = json.loads((run / "translation_report.json").read_text())
    audit = json.loads((run / "audit.json").read_text())
    cons = json.loads((run / "consumer_result.json").read_text())
    verdict = {v["source"]: v.get("verdict") for v in audit.get("verdicts", [])}
    rows = {r["source"]: r for r in rep["results"]}
    prot = json.loads((ROOT / "reports/prosa_inventory/protected_interface.json").read_text())["protected"]
    fam = lambda n: "classic" if n.startswith("prosa.classic.") else "modern"
    per = {}
    for n in prot:
        r = rows.get(n)
        st = r["status"] if r else "ABSENT_FROM_EXPORT"
        per[n] = {"family": fam(n), "status": st, "category": category(st, verdict.get(n)),
                  "blocked_by": (r or {}).get("blocked_by") or []}
    counts = {f: dict(Counter(x["category"] for x in per.values() if x["family"] == f)) for f in ("modern", "classic")}
    counts["total"] = dict(Counter(x["category"] for x in per.values()))
    snap = {"schema": "rocq2lean-coverage/1", "label": label, "run": str(run.relative_to(ROOT) if run.is_relative_to(ROOT) else run),
            "consumer": cons.get("status"), "audit": audit.get("status"), "audit_problems": len(audit.get("problems", [])),
            "protected": len(prot), "counts": counts,
            "all_rows": dict(Counter(r["status"] for r in rep["results"])), "declarations": per}
    Path(out).parent.mkdir(parents=True, exist_ok=True)
    Path(out).write_text(json.dumps(snap, indent=1, sort_keys=True) + "\n")
    return snap


def compare(a, b):
    A, B = json.loads(Path(a).read_text()), json.loads(Path(b).read_text())
    da, db = A["declarations"], B["declarations"]
    moves = Counter((da[n]["category"], db[n]["category"]) for n in da if n in db and da[n]["category"] != db[n]["category"])
    regress = sorted(n for n in da if n in db and da[n]["category"] == "Accepted" and db[n]["category"] != "Accepted")
    newly = sorted(n for n in da if n in db and da[n]["category"] != "Accepted" and db[n]["category"] == "Accepted")
    unblocked = sorted(n for n in da if n in db and da[n]["category"] in ("Blocked Dependency", "Direct Failure")
                       and db[n]["category"] in ("Accepted", "Audited Pending"))
    status_changes = sum(1 for n in da if n in db and da[n]["status"] != db[n]["status"])
    res = {"before": A["counts"]["total"], "after": B["counts"]["total"],
           "delta": {c: B["counts"]["total"].get(c, 0) - A["counts"]["total"].get(c, 0) for c in CATS},
           "moves": {f"{x} -> {y}": n for (x, y), n in sorted(moves.items())},
           "status_changes": status_changes, "newly_accepted": newly, "newly_unblocked": unblocked,
           "regressions_previously_accepted": regress,
           "same_protected_set": sorted(da) == sorted(db)}
    return res


if __name__ == "__main__":
    if sys.argv[1] == "snapshot":
        lab = sys.argv[sys.argv.index("--label") + 1] if "--label" in sys.argv else None
        s = snapshot(sys.argv[2], sys.argv[3], lab)
        print(json.dumps(s["counts"], indent=1))
    elif sys.argv[1] == "compare":
        print(json.dumps(compare(sys.argv[2], sys.argv[3]), indent=1))

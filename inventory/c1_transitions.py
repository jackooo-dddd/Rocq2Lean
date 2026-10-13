"""Per-declaration transitions of the protected interface (4,474 declarations) across corpus runs,
for the C-1 correctness repair (reports/statement_only/ITERATION_LOG.md, entry 4).

Inputs: coverage snapshots (`inventory/coverage_delta.py snapshot`) of the runs, and for each run
whose own audit predates the C-1 generality check, a *re-audit* of its report with the current
`tools/audit.py` (source-derived: it does not read the translator's defaulting flags). From the
re-audit, a claimed row of the old run is a **false acceptance** when the generality check rejects
it (a narrowed statement, or a protected definition/inductive with a narrowed quantification range).

Classification of each protected declaration, old run → new run:
* newly supported      — not claimed before (Blocked Dependency / Direct Failure), claimed now
                         (Accepted / Audited Pending);
* false acceptance corrected — claimed and narrowed before; claimed now and not narrowed (generic);
* false acceptance rejected  — claimed and narrowed before; not claimed now (refused or blocked);
* collateral loss      — claimed and faithful before, not claimed now, and its blocking chain
                         reaches a false acceptance that is now refused (a consequence of the repair);
* false acceptance persisting — claimed and narrowed before and now (the new run's own audit
                         rejects it; must be 0 for a validated run);
* genuine regression   — claimed and faithful before, not claimed now (or Accepted → Pending) for
                         any other reason;
* unchanged / moved within claimed (Accepted ↔ Audited Pending) are counted separately.

    python3 -I inventory/c1_transitions.py OLD_SNAPSHOT OLD_REAUDIT NEW_SNAPSHOT NEW_RUN OUT.json
        [--old-run OLD_RUN] [--new-audit NEW_REAUDIT]

(NEW_RUN: its translation report gives blocking chains and pending hypotheses.)
"""
import json
import sys
from collections import Counter, defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CLAIMED = ("Accepted", "Audited Pending")
GEN_MARKS = ("free in the statement", "narrowed quantification range")


def narrowed_rows(audit):
    out = {}
    for p in audit.get("problems", []):
        m = p["message"]
        if any(k in m for k in GEN_MARKS):
            out.setdefault(m.split(": ")[0], m[:400])
    return out


def flagged_rows(report):
    """Rows the old translator itself reported as statements with defaulted levels."""
    return {r["source"] for r in report["results"]
            if r["status"] in ("STATEMENT_KERNEL_CHECKED", "STATEMENT_PENDING_KERNEL_CHECKED") and
            (r.get("universe_level_defaults") or r.get("universe_residuals"))}


def main(old_snap, old_reaudit, new_snap, new_run, out, old_run=None, new_audit=None):
    A = json.loads(Path(old_snap).read_text())
    B = json.loads(Path(new_snap).read_text())
    narrowed = narrowed_rows(json.loads(Path(old_reaudit).read_text()))
    flagged = set()
    if old_run:
        flagged = flagged_rows(json.loads((Path(old_run) / "translation_report.json").read_text()))
    rep = json.loads((Path(new_run) / "translation_report.json").read_text())
    narrowed_now = narrowed_rows(json.loads(Path(new_audit or Path(new_run) / "audit.json").read_text()))
    rows = {r["source"]: r for r in rep["results"]}
    da, db = A["declarations"], B["declarations"]
    prot = sorted(da)
    # blocking chains in the new run: root failures (rows that failed themselves)
    memo = {}

    def roots(n, stack=()):
        if n in memo:
            return memo[n]
        r = rows.get(n)
        if r is None or n in stack:
            return {n}
        if r["status"] not in ("BLOCKED_DEPENDENCY", "OBLIGATIONS_PENDING"):
            return {n}
        acc = set()
        for b in r.get("blocked_by") or []:
            acc |= roots(b, stack + (n,))
        memo[n] = acc or {n}
        return memo[n]

    # reverse dependencies over the source IR (downstream of each declaration)
    deps = {}
    with open(Path(new_run) / "source.ndjson") as fh:
        for line in fh:
            if line.startswith('{"kind":"constant"') or line.startswith('{"kind":"inductive"'):
                d = json.loads(line)
                dd = d.get("deps") or {}
                deps[d["name"]] = set(dd.get("type", [])) | set(dd.get("body", []))
    rdeps = defaultdict(set)
    for n, ds in deps.items():
        for m in ds:
            rdeps[m].add(n)

    def downstream(n):
        seen, st = set(), [n]
        while st:
            x = st.pop()
            for y in rdeps.get(x, ()):
                if y not in seen:
                    seen.add(y)
                    st.append(y)
        return seen

    rejected_false = set()
    per = {}
    for n in prot:
        a, b = da[n], db[n]
        was_claimed, now_claimed = a["category"] in CLAIMED, b["category"] in CLAIMED
        nar = n in narrowed
        if not was_claimed and now_claimed:
            cls = "newly_supported"
        elif was_claimed and nar:
            cls = ("false_acceptance_rejected" if not now_claimed else
                   "false_acceptance_persisting" if n in narrowed_now else "false_acceptance_corrected")
            if not now_claimed:
                rejected_false.add(n)
        elif was_claimed and not now_claimed:
            cls = "loss"                    # split below (collateral / genuine)
        elif a["category"] == "Accepted" and b["category"] == "Audited Pending":
            cls = "accepted_to_pending"
        elif a["category"] == "Audited Pending" and b["category"] == "Accepted":
            cls = "pending_to_accepted"
        elif a["category"] == b["category"]:
            cls = "unchanged"
        else:
            cls = "moved_unclaimed"         # Blocked ↔ Direct Failure
        per[n] = {"family": a["family"], "old": a["category"], "old_status": a["status"], "new": b["category"],
                  "new_status": b["status"], "old_narrowed": narrowed.get(n), "old_self_reported_default": n in flagged,
                  "class": cls}
    # every false acceptance of the old run that is not claimed now (protected or not) explains losses
    all_false_now_unclaimed = {n for n in narrowed if rows.get(n, {}).get("status") not in
                               ("TRANSLATED_AND_CHECKED", "PENDING_KERNEL_CHECKED", "STATEMENT_KERNEL_CHECKED",
                                "STATEMENT_PENDING_KERNEL_CHECKED", "BOOTSTRAP_RESOLVED")}
    for n, x in per.items():
        if x["class"] in ("loss", "false_acceptance_rejected", "moved_unclaimed") or x["new"] not in CLAIMED:
            rs = sorted(roots(n))
            x["new_root_blockers"] = rs[:10]
            x["new_message"] = (rows.get(n, {}).get("message") or "")[:300]
        if x["class"] == "loss":
            rs = roots(n)
            x["class"] = "collateral_loss" if (rs & all_false_now_unclaimed or n in all_false_now_unclaimed) else "genuine_regression"
        if x["class"] == "accepted_to_pending":
            x["new_pending_hypotheses"] = (rows.get(n, {}).get("pending_hypotheses") or [])[:20]
    # downstream of the false acceptances (protected dependents and how they moved)
    down = {}
    for n in sorted(set(narrowed) & set(prot)):
        ds = downstream(n) & set(prot)
        down[n] = {"protected_dependents": len(ds),
                   "dependents_by_class": dict(Counter(per[d]["class"] for d in ds))}
    totals = {}
    for snap, key in ((A, "old"), (B, "new")):
        totals[key] = snap["counts"]
    cls = Counter(x["class"] for x in per.values())
    by_fam = {f: dict(Counter(x["class"] for x in per.values() if x["family"] == f)) for f in ("modern", "classic")}
    pend_new = [r for r in rep["results"] if r["status"] in ("PENDING_KERNEL_CHECKED", "STATEMENT_PENDING_KERNEL_CHECKED")]
    tasks = Counter()
    for r in rep["results"]:
        if r["status"] in ("STATEMENT_KERNEL_CHECKED", "STATEMENT_PENDING_KERNEL_CHECKED"):
            tasks[r.get("synthetic_kind") or "statement"] += 1
    res = {"schema": "rocq2lean-c1-transitions/1", "old": A.get("label") or A["run"], "new": B.get("label") or B["run"],
           "protected": len(prot), "same_protected_set": sorted(da) == sorted(db),
           "new_run_narrowed_rows": len(narrowed_now),
           "totals": totals, "classes": dict(cls), "classes_by_family": by_fam,
           "old_false_acceptances": {"protected_total": len(set(narrowed) & set(prot)),
                                     "protected_statements_self_reported": sum(1 for n in prot if n in flagged),
                                     "protected_self_reported_and_source_derived": sum(1 for n in prot if n in flagged and n in narrowed),
                                     "protected_self_reported_only": sorted(n for n in prot if n in flagged and n not in narrowed)[:50],
                                     "all_rows": len(narrowed)},
           "pending_in_new_run": {"rows": len(pend_new),
                                  "claimed_statement_rows_by_kind": dict(tasks),
                                  "termination_obligations": sum(1 for r in rep["results"] if r.get("synthetic_kind") == "termination"),
                                  "unfolding_equations": sum(1 for r in rep["results"] if r.get("synthetic_kind") == "unfolding_equation")},
           "downstream_of_false_acceptances": down,
           "declarations": per}
    Path(out).parent.mkdir(parents=True, exist_ok=True)
    Path(out).write_text(json.dumps(res, indent=1, sort_keys=True) + "\n")
    print(json.dumps({k: res[k] for k in ("classes", "classes_by_family", "old_false_acceptances", "pending_in_new_run")}, indent=1)[:4000])


if __name__ == "__main__":
    a = sys.argv[1:]
    opt = lambda k: a[a.index(k) + 1] if k in a else None
    pos = [x for i, x in enumerate(a) if not x.startswith("--") and (i == 0 or not a[i - 1].startswith("--"))]
    main(*pos[:5], old_run=opt("--old-run"), new_audit=opt("--new-audit"))

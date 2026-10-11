"""Per-declaration coverage: availability, preflight, existing translation evidence, interface.

Evidence is joined by exact identity only: a run's record of a declaration counts for the inventory
declaration when (1) the run's implementation tree digest equals the current one, (2) the run's
elaborated record of that declaration (its source.ndjson line) is byte-identical to the inventory's,
and (3) the run's own status says what is claimed. A declaration is VERIFIED only when it was
TRANSLATED_AND_CHECKED in a run whose verify.json status is VERIFIED; a translated declaration in a
run without that status stays KERNEL_CHECKED_UNVERIFIED. Nothing is promoted.

Specialization: a translation result whose R2B-P levels occur in the statement (`in_type`) or whose
result sort was lowered (R2B-S) is a specialized dependency instance, not the full interface. Such a
result for a protected (public Prosa/Classic) declaration is flagged as an interface conflict.

    python3 -I inventory/coverage.py
"""
import hashlib
import json
import sys
from collections import Counter, defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
W = ROOT / ".work" / "inventory"
OUT = ROOT / "reports" / "prosa_inventory"
sys.path.insert(0, str(ROOT / "tools"))

# the existing current-implementation evidence (M6 completion, implementation 33ed468)
RUNS = ["m6-gate-finishtime5", "m6p-behavior61", "m6p-finishtime4", "m6p-holdout13_prosa", "m6p-holdout14_mathcomp",
        "m6p-holdout20_prosa", "m6h-verified8", "m6h-translated9", "m6h-holdout_completion_prosa",
        "m6h-holdout_completion_mathcomp"]
# plus the full-CLI confirmation runs of the diagnostic probes (inventory/probe.py confirm)
RUNS += sorted(p.name for p in (ROOT / "runs").glob("inv-confirm*") if p.is_dir() and (p / "source_snapshot.json").exists())
# P0 focused-test requests (fresh CLI runs of the current implementation)
RUNS += sorted(p.name for p in (ROOT / "runs").glob("p0t-*") if p.is_dir() and (p / "source_snapshot.json").exists())
RANK = ["VERIFIED_AS_ROOT", "VERIFIED_AS_DEPENDENCY", "KERNEL_CHECKED_UNVERIFIED", "ATTEMPTED_NOT_TRANSLATED",
        "STALE_EVIDENCE_ONLY", "NOT_ATTEMPTED"]


def run_evidence(run, impl, inv_digest):
    d = ROOT / "runs" / run
    snap = json.loads((d / "source_snapshot.json").read_text())
    ver = json.loads((d / "verify.json").read_text()) if (d / "verify.json").exists() else {"status": "NOT_RUN"}
    rep = json.loads((d / "translation_report.json").read_text()) if (d / "translation_report.json").exists() else None
    ir_digest = {}
    with open(d / "source.ndjson") as fh:
        for line in fh:
            if line.startswith('{"kind":"constant"') or line.startswith('{"kind":"inductive"'):
                i = line.index('"name":"') + 8
                ir_digest[line[i:line.index('"', i)]] = hashlib.sha256(line.encode()).hexdigest()
    roots = {r["name"] for r in (rep or {}).get("roots", [])} or set(snap.get("request", []))
    current_impl = snap.get("impl_tree_sha256") == impl
    out = {}
    for r in (rep or {}).get("results", []):
        n = r.get("source")
        if not n:
            continue
        same_src = ir_digest.get(n) is not None and ir_digest.get(n) == inv_digest.get(n)
        spec_type = [x["level"] for x in r.get("r2bp_levels") or [] if x.get("in_type")]
        spec_body = [x["level"] for x in r.get("r2bp_levels") or [] if not x.get("in_type")]
        lowered = r.get("sort_lowered_levels") or []
        out[n] = {"run": run, "run_verify": ver.get("status"), "status": r.get("status"), "rule": r.get("rule"),
                  "as_root": n in roots, "current_impl": current_impl, "identical_source": same_src,
                  "statement_specialized": bool(spec_type or lowered), "specialized_levels": spec_type + lowered,
                  "body_only_specialization": bool(spec_body)}
    # declarations exported but without a translation result (run stopped before them)
    for n in ir_digest:
        out.setdefault(n, {"run": run, "run_verify": ver.get("status"), "status": "NO_RESULT", "as_root": n in roots,
                           "current_impl": current_impl,
                           "identical_source": ir_digest[n] == inv_digest.get(n)})
    return out, {"run": run, "verify": ver.get("status"), "impl_tree_sha256": snap.get("impl_tree_sha256"),
                 "current_impl": current_impl, "ir_sha256": snap.get("ir_sha256"), "declarations": len(ir_digest),
                 "results": len((rep or {}).get("results", [])),
                 "identical_to_inventory": sum(1 for n in ir_digest if ir_digest[n] == inv_digest.get(n)),
                 "absent_from_inventory": sum(1 for n in ir_digest if n not in inv_digest),
                 "differs_from_inventory": sum(1 for n in ir_digest if n in inv_digest and ir_digest[n] != inv_digest[n])}


def grade(e):
    if not (e["current_impl"] and e["identical_source"]):
        return "STALE_EVIDENCE_ONLY"
    if e["status"] == "TRANSLATED_AND_CHECKED" or e["status"] == "BOOTSTRAP_RESOLVED":
        if e["run_verify"] == "VERIFIED":
            return "VERIFIED_AS_ROOT" if e["as_root"] else "VERIFIED_AS_DEPENDENCY"
        return "KERNEL_CHECKED_UNVERIFIED"
    return "ATTEMPTED_NOT_TRANSLATED"


def main():
    import rocq2lean
    impl = rocq2lean.impl_tree_sha256()
    decls = [json.loads(l) for l in open(OUT / "declarations.jsonl")]
    g = json.loads((W / "graph.json").read_text())
    merged = {f: json.loads((W / f"merge-{f}.json").read_text()) for f in ("modern", "classic")}
    inv_digest = {**merged["classic"]["digests"], **merged["modern"]["digests"]}
    ev = defaultdict(list)
    runs = []
    for r in RUNS:
        if not (ROOT / "runs" / r / "source_snapshot.json").exists():
            runs.append({"run": r, "missing": True})
            continue
        out, meta = run_evidence(r, impl, inv_digest)
        runs.append(meta)
        for n, e in out.items():
            ev[n].append(e)
    rows = []
    for d in decls:
        n = d.get("canonical") or d["id"]          # an alias is covered exactly as its canonical declaration
        pf = g["preflight_declarations"].get(n)
        rr = g["roots"].get(n)
        es = ev.get(n, [])
        grades = sorted({grade(e) for e in es}, key=RANK.index) or ["NOT_ATTEMPTED"]
        spec_runs = sorted({e["run"] for e in es if e.get("statement_specialized") and grade(e) != "STALE_EVIDENCE_ONLY"})
        full_runs = sorted({e["run"] for e in es if grade(e) in RANK[:3] and not e.get("statement_specialized")})
        rows.append({
            "id": d["id"], "canonical": d.get("canonical"), "family": d["family"], "role": d["role"], "protected_interface": d["protected_interface"],
            "availability": d.get("export", "exported" if d.get("elaborated") else "not_exported"),
            "preflight_declaration": pf["status"] if pf else "UNEXAMINED",
            "preflight_root": rr["preflight"] if rr else ("UNEXAMINED" if d["family"] != "external" else None),
            "known_blocker": rr["known"] if rr else ("UNEXAMINED" if d["family"] != "external" else
                                                    "KNOWN_BLOCKER_DIRECT" if n in g["known_blockers"] else None),
            "reachable_blockers": len(rr["reachable_blockers"]) if rr else None,
            "context_dependent_failures_reachable": rr["context_dependent_reachable"] if rr else None,
            "evidence": grades[0], "evidence_all": grades,
            "evidence_runs": sorted({e["run"] for e in es}),
            "verified_full_interface_runs": [r for r in full_runs if any(e["run"] == r and grade(e).startswith("VERIFIED") for e in es)],
            "specialized_instance_runs": spec_runs,
            "interface_conflict": bool(d["protected_interface"] and spec_runs),
        })
    with open(OUT / "coverage.jsonl", "w") as fh:
        for r in rows:
            fh.write(json.dumps(r, sort_keys=True) + "\n")
    (W / "coverage_runs.json").write_text(json.dumps({"impl_tree_sha256": impl, "runs": runs}, indent=1) + "\n")
    for fam in ("modern", "classic", "external"):
        rs = [r for r in rows if r["family"] == fam]
        print(fam, Counter(r["evidence"] for r in rs), "conflicts", sum(r["interface_conflict"] for r in rs))


if __name__ == "__main__":
    main()

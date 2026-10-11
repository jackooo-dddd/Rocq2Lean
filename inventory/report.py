"""Summary, blocker map and reconciliation of the Prosa v0.6 + Classic inventory.

Counting conventions (also stated in FULL_INVENTORY_REPORT.md):
  * Ownership is by source file: a declaration belongs to modern Prosa (P) or Classic (C) when its
    module is compiled from that tree. Classic imports v0.6 `prosa.util` modules; those declarations
    are owned by P and appear in C's closure as shared dependencies. P and C are disjoint, so the
    combined in-scope count is |P| + |C|; nothing is merged by short name.
  * A declaration is an entry of the compiled environment (MetaRocq tmQuoteModule after all Sections
    are closed) whose name is its kernel identity. Entries that are module aliases (`Module M := N.`:
    the name differs from the kernel name the exporter resolves) are alias_reexport entries; they
    point to their canonical declaration and are not counted as declarations. Roles: public_source (a non-local source sentence), source_local_helper (Local /
    #[local]), generated_projection (record/class fields), generated_scheme (_rect/_ind/_rec/_sind),
    generated_hb (Hierarchy-Builder output), generated_instance / generated_obligation, unattributed.
    The protected target interface is public_source plus generated_projection.
  * The closure of a family is every kernel declaration reachable from its entries through
    elaborated types, transparent bodies and opaque proof bodies (exporter dependencies).
  * Unknown values are the string "UNKNOWN", never zero.

    python3 -I inventory/report.py
"""
import csv
import json
import os
import re
from collections import Counter, defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CFG = json.loads((ROOT / "inventory" / "config.json").read_text())
W = ROOT / ".work" / "inventory"
OUT = ROOT / "reports" / "prosa_inventory"
X = lambda p: Path(os.path.expanduser(p)) if p.startswith("~") else ROOT / p
FAMS = ("modern", "classic")
PROTECTED = ("public_source", "generated_projection")


def jl(p):
    return [json.loads(l) for l in open(p)]


def count(xs, key):
    return dict(sorted(Counter(key(x) for x in xs).items(), key=lambda kv: (-kv[1], str(kv[0]))))


def fam_split(rows, pred=lambda r: True):
    out = {f: sum(1 for r in rows if r["family"] == f and pred(r)) for f in FAMS}
    out["combined"] = out["modern"] + out["classic"]
    return out


def rts_reconciliation(decls):
    rts = X(CFG["rts"]["snapshot"]) / "Prosa-Shunqi"
    inv = list(csv.DictReader(open(rts / "Validation/planning/v06_dependency/declaration_inventory.csv")))
    mine = {r["name"].replace("/", "."): r for r in decls if r["family"] == "modern"}
    names = {r["qualified_name"] for r in inv}
    present = [n for n in names if n in mine]
    pub = {n for n, r in mine.items() if r["role"] == "public_source"}
    extra = sorted(pub - names)
    ext_reason = Counter()
    for n in extra:
        r = mine[n]
        kw = (r.get("source") or {}).get("keyword")
        ext_reason[f"keyword {kw}"] += 1
    plan = list(csv.DictReader(open(rts / "classic-prosa/casestudy-translation/file_order.csv")))
    cfiles = {r["file"]: r for r in csv.DictReader(open(OUT / "files.csv")) if r["family"] == "classic"}
    plan_rows = []
    for p in plan:
        f = cfiles.get(p["source"])
        plan_rows.append({"file": p["source"], "rts_decls": int(p["decls"]), "build": f["build"] if f else "MISSING",
                          "public_source": f["public_source"] if f else "UNKNOWN",
                          "enumerated": f["enumerated"] if f else "UNKNOWN"})
    return {
        "modern": {"rts_declarations": len(inv), "rts_kinds": count(inv, lambda r: r["kind"]),
                   "present_in_compiled_environment": len(present),
                   "missing_from_compiled_environment": sorted(names - set(mine)),
                   "rts_names_by_inventory_role": count(present, lambda n: mine[n]["role"]),
                   "inventory_public_not_in_rts": len(extra), "inventory_public_not_in_rts_by_keyword": dict(ext_reason),
                   "inventory_public_not_in_rts_sample": extra[:40]},
        "classic_plan": {"files": len(plan_rows), "rts_declarations": sum(r["rts_decls"] for r in plan_rows),
                         "files_compiled": sum(1 for r in plan_rows if r["build"] == "COMPILED"),
                         "inventory_public_source": sum(int(r["public_source"]) for r in plan_rows if str(r["public_source"]).isdigit()),
                         "rows": plan_rows},
    }


PROBES = {"stack": [
    {"root": "prosa.results.rta.ideal.gel.bounded_pi.total_workload_shorten_range", "default_stack": "Stack overflow"},
    {"root": "prosa.results.rta.ideal.elf.bounded_pi.bound_on_ep_workload", "default_stack": "Stack overflow"}]}


def recommendations(g, groups, fam_of, prot_of, cov_rows):
    """The curated next tasks (inventory/recommendations.json), each checked against the blocker map:
    every task names mechanisms or declarations with a real dependency path from an in-scope root."""
    recs = json.loads((ROOT / "inventory" / "recommendations.json").read_text())
    if isinstance(recs, dict) and recs.get("superseded"):
        return recs                                   # a recorded change of direction, not a task list
    by_mech = {x["mechanism"]: x for x in groups}
    ctx = g.get("context_dependent", {})
    contra = g.get("preflight_contradicted_by_evidence", {})
    out = []
    for r in recs:
        paths, roots = [], {"modern": 0, "classic": 0}
        for m in r.get("mechanisms", []):
            x = by_mech[m]                                   # KeyError: a task without a blocker
            if not x["example_path"] or x["example_path"][0].split(".")[0] != "prosa":
                raise SystemExit(f"recommendation {r['task']}: no in-scope path for {m}")
            paths.append(x["example_path"])
            for f in roots:
                roots[f] += x["sole_blocker_roots"][f]
        conflicts = {x["id"] for x in cov_rows if x["interface_conflict"]}
        for n in r.get("declarations", []):
            if n in g.get("known_blockers", {}) or n in conflicts:
                continue
            if n not in ctx and n not in contra:
                raise SystemExit(f"recommendation {r['task']}: {n} is not a recorded issue")
            reach = (ctx.get(n) or contra.get(n))["roots_reaching"]
            if not sum(reach.values()):
                raise SystemExit(f"recommendation {r['task']}: no in-scope root reaches {n}")
        ms = set(r.get("mechanisms", []))
        unlocked = {"modern": 0, "classic": 0, "protected": 0}
        for rid, rr in g["roots"].items():
            if rr["mechanisms"] and set(rr["mechanisms"]) <= ms:
                unlocked[fam_of[rid]] += 1
                unlocked["protected"] += prot_of[rid]
        out.append(dict(r, example_paths=paths, sole_blocker_roots=roots if ms else None,
                        roots_without_known_blocker_after_task=unlocked if ms else None))
    # cumulative: roots whose known blockers are all covered by tasks 1..k
    acc = set()
    for t in out:
        acc |= set(t.get("mechanisms", []))
        c = {"modern": 0, "classic": 0, "protected": 0}
        for rid, rr in g["roots"].items():
            if rr["mechanisms"] and set(rr["mechanisms"]) <= acc:
                c[fam_of[rid]] += 1
                c["protected"] += prot_of[rid]
        t["roots_without_known_blocker_after_tasks_up_to_here"] = c if t.get("mechanisms") else None
    return out


def main():
    lock = json.loads((OUT / "scope.lock.json").read_text())
    files = list(csv.DictReader(open(OUT / "files.csv")))
    decls = jl(OUT / "declarations.jsonl")
    cov = {r["id"]: r for r in jl(OUT / "coverage.jsonl")}
    g = json.loads((W / "graph.json").read_text())
    extra = json.loads((W / "extra_blockers.json").read_text())
    merged = {f: json.loads((W / f"merge-{f}.json").read_text()) for f in FAMS}
    exp = {f: json.loads((W / f"export-{f}" / "summary.json").read_text()) for f in FAMS}
    covruns = json.loads((W / "coverage_runs.json").read_text())
    owned = [d for d in decls if d["family"] in FAMS and d["role"] != "alias_reexport"]
    aliases = [d for d in decls if d["role"] == "alias_reexport"]
    prot = [d for d in owned if d["protected_interface"]]
    ext = [d for d in decls if d["family"] == "external"]

    fsum = {}
    for f in FAMS:
        fs = [r for r in files if r["family"] == f]
        fsum[f] = {"files": len(fs), "build": count(fs, lambda r: r["build"]),
                   "import_only": sum(r["import_only"] == "True" for r in fs),
                   "unknown_counts": [r["file"] for r in fs if r["enumerated"] == "UNKNOWN"],
                   "unattributed_declarations": sum(int(r["unattributed"]) for r in fs if r["unattributed"].isdigit())}
    fsum["modern"]["refinements"] = {"files": sum(1 for r in files if r["family"] == "modern" and r["file"].startswith("implementation/refinements/")),
                                     "compiled": sum(1 for r in files if r["family"] == "modern" and r["file"].startswith("implementation/refinements/") and r["build"] == "COMPILED")}
    dsum = {}
    for f in FAMS:
        rs = [d for d in owned if d["family"] == f]
        dsum[f] = {"declarations": len(rs), "by_role": count(rs, lambda d: d["role"]), "by_kind": count(rs, lambda d: d["kind"]),
                   "by_nature": count(rs, lambda d: d["nature"]),
                   "public_source": sum(d["role"] == "public_source" for d in rs),
                   "protected_interface": sum(d["protected_interface"] for d in rs),
                   "public_by_nature": count([d for d in rs if d["role"] == "public_source"], lambda d: d["nature"]),
                   "export": count(rs, lambda d: d["export"]),
                   "aliases": sum(bool(d.get("alias")) for d in rs),
                   "relaxed_checking": sum(bool(d.get("relaxed_checking")) for d in rs),
                   "universe_polymorphic": sum(d.get("universes") == "polymorphic" for d in rs),
                   "unknown_in_failed_files": "UNKNOWN" if fsum[f]["unknown_counts"] else 0,
                   "alias_reexport_entries": sum(1 for d in aliases if d["family"] == f),
                   "enumerated_entries": len(rs) + sum(1 for d in aliases if d["family"] == f)}
    reach = Counter(f for d in decls for f in d.get("reached_by", []))
    both = [d for d in decls if len(d.get("reached_by", [])) == 2]
    closure = {"modern": merged["modern"]["declarations"], "classic": merged["classic"]["declarations"],
               "combined_distinct": sum(1 for d in decls if d.get("reached_by") and d["role"] != "alias_reexport"),
               "shared_by_both": len(both),
               "classic_uses_modern_owned": sum(1 for d in decls if d["family"] == "modern" and "classic" in d.get("reached_by", [])),
               "external_by_library": count(ext, lambda d: d.get("library")),
               "external_by_nature": count(ext, lambda d: d["nature"]),
               "cross_family_conflicts": len(g["cross_family_conflicts"]),
               "inconsistent_chunk_copies": {f: len(merged[f]["inconsistent_copies"]) for f in FAMS},
               "graph": {"nodes": g["nodes"], "edges": g["edges"], "sccs": g["sccs"],
                         "nontrivial_sccs": len(g["nontrivial_sccs"]), "missing_edge_targets": len(g["missing_edge_targets"])}}
    short = defaultdict(set)
    for d in owned:
        if d["role"] == "public_source":
            short[d["name"].replace("/", ".").rsplit(".", 1)[-1]].add(d["family"])
    closure["public_short_names_in_both_families_not_merged"] = sum(1 for v in short.values() if len(v) == 2)

    def verdicts(rows, key):
        return {f: count([r for r in rows if r["family"] == f], lambda r: cov[r["id"]][key]) for f in FAMS}
    psum = {"all_owned": {"preflight": verdicts(owned, "preflight_root"), "known": verdicts(owned, "known_blocker")},
            "protected": {"preflight": verdicts(prot, "preflight_root"), "known": verdicts(prot, "known_blocker")},
            "external_declarations": count(ext, lambda r: cov[r["id"]]["preflight_declaration"])}
    esum = {"runs": covruns["runs"], "implementation": covruns["impl_tree_sha256"],
            "owned": verdicts(owned, "evidence"), "protected": verdicts(prot, "evidence"),
            "external": count(ext, lambda r: cov[r["id"]]["evidence"]),
            "interface_conflicts": [r["id"] for r in cov.values() if r["interface_conflict"]],
            "specialized_dependency_instances": sum(1 for r in cov.values() if r["specialized_instance_runs"])}
    gaps = []
    for f in FAMS:
        for x in fsum[f]["unknown_counts"]:
            gaps.append({"family": f, "file": x, "gap": "not compiled under the fixed toolchain; declarations UNKNOWN"})
        for r in exp[f].get("not_reached", []):
            gaps.append({"family": f, "declaration": r, "gap": "enumerated but neither exported nor recorded as failed"})
        for r, v in merged[f]["failed"].items():
            gaps.append({"family": f, "declaration": r, "gap": "export failed", "detail": str(v.get("log_tail", ""))[-300:]})
    unresolved_unq = {f: len(merged[f]["unquotable"]) for f in FAMS}
    verdict = "INVENTORY_COMPLETE" if not gaps else "INVENTORY_PARTIAL"
    summary = {"schema": "rocq2lean-prosa-inventory-summary/1", "verdict": verdict, "gaps": gaps,
               "scope": {"rts": lock.get("rts", {}).get("commit"), "modern": lock.get("modern", {}).get("commit"),
                         "classic": lock.get("classic", {}).get("commit")},
               "files": fsum, "declarations": dsum,
               "combined": {"declarations": len(owned), "public_source": sum(d["role"] == "public_source" for d in owned),
                            "protected_interface": len(prot)},
               "closure": closure, "preflight": psum, "evidence": esum,
               "export": {f: {k: v for k, v in exp[f].items() if k not in ("not_reached",)} | {"unquotable_roots": unresolved_unq[f],
                          "stack_overflow_parts_at_default_stack": len(merged[f].get("stack_overflow_default", []))} for f in FAMS},
               "rts_reconciliation": rts_reconciliation(decls)}
    # blocker map
    groups = []
    for x in g["groups"]:
        y = dict(x)
        y["affected_root_ids"] = x["affected_root_ids"][:200]
        y["affected_root_ids_truncated"] = len(x["affected_root_ids"]) > 200
        groups.append(y)
    unq = defaultdict(lambda: {"roots": [], "path": None})
    for f in FAMS:
        for r, v in merged[f]["unquotable"].items():
            k = v["path"][-1]
            unq[k]["roots"].append(r)
            unq[k]["path"] = unq[k]["path"] or v["path"]
            unq[k]["reason"] = v["reason"]
    blockers = {"schema": "rocq2lean-prosa-inventory-blockers/1",
                "categories": ["missing_rule", "incorrect_implementation", "source_assumption", "universe_instance",
                               "interface_specialization", "source_build", "resource_limit"],
                "groups": groups,
                "co_blocking_combinations": g["co_blocking_combinations"][:60],
                "build": [{"family": r["family"], "file": r["file"], "build": r["build"], "reason": r["build_reason"],
                           "proposed_change": json.loads(r["proposed_change"]) if r["proposed_change"] else None,
                           "category": "source_build"} for r in files if r["build"] != "COMPILED"],
                "export": {"unquotable": [{"blocking_declaration": k, "category": "missing_rule", "mechanism": v.get("reason"),
                                           "roots": sorted(v["roots"]), "example_path": v["path"]} for k, v in sorted(unq.items())],
                           "failed": {f: merged[f]["failed"] for f in FAMS},
                           "stack_overflow_at_default_stack": {f: merged[f].get("stack_overflow_default", []) for f in FAMS}},
                "interface_conflicts": esum["interface_conflicts"],
                "context_dependent": {n: {"category": v["failures"][0]["category"], "failures": [{k: f[k] for k in ("reason", "source", "translated_in")} for f in v["failures"]],
                                          "detail": v["failures"][0]["detail"][:400], "roots_reaching": v["roots_reaching"]}
                                      for n, v in g.get("context_dependent", {}).items()},
                "preflight_contradicted_by_evidence": {n: dict(v, category="incorrect_implementation",
                                                              note="preflight's static rule rejects a declaration that a current run translated (stale preflight metadata)")
                                                       for n, v in g.get("preflight_contradicted_by_evidence", {}).items()},
                "resource_limits": {
                    "exporter_stack_at_cli_default": {
                        "category": "resource_limit",
                        "parts": {f: len(merged[f].get("stack_overflow_default", [])) for f in FAMS},
                        "roots_in_overflowing_parts": {f: len({r for x in merged[f].get("stack_overflow_default", []) for r in x["roots"]}) for f in FAMS},
                        "minimal_reproducers": PROBES.get("stack", []),
                        "note": "Rocq2Lean Export fails with `Stack overflow` at the default 8 MB stack; the census re-ran these parts with a 4 GB stack. Single large proofs export fine; the culprit inside the closure is not isolated. The roots of overflowing parts are an upper bound."},
                    "preflight_python_recursion": {"category": "resource_limit", "declarations": g.get("preflight_recursion_limited", []),
                                                   "note": "tools/preflight.py exceeds Python's default recursion limit on these terms; the census classified them with a raised limit"}},
                "recommended_tasks": recommendations(g, groups, {d["id"]: d["family"] for d in owned},
                                                     {d["id"]: bool(d["protected_interface"]) for d in owned}, list(cov.values())),
                "notes": ["A root's blockers are all known-blocked declarations its closure reaches; a mechanism's "
                          "sole_blocker_roots are the roots that no other known mechanism blocks.",
                          "Preflight is static: CANDIDATE_SUPPORTED is not a translation result. Translation-only "
                          "failures are known only where a current run reached the declaration."]}
    OUT.mkdir(parents=True, exist_ok=True)
    (OUT / "summary.json").write_text(json.dumps(summary, indent=1, sort_keys=True) + "\n")
    (OUT / "blockers.json").write_text(json.dumps(blockers, indent=1, sort_keys=True) + "\n")
    print(json.dumps({"verdict": verdict, "gaps": len(gaps), "declarations": dsum["modern"]["declarations"] + dsum["classic"]["declarations"]}))


if __name__ == "__main__":
    main()

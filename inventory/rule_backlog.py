"""The rule backlog (reports/statement_only/RULE_BACKLOG.{json,md}), recomputed from a measured corpus
run: every protected root that is not claimed (Blocked Dependency / Direct Failure) is traced through
its `blocked_by` chains to the direct failures that block it, and every direct failure is assigned to
a blocker family by its mechanism (the translator's refusal); a failure no rule recognizes is
UNCLASSIFIED. For each family: members, affected protected roots (modern / Classic), roots blocked
only by that family, an example dependency path and a minimal reproducer (the member with the
smallest dependency closure). Separately: pending proof tasks (for the proving agent), assembly and
computational-representation barriers, validation and tooling gaps.

Curated per-family text (mechanism, proposed change, acceptance tests, status, priority) lives in
FAMILY_NOTES below; the numbers are always recomputed.

    python3 -I inventory/rule_backlog.py RUN [--conversion CONVERSION_DEPENDENCE.json]
"""
import json
import re
import sys
from collections import Counter, defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "reports" / "statement_only"
CLAIMED = ("TRANSLATED_AND_CHECKED", "PENDING_KERNEL_CHECKED", "STATEMENT_KERNEL_CHECKED",
           "STATEMENT_PENDING_KERNEL_CHECKED", "BOOTSTRAP_RESOLVED")
BLOCKED = ("BLOCKED_DEPENDENCY", "OBLIGATIONS_PENDING")

# (family id, status regex, message regex) -- first match wins; message = before " [last tier"
RULES = [
    ("COUPLED_BINDER_LEVELS", "UNIVERSE_REJECTED", r"^statement specialization refused: binder level"),
    ("RESIDUAL_STATEMENT_LEVELS", "UNIVERSE_REJECTED", r"^statement specialization refused: \d+ universe level\(s\) of the statement are not determined"),
    ("STATEMENT_FREE_LEVEL_PINNED", "UNIVERSE_REJECTED", r"^statement specialization refused: \S+: the level of \S+ is free"),
    ("PROTECTED_RANGE_NARROWED", "UNIVERSE_REJECTED", r"^protected public declaration: universe specialization refused"),
    ("SOLUTION_FACT_VIOLATED", "UNIVERSE_REJECTED", r"^proof-local level \S+ solved as .*native fact"),
    ("REFERENCE_COHERENCE", "UNIVERSE_REJECTED", r"coherence: source level \S+ is shared with the referring declaration"),
    ("REFERENCE_RAISING", "UNIVERSE_REJECTED", r"is not entailed by the source universe graph"),
    ("R2BV_REFUSED", "UNIVERSE_REJECTED", r"^R2B-V:"),
    ("UNIVERSE_OTHER", "UNIVERSE_REJECTED", r""),
    ("STATEMENT_R2BP", "INTERFACE_REJECTED", r"^statement specialization refused \(R2B-P"),
    ("PROTECTED_R2BS_R2BP", "INTERFACE_REJECTED", r"^protected public declaration: statement specialization refused"),
    ("INTERFACE_OTHER", "INTERFACE_REJECTED", r""),
    ("MULTI_INSTANCE_PREREQUISITE", "TRANSLATION_FAILED", r"is needed at two different types"),
    ("INTERNAL_ERROR", "TRANSLATION_FAILED", r"internal error"),
    ("PROP_TYPE_CUMULATIVITY", "KERNEL_REJECTED", r"(?s)application type mismatch.*(Prop|Type)"),
    ("KERNEL_OTHER", "KERNEL_REJECTED", r""),
    ("COURSE_OF_VALUES", "UNSUPPORTED_FEATURE", r"course-of-values"),
    ("TERMINATION_DEFERRED", "UNSUPPORTED_FEATURE", r"termination deferred"),
    ("POLYMORPHIC_INSTANCE", "UNSUPPORTED_FEATURE", r"non-empty universe instance"),
    ("COINDUCTIVE", "UNSUPPORTED_FEATURE", r"coinductive"),
    ("UNSUPPORTED_OTHER", "UNSUPPORTED_FEATURE", r""),
]

FAMILY_NOTES = {
    "COUPLED_BINDER_LEVELS": {
        "category": 1, "priority": "P1 (R-SPLIT experimental, entry 9)",
        "mechanism": "a statement's independent binder levels would be identified (or one fixed) by the "
                     "translation: a referenced declaration carries ONE Lean universe parameter for several "
                     "arguments that Rocq instantiates at independent levels by cumulativity (CoqEAL list_R's "
                     "single level 190 for both carriers and the relation: refine_* obligations; fixtures "
                     "SF.R2.pairR_intro, SF.Split.pR_intro). Refused by the round-2 binder-independence check.",
        "proposal": "R-SPLIT (approved as an experimental rule, branch rules-split, docs/LEVEL_SPLIT.md): a level "
                    "that is the sort of >= 2 parameter binders and occurs nowhere else but the result sort gets "
                    "one universe parameter per binder; 13 CoqEAL declarations (17 levels) are eligible.",
        "acceptance": "refine_* obligations generic without identification; binder-independence and generality "
                      "negative controls unchanged; corpus re-measured.",
        "status": "R-SPLIT implemented (not merged); see ITERATION_LOG entry 9 for the corpus measurement"},
    "RESIDUAL_STATEMENT_LEVELS": {
        "category": 1, "priority": "P1/P2",
        "mechanism": "a statement level left free after unification is not mapped to a source level by R3G "
                     "(C-1 refuses it rather than default it). Two shapes: (a) the free level occurs only as "
                     "max(u, r) with the source level u, so any value of r gives the same statement "
                     "(refine_*); (b) the level reaches references through max(...) of several source levels "
                     "(HB_unnamed_mixin_106/107 obligations).",
        "proposal": "P1: an independently checked irrelevance criterion for residual levels (the statement and "
                    "every reference instance are unchanged, up to level normalization, whatever value the "
                    "residual takes under the source constraints); P2: max-coupled source levels mapped "
                    "coherently to parameters.",
        "acceptance": "refine_* restored; negative controls (real narrowing with every self-report hidden) "
                      "still rejected; full corpus re-measured.",
        "status": "round 2: the blanket refusal replaced by binder independence + generality; jointly "
                  "occurring max metavariables identified (P2). (Entry 9 correction: the remaining members were "
                  "attributed to pcancel-like single-level references; ssrfun.pcancel's two carriers are at "
                  "separate levels, so that attribution was wrong.)"},
    "STATEMENT_FREE_LEVEL_PINNED": {
        "category": 1, "priority": "P2 (case A: R3G-F experimental, entry 10; case B: needs a decision)",
        "mechanism": "C-1 generality: a statement's reference argument for a source-free level is closed. Entry 10 split "
                     "the members mechanically by where the pinned level occurs in the referenced source declaration. "
                     "Case A (result-sort-only: hasDecEq.axioms_ eqtype.32, hasChoice.axioms_ choice.299; 280 members in "
                     "R-SPLIT): the class records' fields fixed that level to 0 (R3″). Case B (a structure's carrier, a "
                     "field sort: Equality.type 51, Countable.type 959, Choice.type 333, JobType/TaskType; 73 members): a "
                     "concrete instance (nat_eqType packs Nat : Type 0) coupled to a generic one through one carrier "
                     "level (prod_eqType SporadicTask nat_eqType).",
        "proposal": "case A: R3G-F (docs/RESULT_SORT_LEVELS.md, branch rules-rsonly, not merged): such a level is an "
                    "implicit universe parameter of the block, read minimally, scoped by the dependency closure. Case B: "
                    "needs a representation decision (lifted carriers of concrete instances with transport at every "
                    "use of `sort`, or per-operand carrier levels of structure operations); kept blocked.",
        "acceptance": "case A: 276 of 280 members accepted (4 remain: a mixin level identified with another statement "
                      "level, Builders_62.HB_unnamed_factory_64); case B: unchanged.",
        "status": "case A: R3G-F measured (not merged); case B: awaiting a representation decision"},
    "PROTECTED_RANGE_NARROWED": {
        "category": 1, "priority": "P4", "mechanism": "a protected definition's only current translation narrows a "
        "quantification range (JobReady, ideal/overheads processor_state: unit's finType forces Job to level 0).",
        "proposal": "representation decision needed (explicit lifting of the core finType); not changed without "
                    "approval.", "acceptance": "-", "status": "exact blocker (needs a representation decision)"},
    "SOLUTION_FACT_VIOLATED": {
        "category": 1, "priority": "P2-adjacent", "mechanism": "a solved (proof-local or identified) level "
        "violates a native fact (R2S/R2B), mostly MathComp nmodule/order structure levels identified by "
        "unification.", "proposal": "analyse together with max coupling (the identification usually comes "
        "from max(...) arguments).", "acceptance": "-", "status": "open"},
    "MULTI_INSTANCE_PREREQUISITE": {
        "category": 1, "priority": "P3 (done, entry 8)", "mechanism": "a pending prerequisite statement is needed "
        "at two universe instances in one declaration.", "proposal": "implemented: one hypothesis per instance.",
        "acceptance": "test-multi-instance; the 9 corpus rows now stop at their next blockers.", "status": "done"},
    "REFERENCE_COHERENCE": {
        "category": 1, "priority": "P2-adjacent", "mechanism": "an argument for a level shared with the referring "
        "declaration is not that level's (R2F) reading: JobType/TaskType's second level is read max(u51+1, u58); "
        "unification with a single-level sort `?a+1` makes the bounded solver set the free level to 0 "
        "(max(?a+1, ?x) = ?a+1 ⇒ ?x := 0), which the generality check refuses (last tier).",
        "proposal": "a representation question of its own (a single-level occurrence vs a two-level R2F "
                    "reading; entry 9: not the COUPLED_BINDER_LEVELS mechanism); not changed without approval. Entry 10: "
                    "the P2 retry tier for definitions (joint identification + bounded solver, kept only with fewer "
                    "defaults and parameters of the type) and R3G-F's minimal reading resolve some members (3 protected "
                    "Prosa roots: delay_propagation.propagated_arrival_curve_{valid,respected}, "
                    "instantiated_task_intra_interference_is_bounded); attribution by ablation in entry 10.",
        "acceptance": "-", "status": "diagnosed; partly resolved (entry 10)"},
    "PROP_TYPE_CUMULATIVITY": {
        "category": 1, "priority": "P4", "mechanism": "a Prop-valued term where Rocq expects Type (Prop <= Type "
        "cumulativity), mostly CoqEAL parametricity relations.", "proposal": "representation decision "
        "(no Prop->Type change without approval)", "acceptance": "-", "status": "exact blocker"},
    "INTERNAL_ERROR": {"category": 1, "priority": "P4", "mechanism": "translator internal error (gcdn: unknown "
        "metavariable in a termination-lowered dependent that needs the unfolding).", "proposal": "turn into a "
        "clean refusal", "acceptance": "-", "status": "open"},
}


def classify(r):
    st, m = r["status"], (r.get("message") or "").split(" [last tier")[0]
    for fid, s_re, m_re in RULES:
        if st == s_re and re.search(m_re, m):
            return fid
    return "UNCLASSIFIED"


def main(run, conv=None):
    run = Path(run)
    rep = json.loads((run / "translation_report.json").read_text())
    rows = {r["source"]: r for r in rep["results"]}
    prot = set(json.loads((ROOT / "reports/prosa_inventory/protected_interface.json").read_text())["protected"])
    fam_of = lambda n: "classic" if n.startswith("prosa.classic.") else "modern"
    deps = {}
    with open(run / "source.ndjson") as fh:
        for line in fh:
            if line.startswith('{"kind":"constant"') or line.startswith('{"kind":"inductive"'):
                d = json.loads(line)
                dd = d.get("deps") or {}
                deps[d["name"]] = set(dd.get("type", [])) | set(dd.get("body", []))
    memo, path_memo = {}, {}

    def blockers(n, stack=()):
        if n in memo:
            return memo[n]
        r = rows.get(n)
        if r is None or n in stack:
            return {}
        if r["status"] in CLAIMED:
            return {}
        if r["status"] not in BLOCKED:
            memo[n] = {n: [n]}
            return memo[n]
        out = {}
        for b in r.get("blocked_by") or []:
            for x, p in blockers(b, stack + (n,)).items():
                out.setdefault(x, [n] + p)
        memo[n] = out
        return out

    closure_memo = {}

    def closure(n):
        if n in closure_memo:
            return closure_memo[n]
        seen, st = set(), [n]
        while st:
            x = st.pop()
            for y in deps.get(x, ()):
                if y not in seen:
                    seen.add(y)
                    st.append(y)
        closure_memo[n] = len(seen)
        return len(seen)

    direct = {n: classify(r) for n, r in rows.items() if r["status"] not in CLAIMED + BLOCKED}
    roots = sorted(n for n in prot if n in rows and rows[n]["status"] not in CLAIMED)
    per_root = {}
    for n in roots:
        bs = blockers(n)
        per_root[n] = {"family": fam_of(n), "status": rows[n]["status"],
                       "direct_blockers": sorted(bs), "blocker_families": sorted({direct.get(b, "UNCLASSIFIED") for b in bs}),
                       "example_path": next(iter(bs.values()), [n])}
    fams = defaultdict(lambda: {"members": [], "affected": set(), "only": set()})
    for n, f in direct.items():
        fams[f]["members"].append(n)
    for n, x in per_root.items():
        for f in x["blocker_families"]:
            fams[f]["affected"].add(n)
        if len(x["blocker_families"]) == 1:
            fams[x["blocker_families"][0]]["only"].add(n)
        if not x["blocker_families"]:
            fams["UNCLASSIFIED"]["affected"].add(n)
            fams["UNCLASSIFIED"]["only"].add(n)
    out_f = []
    for f, x in fams.items():
        mem = sorted(x["members"], key=lambda n: (closure(n), n))
        ex_root = next((n for n in sorted(x["affected"]) if any(direct.get(b) == f for b in per_root[n]["direct_blockers"])), None)
        ex_path = None
        if ex_root:
            b = next(b for b in per_root[ex_root]["direct_blockers"] if direct.get(b) == f)
            ex_path = blockers(ex_root)[b]
        sub = Counter()
        for n in mem:
            m = (rows[n].get("message") or "").split(" [last tier")[0]
            sub[re.sub(r"[\w./']+\.[\w']+", "X", m)[:110]] += 1
        out_f.append({
            "family": f, **FAMILY_NOTES.get(f, {"category": 1, "priority": "unranked", "status": "open"}),
            "members": len(mem), "protected_members": sum(1 for n in mem if n in prot),
            "affected_roots": {"total": len(x["affected"]), "modern": sum(1 for n in x["affected"] if fam_of(n) == "modern"),
                               "classic": sum(1 for n in x["affected"] if fam_of(n) == "classic")},
            "roots_blocked_only_by_this_family": {"total": len(x["only"]), "modern": sum(1 for n in x["only"] if fam_of(n) == "modern"),
                                                  "classic": sum(1 for n in x["only"] if fam_of(n) == "classic")},
            "message_shapes": sub.most_common(6),
            "minimal_reproducer": mem[0] if mem else None, "reproducer_closure": closure(mem[0]) if mem else None,
            "example_root": ex_root, "example_path": ex_path, "members_sample": mem[:15]})
    out_f.sort(key=lambda x: (-x["affected_roots"]["total"], x["family"]))
    # 2. pending proof tasks (for the proving agent), 3. assembly / representation barriers
    st = {}
    with open(run / "source.ndjson") as fh:
        for line in fh:
            if line.startswith('{"kind":"constant"'):
                d = json.loads(line)
                st[d["name"]] = d["body_state"]
    pend = [r for n, r in rows.items() if n in prot and r["status"] in ("PENDING_KERNEL_CHECKED", "STATEMENT_PENDING_KERNEL_CHECKED")]
    need = Counter(h for r in pend for h in r.get("pending_hypotheses") or [])
    tasks = Counter()
    if (run / "PROOF_TASKS.jsonl").exists():
        tasks = Counter(json.loads(l)["kind"] for l in open(run / "PROOF_TASKS.jsonl"))
    opaque_val = sorted(h for h in need if st.get(h) == "opaque_interface")
    barriers = {"opaque_values_kept_as_interfaces": {h: need[h] for h in opaque_val},
                "protected_pending_needing_an_opaque_value": sum(1 for r in pend if any(st.get(h) == "opaque_interface" for h in r["pending_hypotheses"])),
                "termination_obligations": {h: need[h] for h in need if "__rocq2lean_termination_" in h},
                "pending_inductives_reemitted_at_assembly (ASSEMBLY_TRANSPORT_REQUIRED for statements about them)":
                    sum(1 for n, r in rows.items() if r["status"] == "PENDING_KERNEL_CHECKED" and r.get("kind") == "inductive")}
    if conv and Path(conv).exists():
        c = json.loads(Path(conv).read_text())
        barriers["conversion_dependence_needs_unfolding"] = [x["declaration"] for x in c.get("needs_unfolding", [])]
    res = {"schema": "rocq2lean-rule-backlog/1", "run": str(run), "report_input_sha256": rep.get("input_sha256"),
           "protected": len(prot), "unclaimed_protected_roots": len(roots),
           "unclaimed_by_family": dict(Counter(fam_of(n) for n in roots)),
           "direct_failures": len(direct), "families": out_f,
           "pending_proof_tasks": {"protected_pending_rows": len(pend), "tasks_by_kind": dict(tasks),
                                   "top_prerequisites": need.most_common(15)},
           "assembly_and_representation_barriers": barriers,
           "roots": per_root}
    OUT.mkdir(parents=True, exist_ok=True)
    (OUT / "RULE_BACKLOG.json").write_text(json.dumps(res, indent=1, sort_keys=True) + "\n")
    (OUT / "RULE_BACKLOG.md").write_text(render(res))
    print(json.dumps({k: res[k] for k in ("unclaimed_protected_roots", "unclaimed_by_family", "direct_failures")}))
    for x in out_f:
        print(f'{x["family"]:32} members {x["members"]:4} (prot {x["protected_members"]:3})  affected {x["affected_roots"]["total"]:4}  only {x["roots_blocked_only_by_this_family"]["total"]:4}  repro {x["minimal_reproducer"]} ({x["reproducer_closure"]})')
    return res


CATEGORY = {1: "translation rule / implementation", 2: "pending proof task", 3: "assembly / representation barrier",
            4: "validation / tooling gap"}
GAPS = [  # category 4: validation and tooling gaps (curated; each with its evidence)
    ("Request independence of the batched statement re-derivation is sampled (8 constants per export)",
     "tools/roundtrip.py STATEMENT_SAMPLE; PROVENANCE.md §6", "open"),
    ("Non-protected definition types: free-level pins are a diagnostic, not a rejection",
     "audit.json definition_type_specialization_candidates", "open (by design; protected ones rejected)"),
    ("Protected definitions are checked at their binder domains, not their result types (R2B-V aside)",
     "docs/UNIVERSE_FAMILY_C.md §2", "open"),
    ("Corpus path lacked the CLI's R2B-P checks (pending R2B-P claimed: eqtype.insub; accepted R2B-P rows not "
     "re-checked at their instances)", "ITERATION_LOG entry 7; statement_run.py instances", "fixed in round 2"),
    ("Corpus manifest bound runs whose consumer/audit were not OK", "ITERATION_LOG entry 6", "fixed (df09655)"),
]


def render(res):
    L = ["# Rule backlog", "",
         f"Generated by `inventory/rule_backlog.py` from `{res['run']}` (do not edit by hand; curated text lives in the",
         "tool). Every unclaimed protected root is traced through its `blocked_by` chains to the direct failures",
         "blocking it; every direct failure is assigned to a family by its mechanism (UNCLASSIFIED otherwise).",
         "Machine-readable companion: `RULE_BACKLOG.json` (per-root blockers and example paths).", "",
         f"Unclaimed protected roots: **{res['unclaimed_protected_roots']}** "
         f"(modern {res['unclaimed_by_family'].get('modern', 0)}, Classic {res['unclaimed_by_family'].get('classic', 0)}); "
         f"direct failures (all rows): {res['direct_failures']}.", "",
         "## 1. Translation-rule / implementation families", "",
         "| family | members (protected) | affected roots (modern / Classic) | only this family | priority | status |",
         "|---|---|---|---|---|---|"]
    for f in res["families"]:
        a, o = f["affected_roots"], f["roots_blocked_only_by_this_family"]
        L.append(f"| `{f['family']}` | {f['members']} ({f['protected_members']}) | {a['total']} ({a['modern']} / {a['classic']}) | "
                 f"{o['total']} | {f.get('priority', '')} | {f.get('status', '')} |")
    L += ["", "Per family (mechanism, reproducer, example path, proposal, acceptance):", ""]
    for f in res["families"]:
        L += [f"### `{f['family']}`", "",
              f"* mechanism: {f.get('mechanism', 'see message shapes')}",
              f"* minimal reproducer: `{f['minimal_reproducer']}` (closure {f['reproducer_closure']})",
              f"* example path: {' → '.join('`' + x + '`' for x in (f['example_path'] or [])[:6])}",
              f"* message shapes: " + "; ".join(f"{c}× {m}" for m, c in f["message_shapes"][:3]),
              f"* proposal: {f.get('proposal', '—')}", f"* acceptance: {f.get('acceptance', '—')}", ""]
    p = res["pending_proof_tasks"]
    L += ["## 2. Pending proof tasks (for the proving agent; not translation work)", "",
          f"Protected pending rows: {p['protected_pending_rows']}; tasks by kind: {p['tasks_by_kind']}.", "",
          "Top prerequisites (pending protected rows needing them): " +
          ", ".join(f"`{h}` {c}" for h, c in p["top_prerequisites"][:10]), "",
          "## 3. Assembly / computational-representation barriers", ""]
    for k, v in res["assembly_and_representation_barriers"].items():
        L.append(f"* {k}: {v}")
    L += ["", "## 4. Validation and tooling gaps", "", "| gap | evidence | status |", "|---|---|---|"]
    for g, e, st in GAPS:
        L.append(f"| {g} | {e} | {st} |")
    return "\n".join(L) + "\n"


if __name__ == "__main__":
    a = sys.argv[1:]
    main(a[0], a[a.index("--conversion") + 1] if "--conversion" in a else None)

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
        "status": "P1 in progress"},
    "STATEMENT_FREE_LEVEL_PINNED": {
        "category": 1, "priority": "P2 (re-ranked: largest family)",
        "mechanism": "C-1 generality: a statement's reference argument for a source-free level is closed (mostly "
                     "MathComp mixin levels eqtype.32 / choice.299 reached through a referenced definition "
                     "whose level the translation fixed); translating it would specialize the statement.",
        "proposal": "trace each to the referenced definition that pins the level; make that definition generic "
                    "where its value allows (shared with the max-coupling analysis).",
        "acceptance": "statement generic, audit generality check passes; no protected range narrowed.",
        "status": "diagnosed (this backlog)"},
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
        "category": 1, "priority": "P3", "mechanism": "a pending prerequisite statement is needed at two "
        "universe instances in one declaration; the hypothesis telescope has one binder per prerequisite name.",
        "proposal": "instance-aware prerequisite identities (one hypothesis per (prerequisite, instance)).",
        "acceptance": "translation, audit, tasks and assembly consistent; no hypothesis reused at a wrong type.",
        "status": "open"},
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
    print(json.dumps({k: res[k] for k in ("unclaimed_protected_roots", "unclaimed_by_family", "direct_failures")}))
    for x in out_f:
        print(f'{x["family"]:32} members {x["members"]:4} (prot {x["protected_members"]:3})  affected {x["affected_roots"]["total"]:4}  only {x["roots_blocked_only_by_this_family"]["total"]:4}  repro {x["minimal_reproducer"]} ({x["reproducer_closure"]})')
    return res


if __name__ == "__main__":
    a = sys.argv[1:]
    main(a[0], a[a.index("--conversion") + 1] if "--conversion" in a else None)

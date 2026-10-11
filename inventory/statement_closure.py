"""Statement/definition closure of Prosa v0.6 + Classic (statement-only policy, Phase B).

Input: the census store (.work/inventory/ir-{modern,classic}.ndjson: every elaborated record of the
proof-preserving closure, with dependencies split into type and body), declarations.jsonl (roles and
natures read from the elaborated types) and the historical graph.json (blocker evidence).

Policy (docs/STATEMENT_ONLY_DESIGN.md):
  * roots: every protected declaration (public Prosa/Classic declarations and projections);
  * proof-valued declaration (nature proof_* or a source assumption whose type is a proposition): its
    STATEMENT is needed (type edges, kind `statement`); its body is never followed (`proof_only`);
  * any other constant: type edges (`statement`) and body edges; a body edge to a non-proof declaration
    is `computation`; a body edge to a proof-valued constant is `obligation` (the proof is needed to
    assemble the definition; only that proof's statement enters the closure);
  * inductive: its arity, parameters and constructor types (`datatype`).
Inline proof subterms of definition bodies (not references to proof-valued constants) are not
delimited here (that needs typing; the statement-only exporter does it). Their references are kept
as `computation` edges: the closure below is an over-approximation for such definitions, which is
reported.

Writes reports/statement_only/closure.jsonl, closure_summary.json, blocker_reassessment.json.

    python3 -I inventory/statement_closure.py
"""
import json
from collections import Counter, defaultdict, deque
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
W = ROOT / ".work" / "inventory"
INV = ROOT / "reports" / "prosa_inventory"
OUT = ROOT / "reports" / "statement_only"
PROOF = ("proof_opaque", "proof_transparent")


def main():
    store = {}
    for fam in ("modern", "classic"):
        with open(W / f"ir-{fam}.ndjson") as fh:
            for line in fh:
                d = json.loads(line)
                store.setdefault(d["name"], d)
    decls = {}
    for line in open(INV / "declarations.jsonl"):
        r = json.loads(line)
        if r["role"] != "alias_reexport":
            decls[r["id"]] = r

    def is_proof(n):
        r = decls.get(n)
        if not r:
            return False
        if r["nature"] in PROOF:
            return True
        # a source assumption (Admitted) whose type is a proposition is a theorem statement
        return r["nature"] == "assumption" and store.get(n, {}).get("kind") == "constant" and _prop_type(store, decls, n)

    roots = sorted(n for n, r in decls.items() if r.get("protected_interface") and n in store)
    edges, kinds = {}, Counter()
    reach, via = {}, {}
    q = deque()
    for r in roots:
        reach[r] = "root"
        q.append(r)
    while q:
        n = q.popleft()
        d = store[n]
        deps = d.get("deps") or {}
        out = []
        for m in deps.get("type", []):
            out.append((m, "datatype" if d["kind"] == "inductive" else "statement"))
        if d["kind"] == "constant" and not is_proof(n):
            for m in deps.get("body", []):
                out.append((m, "obligation" if is_proof(m) else "computation"))
        edges[n] = out
        for m, k in out:
            kinds[k] += 1
            if m in store and m not in reach:
                reach[m] = k
                via[m] = n
                q.append(m)
    # what each reached declaration is needed for
    need = defaultdict(set)
    for n, out in edges.items():
        for m, k in out:
            need[m].add(k)
    old = set(store)
    new = set(reach)
    proof_only = old - new
    fam = lambda n: decls.get(n, {}).get("family", "external")
    nat = lambda n: decls.get(n, {}).get("nature", "unknown")
    obligations = sorted(m for m in new if "obligation" in need[m])
    tasks = sorted(n for n in new if is_proof(n))
    rows = []
    for n in sorted(new):
        rows.append({"id": n, "family": fam(n), "kind": store[n]["kind"], "nature": nat(n),
                     "role": decls.get(n, {}).get("role", "external_dependency"),
                     "protected": bool(decls.get(n, {}).get("protected_interface")),
                     "translate": "statement" if is_proof(n) else ("datatype" if store[n]["kind"] == "inductive" else "definition"),
                     "needed_for": sorted(need[n]) or ["root"], "reached_via": via.get(n),
                     "proof_task": is_proof(n), "obligation_for_definitions": n in obligations,
                     "edges": {k: sorted({m for m, kk in edges.get(n, []) if kk == k})
                               for k in ("statement", "datatype", "computation", "obligation") if any(kk == k for _, kk in edges.get(n, []))}})
    OUT.mkdir(parents=True, exist_ok=True)
    with open(OUT / "closure.jsonl", "w") as fh:
        for r in rows:
            fh.write(json.dumps(r, sort_keys=True) + "\n")
    by = lambda xs, key: dict(sorted(Counter(key(x) for x in xs).items(), key=lambda kv: -kv[1]))
    lib = lambda n: n.split(".")[0] if fam(n) == "external" else fam(n)
    summary = {
        "schema": "rocq2lean-statement-closure/1",
        "roots": {"total": len(roots), "by_family": by(roots, fam)},
        "old_proof_preserving_closure": len(old),
        "statement_closure": len(new),
        "statement_closure_by_family": by(new, lib),
        "statement_closure_by_translation": by(rows, lambda r: r["translate"]),
        "eliminated_proof_only": len(proof_only),
        "eliminated_by_family": by(proof_only, lib),
        "eliminated_by_nature": by(proof_only, nat),
        "proof_tasks": {"total": len(tasks), "by_family": by(tasks, lib),
                        "in_scope_theorem_statements": sum(1 for n in tasks if fam(n) in ("modern", "classic"))},
        "obligation_statements": {"total": len(obligations), "by_family": by(obligations, lib)},
        "definitions_needing_obligations": sum(1 for n, out in edges.items() if any(k == "obligation" for _, k in out)),
        "edge_kinds": dict(kinds),
        "approximation": "inline proof subterms of definition bodies are not delimited (typing needed); their references count as computation edges",
    }
    (OUT / "closure_summary.json").write_text(json.dumps(summary, indent=1) + "\n")
    # blocker reassessment against the historical evidence
    g = json.loads((W / "graph.json").read_text())
    extra = json.loads((W / "extra_blockers.json").read_text())
    nodes = set(g.get("known_blockers", {})) | set(extra.get("declarations", {})) | set(extra.get("context_dependent", {}))
    named = ["mathcomp.boot.eqtype.Sub_spec", "mathcomp.boot.eqtype.insub_spec", "mathcomp.boot.div.edivn_rec",
             "mathcomp.boot.div.modn_rec", "mathcomp.boot.choice.PCanHasChoice", "mathcomp.boot.bigop.big_const_seq",
             "prosa.model.priority.definitions.FP_policy", "prosa.model.priority.definitions.JLFP_policy",
             "prosa.model.priority.definitions.JLDP_policy", "mathcomp.boot.ssrnat.leqif", "Corelib.ssr.ssrfun.pair_of_and",
             "mathcomp.boot.ssrnat.nat_of_add_pos", "mathcomp.boot.fintype/isFinite.axioms_",
             "Corelib.ssr.ssreflect_rw.nary_congruence", "mathcomp.boot.bigop.big_morph", "mathcomp.boot.seq.mask_cat",
             "prosa.implementation.definitions.extrapolated_arrival_curve.ArrivalCurvePrefix",
             "prosa.implementation.definitions.task.concrete_job", "Corelib.Classes.Morphisms.normalization_done"]
    rea = []
    for n in sorted(set(named) | nodes):
        if n not in store:
            continue
        reasons = [k["mechanism"] for k in g.get("known_blockers", {}).get(n, [])] + \
                  [x["reason"] for x in extra.get("declarations", {}).get(n, [])] + \
                  [x["reason"] for x in extra.get("context_dependent", {}).get(n, [])]
        locs = g.get("preflight_declarations", {}).get(n, {}).get("locations", {})
        in_new = n in new
        proof = is_proof(n)
        if not in_new:
            verdict = "PROOF_ONLY_REMOVED"
        elif proof:
            verdict = "STATEMENT_NEEDED_BODY_IRRELEVANT"
        else:
            verdict = "STILL_REQUIRED"
        rea.append({"declaration": n, "family": fam(n), "nature": nat(n), "historical_reasons": sorted(set(reasons)),
                    "preflight_locations": locs, "in_statement_closure": in_new, "needed_for": sorted(need[n]) if in_new else [],
                    "proof_valued": proof, "verdict": verdict, "example_path": _path(via, n) if in_new else None})
    # roots reaching each still-needed blocker in the statement closure (reverse reachability)
    rev = defaultdict(set)
    for n, out in edges.items():
        for m, k in out:
            rev[m].add(n)
    rootset = set(roots)
    for r in rea:
        if not r["in_statement_closure"]:
            continue
        seen, stack = {r["declaration"]}, [r["declaration"]]
        while stack:
            x = stack.pop()
            for y in rev[x]:
                if y not in seen:
                    seen.add(y)
                    stack.append(y)
        hit = seen & rootset
        r["roots_reaching"] = {"modern": sum(1 for x in hit if fam(x) == "modern"),
                               "classic": sum(1 for x in hit if fam(x) == "classic")}
    (OUT / "blocker_reassessment.json").write_text(json.dumps(rea, indent=1) + "\n")
    print(json.dumps(summary, indent=1))
    print(Counter(r["verdict"] for r in rea))


def _prop_type(store, decls, n):
    t = store[n]["type"]
    while t.get("k") in ("prod", "let"):
        t = t["b"]
    h = t
    while h.get("k") == "app":
        h = h["f"]
    if h.get("k") == "sort":
        return False
    if h.get("k") == "const":
        r = decls.get(h["c"])
        return bool(r) and r["nature"] == "type_former" and _codomain_prop(store, h["c"])
    if h.get("k") == "ind":
        b = store.get(h["ind"]["mind"])
        return bool(b) and b["bodies"][h["ind"]["i"]]["sort"].get("k") in ("prop", "sprop")
    return False


def _codomain_prop(store, n):
    t = store.get(n, {}).get("type", {})
    while t.get("k") == "prod":
        t = t["b"]
    return t.get("k") == "sort" and t["s"].get("k") in ("prop", "sprop")


def _path(via, n):
    p = [n]
    while via.get(p[-1]):
        p.append(via[p[-1]])
    return p[::-1]


if __name__ == "__main__":
    main()

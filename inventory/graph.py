"""Semantic declaration graph, build/import graph, preflight over the whole closure, reachability.

Semantic graph: one node per distinct kernel declaration of the combined closure (modern store ∪ Classic
store; a name present in both must have byte-identical elaborated records, otherwise it is a recorded
shared-library conflict). Edges come from the exporter's elaborated terms: `type` (type, inductive
arities and constructor types), `body` (transparent body) and `opaque_body` (opaque proof body, e.g.
`lia` certificates). Constructors and primitive projections are part of their inductive's node
(the exporter records `construct`, `case` and `proj` as dependencies on the inductive); non-primitive
projections are constants with a type edge to their record. Nothing is inferred from imports.

Build graph: `rocq dep` over each pinned tree (file -> required logical modules).

Preflight: tools/preflight.py's per-declaration classifier, unchanged, over every node. A declaration
is UNSUPPORTED_FEATURE (a direct blocker) when the classifier finds a reason in its own terms; an
in-scope root is BLOCKED_DEPENDENCY when its closure (type + body + opaque body edges) reaches one.
This is the same rule as preflight.preflight's root verdict, computed once for all roots with all
reachable blockers instead of the first one.

Known blockers add the direct translation failures and instance rejections of current runs
(inventory/evidence_blockers.py); a root's `known` verdict uses both, its `preflight` verdict only
preflight. Blocker groups are keyed by mechanism, with category and evidence source.

    python3 -I inventory/graph.py
"""
import hashlib
import json
import os
import re
import subprocess
import sys
from collections import Counter, defaultdict, deque
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CFG = json.loads((ROOT / "inventory" / "config.json").read_text())
W = ROOT / ".work" / "inventory"
OUT = ROOT / "reports" / "prosa_inventory"
X = lambda p: Path(os.path.expanduser(p)) if p.startswith("~") else ROOT / p
sys.path.insert(0, str(ROOT / "tools"))
import preflight  # noqa: E402  (the unchanged translator preflight)


def load_store():
    store, digest, conflicts = {}, {}, {}
    for fam in ("modern", "classic"):
        with open(W / f"ir-{fam}.ndjson") as fh:
            for line in fh:
                d = json.loads(line)
                h = hashlib.sha256(line.encode()).hexdigest()
                n = d["name"]
                if n in digest and digest[n] != h:
                    conflicts[n] = [digest[n], h]
                    continue
                digest[n] = h
                store[n] = d
    return store, digest, conflicts


def edges_of(d):
    out = []
    deps = d.get("deps") or {}
    for m in deps.get("type", []):
        out.append((m, "type"))
    kind = "opaque_body" if d.get("body_state") == "opaque_present" else "body"
    for m in deps.get("body", []):
        out.append((m, kind))
    # primitive projections are `proj` nodes on their record: the exporter records them as dependencies
    # on the inductive itself, so a projection is not a separate node
    return out


def mechanism(reason):
    """Group a preflight reason into a reusable mechanism (drop declaration-specific detail)."""
    r = re.sub(r"\(([^)]*)\)", lambda m: "(" + re.sub(r"[A-Za-z0-9_.']+\.[A-Za-z0-9_']+", "…", m.group(1)) + ")", reason)
    return r


CATEGORY = [
    ("source_assumption", ("genuine source assumption", "body state unavailable")),
    ("source_build", ("relaxed source checking",)),
    ("universe_instance", ("universe", "template", "SProp", "irrelevant")),
    ("missing_rule", ("", )),
]


def category(reason):
    for cat, keys in CATEGORY:
        if any(k in reason for k in keys):
            return cat
    return "missing_rule"


def rocq_dep(fam):
    sys.path.insert(0, str(ROOT / "tools"))
    import rocq2lean
    env = rocq2lean.opam_env()
    mw, cb = X(CFG["modern"]["working"]), X(CFG["classic"]["working"])
    if fam == "modern":
        lp, tree, files = ["-R", str(mw), "prosa"], mw, sorted(p for p in mw.rglob("*.v"))
    else:
        lp = ["-R", str(mw), "prosa", "-R", str(cb / "classic"), "prosa.classic", "-Q", str(cb / "compat"), "Compat"]
        tree, files = cb, sorted((cb / "classic").rglob("*.v"))
    p = subprocess.run(["rocq", "dep", *lp, *map(str, files)], capture_output=True, text=True, env=env, cwd=tree)
    graph = {}
    for line in p.stdout.splitlines():
        m = re.match(r"(\S+)\.vo \S+\.glob \S+\.v\.beautified \S+\.required_vo: (\S+)\.v(.*)$", line)
        if not m:
            continue
        src = os.path.relpath(m.group(2) + ".v", tree).replace("\\", "/")
        reqs = sorted({os.path.relpath(x, ROOT) if not x.startswith("/") else x for x in m.group(3).split() if x.endswith(".vo")})
        graph[src] = reqs
    return graph, p.returncode, p.stderr[-2000:]


def main(build_graph=True):
    store, digest, conflicts = load_store()
    decls = [json.loads(l) for l in open(OUT / "declarations.jsonl")]
    by_id = {d["id"]: d for d in decls}
    inds = preflight.Inductives(store)
    status, recursion_limited = {}, []
    default_limit = sys.getrecursionlimit()
    for n in sorted(store):
        try:
            st, where = preflight.classify(store[n], inds)
        except RecursionError:
            # the CLI's preflight (default Python recursion limit) cannot walk this term: a resource
            # limit of the tool, recorded; the census classifies it with a raised limit
            recursion_limited.append(n)
            sys.setrecursionlimit(200000)
            try:
                st, where = preflight.classify(store[n], inds)
            finally:
                sys.setrecursionlimit(default_limit)
        status[n] = (st, where)
    # graph
    names = sorted(store)
    idx = {n: i for i, n in enumerate(names)}
    adj = [[] for _ in names]
    missing = Counter()
    lines = []
    for n in names:
        es = edges_of(store[n])
        kinds = defaultdict(list)
        for m, k in es:
            kinds[k].append(m)
            if m in idx:
                adj[idx[n]].append(idx[m])
            else:
                missing[m] += 1
        rec = {"graph": "semantic", "id": n, "family": by_id.get(n, {}).get("family", "external"),
               "kind": store[n]["kind"], "edges": {k: sorted(set(v)) for k, v in sorted(kinds.items())}}
        miss = sorted({m for m, _ in es if m not in idx})
        if miss:
            rec["missing_targets"] = miss
        lines.append(rec)
    for fam in ("modern", "classic") if build_graph else ():
        g, rc, err = rocq_dep(fam)
        for f in sorted(g):
            lines.append({"graph": "build", "family": fam, "file": f, "requires_vo": g[f]})
        lines.append({"graph": "build_meta", "family": fam, "rocq_dep_exit": rc, "stderr_tail": err})
    with open(OUT / "dependencies.jsonl", "w") as fh:
        for r in lines:
            fh.write(json.dumps(r, sort_keys=True) + "\n")
    # known reasons: preflight's own, plus direct translation failures / instance rejections from
    # current runs (inventory/evidence_blockers.py), each with its category and evidence source
    extra = json.loads((W / "extra_blockers.json").read_text()) if (W / "extra_blockers.json").exists() else {"declarations": {}}
    known, contradicted = {}, {}
    translated = extra.get("translated_in_current_runs", {})
    for n in names:
        ks = [(mechanism(r), category(r), "preflight") for r in status[n][1]] if status[n][0] != "CANDIDATE_SUPPORTED" else []
        if ks and n in translated:
            # preflight's static rule is contradicted by a current run that translated this very record
            contradicted[n] = {"reasons": sorted(status[n][1]), "translated_in": translated[n]}
            ks = []
        ks += [(x["reason"], x["category"], x["source"]) for x in extra["declarations"].get(n, [])]
        if ks:
            known[n] = ks
    # blocked-set reachability over SCCs (iterative Tarjan), as bitsets over known-blocked nodes
    ctx = {n: v for n, v in extra.get("context_dependent", {}).items() if n in idx}
    blocked = [i for i, n in enumerate(names) if n in known or n in ctx or n in contradicted]
    ctx_mask = sum(1 << k for k, i in enumerate(blocked) if names[i] in ctx and names[i] not in known)
    contra_mask = sum(1 << k for k, i in enumerate(blocked) if names[i] in contradicted and names[i] not in known)
    pf_mask = sum(1 << k for k, i in enumerate(blocked) if status[names[i]][0] != "CANDIDATE_SUPPORTED")
    bit = {i: 1 << k for k, i in enumerate(blocked)}
    N = len(names)
    index, low, onst, st, comp = [None] * N, [0] * N, [False] * N, [], [None] * N
    order, c = [], 0
    counter = 0
    for s in range(N):
        if index[s] is not None:
            continue
        work = [(s, 0)]
        while work:
            v, pi = work.pop()
            if pi == 0:
                index[v] = low[v] = counter
                counter += 1
                st.append(v)
                onst[v] = True
            recurse = False
            for j in range(pi, len(adj[v])):
                w = adj[v][j]
                if index[w] is None:
                    work.append((v, j + 1))
                    work.append((w, 0))
                    recurse = True
                    break
                elif onst[w]:
                    low[v] = min(low[v], index[w])
            if recurse:
                continue
            if low[v] == index[v]:
                members = []
                while True:
                    w = st.pop()
                    onst[w] = False
                    comp[w] = c
                    members.append(w)
                    if w == v:
                        break
                order.append(members)
                c += 1
            if work:
                u = work[-1][0]
                low[u] = min(low[u], low[v])
    # Tarjan emits SCCs in reverse topological order (dependencies first)
    reach = [0] * c
    for members in order:
        ci = comp[members[0]]
        acc = 0
        for v in members:
            acc |= bit.get(v, 0)
            for w in adj[v]:
                if comp[w] != ci:
                    acc |= reach[comp[w]]
        reach[ci] = acc
    closure_size_cache = {}

    def blockers_of(n, mask=None):
        r = reach[comp[idx[n]]]
        if mask is not None:
            r &= mask
        else:
            r &= ~(ctx_mask | contra_mask)
        return [names[blocked[k]] for k in range(len(blocked)) if r >> k & 1]

    def path_to(src, targets):
        """A shortest dependency path from src to any of targets (BFS)."""
        s = idx[src]
        prev = {s: None}
        q = deque([s])
        tg = {idx[t] for t in targets}
        while q:
            v = q.popleft()
            if v in tg:
                p = []
                while v is not None:
                    p.append(names[v])
                    v = prev[v]
                return p[::-1]
            for w in adj[v]:
                if w not in prev:
                    prev[w] = v
                    q.append(w)
        return None

    # roots: every in-scope (modern / Classic owned) declaration that was exported
    roots = [d for d in decls if d["family"] in ("modern", "classic") and d["role"] != "alias_reexport" and d["id"] in idx]
    root_rows = {}
    for d in roots:
        n = d["id"]
        bs = blockers_of(n)
        pf_reach = reach[comp[idx[n]]] & (pf_mask | contra_mask)
        pf_direct = status[n][0] != "CANDIDATE_SUPPORTED"
        root_rows[n] = {"preflight": "UNSUPPORTED_FEATURE" if pf_direct else "BLOCKED_DEPENDENCY" if pf_reach else "CANDIDATE_SUPPORTED",
                        "known": "KNOWN_BLOCKER_DIRECT" if n in known else "KNOWN_BLOCKER_DOWNSTREAM" if bs else "NO_KNOWN_BLOCKER",
                        "reachable_blockers": bs,
                        "context_dependent_reachable": blockers_of(n, ctx_mask),
                        "mechanisms": sorted({k[0] for b in bs for k in known[b]})}
    # blocker map grouped by mechanism
    mech = defaultdict(lambda: {"defining_nodes": set(), "roots": set(), "category": None, "evidence": set()})
    for n, ks in known.items():
        for m, cat, src in ks:
            mech[m]["defining_nodes"].add(n)
            mech[m]["category"] = cat
            mech[m]["evidence"].add(src)
    for rid, rr in root_rows.items():
        for m in rr["mechanisms"]:
            mech[m]["roots"].add(rid)
    fam_of = {d["id"]: d["family"] for d in decls}
    role_of = {d["id"]: d["role"] for d in decls}
    groups = []
    for m, g in mech.items():
        nodes = sorted(g["defining_nodes"])
        rts = sorted(g["roots"])
        prot = [r for r in rts if by_id[r].get("protected_interface")]
        sole = [r for r in rts if root_rows[r]["mechanisms"] == [m]]
        direct = [r for r in rts if r in g["defining_nodes"]]
        # smallest defining node by closure-independent proxy: the node reached by most roots first
        hits = Counter()
        for r in rts:
            for b in root_rows[r]["reachable_blockers"]:
                if b in g["defining_nodes"]:
                    hits[b] += 1
        rep = max(nodes, key=lambda b: (hits[b], -len(b))) if nodes else None
        ex_root = next((r for r in rts if rep in root_rows[r]["reachable_blockers"]), None)
        co = Counter(x for r in rts for x in root_rows[r]["mechanisms"] if x != m)
        groups.append({
            "mechanism": m, "category": g["category"], "evidence": sorted(g["evidence"]),
            "defining_nodes": len(nodes), "defining_nodes_in_scope": sum(1 for b in nodes if fam_of.get(b) in ("modern", "classic")),
            "defining_nodes_sample": nodes[:25],
            "reproducer": {"declaration": rep,
                           "location": next((loc for r, loc in status[rep][1].items() if mechanism(r) == m), None) if rep else None,
                           "detail": next((x["detail"] for x in extra["declarations"].get(rep, []) if x["reason"] == m), None) if rep else None,
                           "affected_roots_through_it": hits[rep] if rep else 0},
            "example_path": path_to(ex_root, [rep]) if ex_root else None,
            "affected_roots": {"modern": sum(1 for r in rts if fam_of[r] == "modern"),
                               "classic": sum(1 for r in rts if fam_of[r] == "classic"),
                               "combined": len(rts)},
            "affected_protected_interface": {"modern": sum(1 for r in prot if fam_of[r] == "modern"),
                                             "classic": sum(1 for r in prot if fam_of[r] == "classic"),
                                             "combined": len(prot)},
            "direct_roots": len(direct), "downstream_roots": len(rts) - len(direct),
            "sole_blocker_roots": {"modern": sum(1 for r in sole if fam_of[r] == "modern"),
                                   "classic": sum(1 for r in sole if fam_of[r] == "classic"),
                                   "combined": len(sole),
                                   "protected": sum(1 for r in sole if by_id[r].get("protected_interface"))},
            "co_blocking_mechanisms": co.most_common(8),
            "affected_root_ids": rts,
        })
    groups.sort(key=lambda g: (-g["affected_protected_interface"]["combined"], g["mechanism"]))
    combos = Counter(tuple(rr["mechanisms"]) for rr in root_rows.values() if rr["mechanisms"])
    res = {"preflight_declarations": {n: {"status": s, "reasons": sorted(w), "locations": w} for n, (s, w) in status.items()},
           "known_blockers": {n: [{"mechanism": m, "category": c, "evidence": e} for m, c, e in ks] for n, ks in known.items()},
           "context_dependent": {n: {"failures": v, "roots_reaching": {f: sum(1 for r, rr in root_rows.items() if n in rr["context_dependent_reachable"] and fam_of[r] == f) for f in ("modern", "classic")}}
                                 for n, v in ctx.items()},
           "roots": root_rows, "groups": groups,
           "co_blocking_combinations": [{"mechanisms": list(k), "roots": v} for k, v in combos.most_common()],
           "cross_family_conflicts": conflicts, "preflight_recursion_limited": recursion_limited,
           "preflight_contradicted_by_evidence": {n: dict(v, roots_reaching={
               f: sum(1 for r in root_rows if fam_of[r] == f and n in blockers_of(r, contra_mask)) for f in ("modern", "classic")})
               for n, v in contradicted.items()}, "missing_edge_targets": dict(missing),
           "nodes": N, "edges": sum(map(len, adj)), "blocked_nodes": len(blocked), "sccs": c,
           "nontrivial_sccs": [sorted(names[v] for v in m) for m in order if len(m) > 1]}
    (W / "graph.json").write_text(json.dumps(res, sort_keys=True) + "\n")
    print(f"nodes {N}, edges {res['edges']}, blocked {len(blocked)}, sccs {c} ({len(res['nontrivial_sccs'])} nontrivial), "
          f"conflicts {len(conflicts)}, missing targets {len(missing)}")
    print(Counter(r["preflight"] for r in root_rows.values()), Counter(r["known"] for r in root_rows.values()))
    for g in groups[:15]:
        print(g["mechanism"][:90], g["affected_roots"], g["sole_blocker_roots"]["combined"], g["defining_nodes"])


if __name__ == "__main__":
    import threading
    threading.stack_size(1 << 30)           # deep terms: a large C stack for the raised recursion limit
    t = threading.Thread(target=main)
    t.start()
    t.join()

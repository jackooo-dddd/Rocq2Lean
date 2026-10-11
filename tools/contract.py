#!/usr/bin/env python3
"""Coverage contract: what a successful verification must cover, anchored in the source.

Built at export time from the *validated* source IR (after the independent round trip) and the
original request. Neither the translator nor the report is consulted. Fields:

  run_id            fresh identity of this export
  ir_sha256         digest of the exact IR file
  request           the requested root spellings, in order (non-empty, no duplicates)
  roots             [{requested, canonical, kind (constant|inductive)}]; constructor roots and
                    roots resolving to the same canonical declaration are rejected
  exported          every exported declaration
  required_closure  roots plus everything reachable through dependencies recomputed from the
                    terms (types, bodies, contexts, constructors, projections, case/proj metadata)
  extra_exported    exported but not required (classified, never counted as accepted)
  protection        P0: the pinned protected public interface bound to this export (manifest digest,
                    policy, protected declarations present in the export; tools/protection.py)
"""
import hashlib
import json
import sys
import uuid


class ContractError(Exception):
    pass


def term_refs(t, acc):
    if isinstance(t, dict):
        k = t.get("k")
        if k == "const":
            acc.add(t["c"])
        elif k in ("ind", "construct"):
            acc.add(t["ind"]["mind"])
        elif k == "case":
            acc.add(t["ci"]["ind"]["mind"])
        elif k == "proj":
            acc.add(t["p"]["ind"]["mind"])
        for v in t.values():
            term_refs(v, acc)
    elif isinstance(t, list):
        for v in t:
            term_refs(v, acc)
    return acc


def decl_refs(d):
    acc = set()
    if d["kind"] == "constant":
        term_refs([d["type"], d["body"]], acc)
    else:
        term_refs([d["params"], d["bodies"]], acc)
    acc.discard(d["name"])
    return acc


def build(ir_path, request, protection=None):
    if not request:
        raise ContractError("empty root request")
    if len(set(request)) != len(request):
        dups = sorted({r for r in request if request.count(r) > 1})
        raise ContractError(f"duplicate requested roots: {dups}")
    raw = open(ir_path, "rb").read()
    lines = [json.loads(l) for l in raw.decode().splitlines() if l]
    decls = {d["name"]: d for d in lines if d["kind"] in ("constant", "inductive")}
    ir_roots = lines[1]["roots"]
    if [r["requested"] for r in ir_roots] != list(request):
        raise ContractError("exported root records do not match the request (order, spelling or count)")
    roots, seen = [], {}
    for r in ir_roots:
        kind = {"const": "constant", "ind": "inductive"}.get(r["term"]["k"])
        if kind is None:
            raise ContractError(f"root {r['requested']}: unsupported root form '{r['term']['k']}' "
                                f"(request the inductive or a constant, not a constructor)")
        c = r["name"]
        if c not in decls or decls[c]["kind"] != kind:
            raise ContractError(f"root {r['requested']}: resolved identity {c} is not an exported {kind}")
        if c in seen:
            raise ContractError(f"roots {seen[c]} and {r['requested']} resolve to the same declaration {c}")
        seen[c] = r["requested"]
        roots.append({"requested": r["requested"], "canonical": c, "kind": kind})
    closure, todo = set(), [r["canonical"] for r in roots]
    while todo:
        n = todo.pop()
        if n in closure:
            continue
        if n not in decls:
            raise ContractError(f"required declaration {n} is absent from the export")
        closure.add(n)
        todo.extend(decl_refs(decls[n]) - closure)
    out = {
        "schema": "rocq2lean-contract/1",
        "run_id": str(uuid.uuid4()),
        "ir_sha256": hashlib.sha256(raw).hexdigest(),
        "request": list(request),
        "roots": roots,
        "exported": sorted(decls),
        "required_closure": sorted(closure),
        "extra_exported": sorted(set(decls) - closure),
        "protection": protection,
    }
    # statement mode (docs/STATEMENT_ONLY_DESIGN.md): the mode is bound in the contract (proof-mode
    # contracts are unchanged); the closure above is already the statement closure, since the exporter
    # dropped the bodies of proofs
    m = lines[0].get("mode")
    if isinstance(m, dict) and m.get("name") == "statement":
        out["mode"] = "statement"
    return out


if __name__ == "__main__":
    try:
        print(json.dumps(build(sys.argv[1], sys.argv[2].split(",")), indent=2))
    except ContractError as e:
        print(f"CONTRACT_REJECTED: {e}", file=sys.stderr)
        sys.exit(2)

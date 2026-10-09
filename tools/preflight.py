#!/usr/bin/env python3
"""Preflight support classification of an export (no translation).

Classifies each declaration from its actual elaborated terms, never from surface keywords.
CANDIDATE_SUPPORTED means "no known blocker", not a guarantee of success. Kept in sync with
docs/SUPPORT_PROFILE.md.
"""

import json
import sys

# Node kinds the current build translates.
SUPPORTED_NODES = {"rel", "sort", "cast", "prod", "lam", "let", "app", "const", "ind", "construct"}
BOOTSTRAP = {"Corelib.Init.Datatypes.nat", "Corelib.Init.Logic.eq"}


def walk(t, found):
    if isinstance(t, dict):
        k = t.get("k")
        if k == "sort":
            s = t["s"]
            if s["k"] == "sprop":
                found.add("SProp")
            elif s["k"] == "type":
                for e in s["u"]:
                    if e["l"]["k"] == "global":
                        found.add("global universe level")
                    elif e["l"]["k"] == "var":
                        found.add("polymorphic universe level")
            return
        if k is not None and k not in SUPPORTED_NODES:
            found.add(f"node:{k}")
        if k in ("const", "ind", "construct") and t.get("u"):
            found.add("universe instance")
        if isinstance(t, dict) and t.get("r") == "I":
            found.add("SProp-irrelevant binder")
        for v in t.values():
            walk(v, found)
    elif isinstance(t, list):
        for v in t:
            walk(v, found)


def classify(d):
    found = set()
    if d["kind"] == "constant":
        if d["universes"]["k"] != "monomorphic":
            found.add("universe-polymorphic constant")
        if d["body_state"] == "assumption":
            found.add("genuine source assumption")
        if d["body_state"] in ("unavailable", "unsupported_primitive"):
            found.add(f"body state {d['body_state']}")
        walk(d["type"], found)
        walk(d["body"], found)
    else:
        if d["name"] in BOOTSTRAP:
            return "CANDIDATE_SUPPORTED", ["bootstrap registry"]
        found.add("new inductive declaration")
    return ("UNSUPPORTED_FEATURE" if found else "CANDIDATE_SUPPORTED"), sorted(found)


def preflight(ir_path):
    lines = [json.loads(l) for l in open(ir_path)]
    decls = {d["name"]: d for d in lines if d["kind"] in ("constant", "inductive")}
    roots = [r["name"] for r in lines[1]["roots"]]
    status = {n: classify(d) for n, d in decls.items()}

    def deps(n):
        dd = decls[n]["deps"]
        return dd["type"] + dd.get("body", [])

    def blocker_path(n, seen=()):
        if status[n][0] != "CANDIDATE_SUPPORTED":
            return [n]
        for m in deps(n):
            if m in decls and m not in seen:
                p = blocker_path(m, seen + (n,))
                if p:
                    return [n] + p
        return None

    return {
        "roots": {r: ({"status": "CANDIDATE_SUPPORTED"} if not blocker_path(r)
                      else {"status": "UNSUPPORTED_FEATURE", "dependency_path": blocker_path(r),
                            "reasons": status[blocker_path(r)[-1]][1]}) for r in roots},
        "declarations": {n: {"status": s, "reasons": r} for n, (s, r) in status.items()},
    }


if __name__ == "__main__":
    print(json.dumps(preflight(sys.argv[1]), indent=2))

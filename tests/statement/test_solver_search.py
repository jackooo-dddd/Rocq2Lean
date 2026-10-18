#!/usr/bin/env python3
"""Unit controls for tools/solver_search.py (solver stage B reference solver): SAT where a variant can accept,
UNSAT with a certificate where typing forces a conflict, and the allowances of each variant."""
import copy
import json
import os
import sys
import tempfile

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "tools"))
import solver_policy as P  # noqa: E402
import solver_search as SS  # noqa: E402

# native facts: a < b, a ≤ c, c ≤ b; d unrelated
SOURCE = [{"kind": "header"}, {"kind": "roots", "roots": []}, {"kind": "libraries", "libraries": []},
          {"kind": "universes", "levels": [], "constraints": []},
          {"kind": "universe_facts", "levels": ["x.a", "x.b", "x.c", "x.d"],
           "relations": [{"l": "x.a", "rel": "lt", "r": "x.b"}, {"l": "x.a", "rel": "le", "r": "x.c"},
                         {"l": "x.c", "rel": "le", "r": "x.b"}]},
          {"kind": "footer", "declarations": 0}]

# own type level a (?0 free); references at a (?1) and at c (?2); unification made ?1 := ?0
BASE = {"decl": "fixture.ok", "tier": "c[]", "accepted": False,
        "record": {"metavariables": 3, "own": [["x.a", "m:0"]],
                   "occurrences": [["m:1", "x.a", "k.f"], ["m:2", "x.c", "k.f"]],
                   "sites_type": [], "sites_value": [], "assignments": [[1, "m:0"]], "postponed": [],
                   "diagnostics": []}}


def outcome(rec, facts, allow):
    try:
        w = SS.solve(rec, facts, set(allow))
        return "SAT", w
    except SS.Unsat as e:
        return "UNSAT", e.cert
    except SS.Unknown as e:
        return "UNKNOWN", str(e)


def expect(rec, facts, allow, want, label):
    got, info = outcome(rec, facts, allow)
    print(f"{'PASS' if got == want else 'FAIL'} {label}: {got} {str(info)[:160]}")
    return got == want


def main():
    with tempfile.TemporaryDirectory() as d:
        src = os.path.join(d, "source.ndjson")
        with open(src, "w") as fh:
            fh.writelines(json.dumps(x) + "\n" for x in SOURCE)
        ok = True
        ok &= expect(BASE, P.Facts(src), [], "SAT", "free classes: own parameter and an implicit level")
        r = copy.deepcopy(BASE)                       # the occurrence at c is forced to u_a + 1: a + 1 ≤ c not entailed
        r["record"]["assignments"].append([2, "S(m:0)"])
        ok &= expect(r, P.Facts(src), [], "UNSAT", "forced raising at c (a + 1 ≤ c not entailed)")
        r = copy.deepcopy(BASE)                       # forced to u_a + 1 at b: a < b, entailed
        r["record"]["occurrences"][1] = ["m:2", "x.b", "k.f"]
        r["record"]["assignments"].append([2, "S(m:0)"])
        ok &= expect(r, P.Facts(src), [], "SAT", "u_a + 1 at b (a < b)")
        r = copy.deepcopy(BASE)                       # forced to the unrelated own type level d (a rigid parameter)
        r["record"]["own"].append(["x.d", "p:u_x_d"])
        r["record"]["assignments"].append([2, "p:u_x_d"])
        ok &= expect(r, P.Facts(src), [], "UNSAT", "occurrence at c forced to the unrelated own parameter u_d")
        r2 = copy.deepcopy(r)                         # with R3↑ (cu) still unrelated: UNSAT
        ok &= expect(r2, P.Facts(src), ["cu"], "UNSAT", "R3↑ does not relate d and c either")
        r = copy.deepcopy(BASE)                       # occurrence of own a forced to u_c (c ≥ a): coherence
        r["record"]["own"].append(["x.c", "m:3"])
        r["record"]["assignments"] = [[1, "m:3"]]
        ok &= expect(r, P.Facts(src), [], "SAT", "a identified with own c by the solving step (candidate)")
        r = copy.deepcopy(BASE)                       # the occurrence of a forced to 0, with Set < a in the source
        SRC2 = copy.deepcopy(SOURCE)
        SRC2[4]["relations"].append({"l": "Set", "rel": "lt", "r": "x.a"})
        src2 = os.path.join(d, "source2.ndjson")
        with open(src2, "w") as fh:
            fh.writelines(json.dumps(x) + "\n" for x in SRC2)
        r["record"]["assignments"] = [[0, "0"], [1, "0"]]
        ok &= expect(r, P.Facts(src2), [], "UNSAT", "R2B: own a forced to 0 against Set < a")
        ok &= expect(r, P.Facts(src2), ["lo"], "UNSAT", "R3↓ does not lift a forced 0 above Set either")
        print("ALL PASS" if ok else "SOME FAILED")
        return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())

#!/usr/bin/env python3
"""Unit controls for tools/solver_policy.py (solver stage A): R3 coherence and no raising over constraint
records, with forged records that must be refused."""
import copy
import json
import os
import sys
import tempfile

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "tools"))
import solver_check as S  # noqa: E402
import solver_policy as P  # noqa: E402

# native facts: a < b, a ≤ c, c ≤ b; levels a, b, c, d (d unrelated)
SOURCE = [{"kind": "header"}, {"kind": "roots", "roots": []}, {"kind": "libraries", "libraries": []},
          {"kind": "universes", "levels": [], "constraints": []},
          {"kind": "universe_facts", "levels": ["x.a", "x.b", "x.c", "x.d"],
           "relations": [{"l": "x.a", "rel": "lt", "r": "x.b"}, {"l": "x.a", "rel": "le", "r": "x.c"},
                                         {"l": "x.c", "rel": "le", "r": "x.b"}]},
          {"kind": "footer", "declarations": 0}]

# the declaration has level a (?0); it references a constant at a (shared, ?1) and at b (?2)
BASE = {
    "decl": "fixture.ok", "tier": "c[]", "accepted": True,
    "record": {"metavariables": 3, "own": [["x.a", "m:0"]],
               "occurrences": [["m:1", "x.a", "k.f"], ["m:2", "x.b", "k.f"]],
               "sites_type": [["s", "m:0"], ["k.f#0", "m:1"], ["k.f#1", "m:2"]], "sites_value": [],
               "assignments": [], "postponed": [], "diagnostics": []},
    "winner_type": [["s", "p:u_x_a"], ["k.f#0", "p:u_x_a"], ["k.f#1", "S(p:u_x_a)"]],
    "winner_value": [],
}


def results(rec, facts, rows):
    res, why, theta = S.solve_record(rec)
    assert res == "OK", (res, why)
    return [(k, r) for k, r, _ in P.check_policy(rec, theta, facts, rows)]


def expect(rec, facts, rows, want, label):
    got = results(rec, facts, rows)
    ok = want in got and (want[1] in P.VIOLATIONS or not any(r in P.VIOLATIONS for _, r in got))
    print(f"{'PASS' if ok else 'FAIL'} {label}: {got}")
    return ok


def main():
    with tempfile.TemporaryDirectory() as d:
        src = os.path.join(d, "source.ndjson")
        with open(src, "w") as fh:
            fh.writelines(json.dumps(x) + "\n" for x in SOURCE)
        facts = P.Facts(src)
        rows = P.Rows()
        ok = True
        ok &= expect(BASE, facts, rows, ("coherence", "COHERENT"), "shared level at its own parameter")
        ok &= expect(BASE, facts, rows, ("no_raising", "NO_RAISING"), "u_a + 1 at b, with a < b")
        r = copy.deepcopy(BASE)
        r["winner_type"][2] = ["k.f#1", "S(S(p:u_x_a))"]           # a + 2 ≤ b: not entailed
        ok &= expect(r, facts, rows, ("no_raising", "RAISING"), "forged: an argument above the level")
        r = copy.deepcopy(BASE)
        r["record"]["occurrences"][1][1] = "x.d"                  # u_a at d, unrelated
        r["winner_type"][2] = ["k.f#1", "p:u_x_a"]
        ok &= expect(r, facts, rows, ("no_raising", "RAISING"), "forged: an argument at an unrelated level")
        r = copy.deepcopy(BASE)
        r["record"]["own"].append(["x.c", "m:3"])
        r["record"]["sites_type"].append(["s", "m:3"])
        r["winner_type"].append(["s", "p:u_x_c"])
        r["record"]["occurrences"][0] = ["m:1", "x.c", "k.f"]     # shared c given u_a (a ≤ c: lower)
        ok &= expect(r, facts, rows, ("coherence", "EXCEPTION"), "forged: a shared level given another level")
        rows_l = P.Rows()
        rows_l.lowered.add("fixture.ok")
        ok &= expect(r, facts, rows_l, ("coherence", "LOWER"), "the same, on a row reporting R3↓")
        r = copy.deepcopy(BASE)
        r["record"]["occurrences"][1] = ["m:2", "x.a", "k.g"]
        r["record"]["own"] = [["x.c", "m:0"]]
        r["winner_type"] = [["s", "p:u_x_c"], ["k.f#0", "p:u_x_c"], ["k.f#1", "p:u_x_c"]]
        r["record"]["occurrences"][0] = ["m:1", "x.a", "k.f"]     # u_c at a, with a ≤ c: R3↑
        rows_c = P.Rows()
        rows_c.known = True
        ok &= expect(r, facts, rows_c, ("no_raising", "LIFT_UNREPORTED"), "forged: R3↑ on a row not reporting it")
        rows_c.cumul.add("fixture.ok")
        ok &= expect(r, facts, rows_c, ("no_raising", "LIFT"), "R3↑ on a cumulativity-tier row")
        rows_m = P.Rows()
        rows_m.motive.add("x.b")
        r = copy.deepcopy(BASE)
        r["record"]["own"] = [["x.c", "m:0"]]
        r["record"]["occurrences"] = [["m:1", "x.a", "k.f"], ["m:2", "x.b", "k.rect"]]
        r["winner_type"] = [["s", "p:u_x_c"], ["k.f#0", "0"], ["k.f#1", "S(p:u_x_c)"]]
        ok &= expect(r, facts, rows_m, ("no_raising", "R8"), "u_c + 1 at a motive level b, with c ≤ b (R8)")
        ok &= expect(r, facts, P.Rows(), ("no_raising", "RAISING"), "forged: the same at a level that is not a motive level")
        r["record"]["occurrences"][1][1] = "x.a"
        rows_m.motive.add("x.a")
        ok &= expect(r, facts, rows_m, ("no_raising", "RAISING"), "forged: u_c + 1 at a motive level a, c ≤ a not entailed")
    print("ALL PASS" if ok else "FAILURES")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()

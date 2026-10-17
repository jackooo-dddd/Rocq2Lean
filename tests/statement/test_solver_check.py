#!/usr/bin/env python3
"""Unit controls for tools/solver_check.py (solver stage A): accepted and forged constraint records."""
import copy
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "tools"))
import solver_check as S  # noqa: E402

# `@Eq.{?1} (Sort ?0) A A` with `A : Sort (?0)`, an own level ?2 for the type's sort; unification assigned
# ?1 := ?0+1 and postponed max(?3, ?2) = ?2+1 ... (synthetic shapes, one per kind of constraint)
BASE = {
    "decl": "fixture.ok", "tier": "c[]", "accepted": True, "status": "STATEMENT_KERNEL_CHECKED",
    "record": {
        "metavariables": 4,
        "own": [["l", "m:0"]],
        "occurrences": [["m:1", "l"]],
        "sites_type": [["s", "S(m:0)"], ["Eq#0", "m:1"], ["s", "m:0"]],
        "sites_value": [["c#0", "m:3"]],
        "assignments": [[1, "S(m:0)"]],
        "postponed": [["M(m:3,m:0)", "S(m:0)"]],
        "diagnostics": [],
    },
    "winner_type": [["s", "S(p:u_l)"], ["Eq#0", "S(p:u_l)"], ["s", "p:u_l"]],
    "winner_value": [["c#0", "S(p:u_l)"]],
    "winner_params": ["u_l"],
}


def expect(rec, want, label):
    got, why = S.check_record(rec)
    ok = got == want
    print(f"{'PASS' if ok else 'FAIL'} {label}: {got} ({why})")
    return ok


def main():
    ok = True
    ok &= expect(BASE, "OK", "accepted record satisfies its constraints")
    r = copy.deepcopy(BASE)
    r["winner_type"][1] = ["Eq#0", "p:u_l"]                     # Eq at u_l, but typing assigned ?1 := ?0+1
    ok &= expect(r, "VIOLATED", "forged: an assignment the row does not satisfy")
    r = copy.deepcopy(BASE)
    r["winner_value"][0] = ["c#0", "p:u_l"]                     # max(u_l, u_l) = u_l ≠ u_l + 1
    ok &= expect(r, "VIOLATED", "forged: a postponed constraint the row does not satisfy")
    r = copy.deepcopy(BASE)
    r["winner_type"][2] = ["s", "S(p:u_l)"]                     # ?0 read as u_l and as u_l+1
    ok &= expect(r, "VIOLATED", "forged: one metavariable read two ways")
    r = copy.deepcopy(BASE)
    r["winner_value"] = []
    ok &= expect(r, "GAP", "skeleton mismatch")
    r = copy.deepcopy(BASE)
    r["record"]["sites_value"] = [["c#0", "M(m:3,m:2)"]]
    r["record"]["postponed"] = []
    ok &= expect(r, "GAP", "an undetermined metavariable")
    r = copy.deepcopy(BASE)
    r["accepted"] = False
    ok &= expect(r, "NOT_ACCEPTED", "failed declaration")
    # normal form: dominated constants, max/succ distribution
    ok &= S.canon(S.nf(S.parse("M(S(0),p:u)"))) != S.canon(S.nf(S.parse("p:u")))
    ok &= S.canon(S.nf(S.parse("M(0,p:u)"))) == S.canon(S.nf(S.parse("p:u")))
    ok &= S.canon(S.nf(S.parse("S(M(p:u,p:v))"))) == S.canon(S.nf(S.parse("M(S(p:v),S(p:u))")))
    ok &= S.canon(S.nf(S.parse("M(S(0),S(p:u))"))) == S.canon(S.nf(S.parse("S(p:u)")))
    ok &= S.canon(S.nf(S.parse("I(p:u,S(p:v))"))) == S.canon(S.nf(S.parse("M(p:u,S(p:v))")))
    print("normal-form units", "PASS" if ok else "FAIL")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()

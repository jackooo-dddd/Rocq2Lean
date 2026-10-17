#!/usr/bin/env python3
"""Solver stage A (docs/UNIVERSE_SOLVER_PROPOSAL.md): independent check of the shadow-mode constraint
records (`R2L_SHADOW=<file>`, one JSON line per declaration).

For an accepted declaration the record holds the level sites of its term before unification (over level
metavariables), the assignments Lean's unification made, the constraints it postponed, and the accepted row's
level sites in the same traversal order. The check (criterion (a)):

* skeleton: both site sequences have the same keys (sorts and universe-argument positions of constants);
* the accepted row's levels determine each metavariable that occurs bare (`?m + k`) at some site; the
  assignments then determine the others;
* every assignment `?m := v`, every postponed constraint `l = r` and every site holds under that reading,
  as an identity of levels (the normal form `max(c, a₁ + k₁, …)`, valid for all parameter values).

Outcomes per record: OK, VIOLATED (a constraint the accepted row does not satisfy: the extracted system is
stronger than typing — an extraction error — or the row is wrong), GAP (skeleton mismatch, a metavariable not
determined, `imax` not decided), NOT_ACCEPTED (a failed declaration: its system is recorded, nothing to check).
Independent of the translator: it reads only the records. Usage: solver_check.py SHADOW.jsonl [OUT.json]
"""
import json
import sys
from collections import Counter


class Unsupported(Exception):
    pass


def parse(s):
    """`0`, `p:<name>`, `m:<id>`, `S(l)`, `M(a,b)`, `I(a,b)` -> nested tuples."""
    pos = 0

    def go():
        nonlocal pos
        if s.startswith("0", pos):
            pos += 1
            return ("zero",)
        if s.startswith("p:", pos) or s.startswith("m:", pos):
            k = s[pos]
            pos += 2
            j = pos
            while pos < len(s) and s[pos] not in ",)":
                pos += 1
            return ("param", s[j:pos]) if k == "p" else ("mvar", int(s[j:pos]))
        head = s[pos]
        if head not in "SMI" or s[pos + 1] != "(":
            raise ValueError(f"bad level {s!r} at {pos}")
        pos += 2
        a = go()
        if head == "S":
            assert s[pos] == ")"
            pos += 1
            return ("succ", a)
        assert s[pos] == ","
        pos += 1
        b = go()
        assert s[pos] == ")"
        pos += 1
        return ("max" if head == "M" else "imax", a, b)

    t = go()
    if pos != len(s):
        raise ValueError(f"trailing input in {s!r}")
    return t


def nf(t):
    """Normal form (c, {atom: k}) of a level without imax: max(c, atom + k ...); c dropped when dominated."""
    if t[0] == "zero":
        return (0, {})
    if t[0] in ("param", "mvar"):
        return (0, {t: 0})
    if t[0] == "succ":
        c, m = nf(t[1])
        return (c + 1, {a: k + 1 for a, k in m.items()})
    if t[0] == "max":
        c1, m1 = nf(t[1])
        c2, m2 = nf(t[2])
        m = dict(m1)
        for a, k in m2.items():
            m[a] = max(m.get(a, k), k)
        return (max(c1, c2), m)
    if t[0] == "imax":
        cb, mb = nf(t[2])
        if cb >= 1 or any(k >= 1 for k in mb.values()):     # never zero: imax a b = max a b
            return nf(("max", t[1], t[2]))
        if not mb and cb == 0:                               # b = 0: imax a 0 = 0
            return (0, {})
        raise Unsupported("imax with a possibly-zero right side")
    raise ValueError(t)


def canon(n):
    c, m = n
    if m and c <= max(m.values()):
        c = 0
    return (c, tuple(sorted(m.items(), key=repr)))


def subst(t, theta):
    if t[0] == "mvar":
        if t[1] not in theta:
            raise KeyError(t[1])
        return theta[t[1]]
    if t[0] in ("zero", "param"):
        return t
    return (t[0],) + tuple(subst(x, theta) for x in t[1:])


def shift_down(n, k):
    """n - k as a level, when n ≥ k + every summand (n = (c, m) with all offsets ≥ k, and c ≥ k or dominated)."""
    c, m = n
    if m and c <= max(m.values()):
        c = 0                                   # dominated constant
    if any(v < k for v in m.values()):
        return None
    if c and c < k:
        return None
    if not m and c < k:
        return None
    return (c - k if c else 0, {a: v - k for a, v in m.items()})


def from_nf(n):
    c, m = n
    parts = []
    if c or not m:
        t = ("zero",)
        for _ in range(c):
            t = ("succ", t)
        parts.append(t)
    for a, k in sorted(m.items(), key=repr):
        t = a
        for _ in range(k):
            t = ("succ", t)
        parts.append(t)
    t = parts[0]
    for p in parts[1:]:
        t = ("max", t, p)
    return t


def bare(t):
    """`?m + k` -> (m, k), else None."""
    k = 0
    while t[0] == "succ":
        t, k = t[1], k + 1
    return (t[1], k) if t[0] == "mvar" else None


def check_record(rec):
    res, why, _ = solve_record(rec)
    return res, why


def solve_record(rec):
    """check_record, also returning the reading `theta` (metavariable -> level) the accepted row determines."""
    if not rec.get("accepted"):
        return "NOT_ACCEPTED", None, None
    r = rec.get("record")
    if r is None:
        return "GAP", f"no constraint record ({rec.get('error') or 'shadow attempt returned early'})", None
    st = r["sites_type"] + r["sites_value"]
    wt = (rec.get("winner_type") or []) + (rec.get("winner_value") or [])
    if [k for k, _ in st] != [k for k, _ in wt]:
        return "GAP", f"skeleton: {len(st)} shadow sites vs {len(wt)} accepted sites", None
    try:
        pairs = [(parse(a), parse(b)) for (_, a), (_, b) in zip(st, wt)]
        asg = [(int(k), parse(v)) for k, v in r["assignments"]]
        post = [(parse(a), parse(b)) for a, b in r["postponed"]]
    except ValueError as e:
        return "GAP", f"parse: {e}", None
    theta = {}
    try:
        # 1. bare sites determine their metavariables
        for s, w in pairs:
            b = bare(s)
            if b is None:
                continue
            m, k = b
            v = shift_down(nf(w), k)
            if v is None:
                return "VIOLATED", f"site ?{m}+{k} has accepted level {w} below its offset", None
            v = from_nf(v)
            if m in theta and canon(nf(theta[m])) != canon(nf(v)):
                return "VIOLATED", f"?{m} read as {theta[m]} and as {v} at two sites", None
            theta.setdefault(m, v)
        # 2. assignments determine the others (to a fixed point)
        changed = True
        while changed:
            changed = False
            for m, v in asg:
                if m in theta:
                    continue
                try:
                    theta[m] = from_nf(nf(subst(v, theta)))
                    changed = True
                except KeyError:
                    pass
        # 3. every constraint holds as an identity
        for m, v in asg:
            if m not in theta:
                return "GAP", f"?{m} not determined", None
            if canon(nf(theta[m])) != canon(nf(subst(v, theta))):
                return "VIOLATED", f"assignment ?{m} := {v}: {theta[m]} vs {subst(v, theta)}", None
        for s, w in pairs:
            if canon(nf(subst(s, theta))) != canon(nf(w)):
                return "VIOLATED", f"site {s} -> {subst(s, theta)} vs accepted {w}", None
        for a, b in post:
            if canon(nf(subst(a, theta))) != canon(nf(subst(b, theta))):
                return "VIOLATED", f"postponed {a} = {b}", None
    except KeyError as e:
        return "GAP", f"?{e.args[0]} not determined", None
    except Unsupported as e:
        return "GAP", str(e), None
    return "OK", None, theta


def main():
    recs = [json.loads(l) for l in open(sys.argv[1]) if l.strip()]
    out, cnt, ex = [], Counter(), {}
    for rec in recs:
        res, why = check_record(rec)
        cnt[res] += 1
        if why and res not in ex:
            ex[res] = (rec["decl"], why)
        r = rec.get("record") or {}
        out.append({"decl": rec["decl"], "tier": rec.get("tier"), "result": res, "why": why,
                    "metavariables": r.get("metavariables"), "assignments": len(r.get("assignments", [])),
                    "postponed": len(r.get("postponed", [])), "diagnostics": r.get("diagnostics", []),
                    "shadow_ms": rec.get("shadow_ms")})
    summary = {"schema": "rocq2lean-solver-stage-a-check/1", "records": len(recs), "results": dict(cnt),
               "examples": {k: {"decl": d, "why": w} for k, (d, w) in ex.items()}}
    print(json.dumps(summary, indent=1))
    if len(sys.argv) > 2:
        json.dump({"summary": summary, "rows": out}, open(sys.argv[2], "w"), indent=1)
    sys.exit(0 if cnt["VIOLATED"] == 0 else 1)


if __name__ == "__main__":
    main()

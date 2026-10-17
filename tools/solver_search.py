#!/usr/bin/env python3
"""Solver stage B, reference solver (docs/UNIVERSE_SOLVER_PROPOSAL.md §4-5): on a stage-A shadow record, decide
whether some level assignment satisfies the extracted system under the policy of a *group* of universe-only
variants (the tiers that share the record's term and differ only in `it`, `cu`, `lo`, `un`, `jo`), and give a
certificate when none does.

The record (`R2L_SHADOW`) is the attempt with a fresh level metavariable at every reference (the `unify` path),
stopped after Lean's checker and unification: the most general term of the group (the other variants share own
levels at references from the start, a specialization of it). The encoding over-approximates what any variant
of the group can accept, so that UNSAT is sound for skipping the group:

* typing: every assignment `?m := v` and postponed constraint `a = b` (identities of levels);
* own levels: each own level whose metavariable unification left free is its parameter `u_l` (a type level),
  its minimal model (a body level, R2B), another own level's parameter (identified by the solving step), or,
  with `it`, its R2F reading `ι l` (`max(u_l, ι m + k)` over own `m ≤ l`);
* R3 coherence: an occurrence of an own level takes the own level's value; with rule R (all variants), any
  value equal to it at every model of the source facts; with `lo` (R3↓) any value that does not raise;
* R3 no raising: an occurrence of another level `l` takes `max(c, u_m + k, …)` with `Set + c ≤ l` and `m + k ≤ l`
  entailed; with `cu` (R3↑) also `u_m` where `l ≤ m`; at a motive level of some accepted constant (the report's
  `admitting_levels`) also `u_m + 1` with `m ≤ l` (R8);
* implicit levels (R3G): a class of occurrences unification left free is a new parameter standing for one
  of the source levels it occurs bare at (any of them), or a residual default `0` (R3′);
* R2S/R2B: every native fact among the own levels holds for their values (`summandsLeq`), with `cu` reading
  `Set < m` as `Set ≤ m` (R2B-P).

Not modelled (each only *removes* acceptances, so leaving it out keeps UNSAT sound): generality and interface
checks, kernel acceptance, R3′ justification, R-CARRIER and copy bookkeeping beyond the copies' source level.

Outcomes: SAT (a witness: a value for each unknown; checked against every constraint), UNSAT (certificate: the
constraint that no candidate combination satisfies, with the candidates tried), UNKNOWN (unsupported level forms,
search limit). Usage: solver_search.py SHADOW.jsonl SOURCE.ndjson [translation_timing.json] [translation_report.json] [OUT.json]
With TIMING (a run's `translation_timing.json`), each record's group is the variants that run tried with the
record's term flags, and the report checks soundness (no accepted record UNSAT) and the time a skip would save.
"""
import json
import re
import sys
from collections import Counter, defaultdict

sys.path.insert(0, sys.argv[0].rsplit("/", 1)[0])
import solver_check as S
import solver_policy as P

UNI = {"it", "cu", "lo", "un", "jo"}
OK = {"TRANSLATED_AND_CHECKED", "STATEMENT_KERNEL_CHECKED", "BOOTSTRAP_RESOLVED", "PENDING_KERNEL_CHECKED",
      "STATEMENT_PENDING_KERNEL_CHECKED"}
LIMIT = 200000


class Unknown(Exception):
    pass


class Unsat(Exception):
    def __init__(self, why, cert):
        super().__init__(why)
        self.why, self.cert = why, cert


def parse_label(lab):
    m = re.match(r"(\w)\[([^\]]*)\](?: eo(\d+))?", lab or "")
    if not m:
        return None
    fl = {f for f in m.group(2).split(",") if f}
    return m.group(1), frozenset(fl - UNI), m.group(3) or "0", frozenset(fl & UNI)


# ---- levels as normal forms (c, {atom: k}); atoms ("param", name) or ("mvar", id) --------------------------
def norm(n):
    c, m = n
    if m and c <= max(m.values()):
        c = 0
    return (c, tuple(sorted(m.items(), key=repr)))


def nmax(a, b):
    c = max(a[0], b[0])
    m = dict(a[1])
    for x, k in b[1].items():
        m[x] = max(m.get(x, k), k)
    return (c, m)


def nsub(n, val):
    """Replace unknown atoms by their values (normal forms over parameters)."""
    c, m = n
    out = (c, {})
    for a, k in m.items():
        if a[0] == "mvar" and a[1] in val:
            vc, vm = val[a[1]]
            out = nmax(out, (vc + k, {b: j + k for b, j in vm.items()}))
        else:
            out = nmax(out, (0, {a: k}))
    return out


def unknowns_of(n):
    return {a[1] for a in n[1] if a[0] == "mvar"}


def show(n):
    return P.show(norm(n))


class Policy:
    def __init__(self, facts, allow, motive=None):
        self.f, self.cu, self.lo, self.it = facts, "cu" in allow, "lo" in allow, "it" in allow
        self.motive = motive                       # target constant -> its motive levels (R8)
        self.motive_all = set().union(*motive.values()) if motive else set()

    def src(self, p):
        s = self.f.source_of(p)
        if s is None:
            raise Unknown(f"foreign parameter {p}")
        return s

    def raise_ok(self, l, n, const=None):
        """No raising of the value `n` (over parameters) at source level `l` (of the referenced `const`)."""
        c, m = norm(n)
        if c and not self.f.entails("Set", l, c):
            return False
        for a, k in m:
            s = self.src(a[1])
            if self.f.entails(s, l, k):
                continue
            if self.cu and k == 0 and self.f.entails(l, s, 0):
                continue                                  # R3↑
            mot = self.motive.get(const) if const not in (None, "?") else None
            if k >= 1 and (l in mot if mot is not None else const == "?" and l in self.motive_all) and \
                    self.f.entails(s, l, k - 1):
                continue                                  # R8 (motive level: u_m + 1 for m ≤ l)
            return False
        return True

    def summ(self, n):
        c, m = norm(n)
        return [("Set", c)] + [(self.src(a[1]), k) for a, k in m]

    def leq(self, lhs, rhs, k):
        f = self.f
        for a, i in lhs:
            if a == "Set" and i + k == 0:
                continue
            if not any(((i + k <= j) and (f.entails(a, b, 0) or a == "Set")) or
                       ((i + k > j) and f.entails(a, b, i + k - j)) for b, j in rhs):
                return False
        return True

    def equal_at_models(self, x, y):
        return self.leq(self.summ(x), self.summ(y), 0) and self.leq(self.summ(y), self.summ(x), 0)

    def coherent(self, l, occ, own):
        if norm(occ) == norm(own):
            return True
        if self.equal_at_models(occ, own):                # rule R
            return True
        return self.lo and self.raise_ok(l, occ)          # R3↓


def readings(facts, own_src, params):
    """R2F readings ι l = max(u_l, ι m + k) over own m ≤ l (k = 1 for <), mutually ≤ levels by parameter."""
    def go(l, seen):
        acc = (0, {("param", params[l]): 0})
        for m in own_src:
            if m == l or m in seen:
                continue
            r = facts.rel(m, l)
            if r not in ("le", "lt"):
                continue
            k = 1 if r == "lt" else 0
            if facts.rel(l, m) in ("le", "lt"):
                acc = nmax(acc, (0, {("param", params[m]): k}))
            else:
                v = go(m, seen | {l})
                acc = nmax(acc, (v[0] + k, {a: j + k for a, j in v[1].items()}))
        return acc
    return {l: go(l, frozenset()) for l in own_src}


def solve(rec, facts, allow, motive=None):
    r = rec["record"]
    pol = Policy(facts, allow, motive or {})
    asg = {int(k): S.parse(v) for k, v in r["assignments"]}
    memo = {}

    def term_nf(t, depth=0):
        if depth > 600:
            raise Unknown("assignment chain too deep")
        if t[0] == "mvar":
            m = t[1]
            if m not in asg:
                return (0, {("mvar", m): 0})
            if m in memo:
                if memo[m] is None:
                    raise Unknown("cyclic assignment")
                return memo[m]
            memo[m] = None
            memo[m] = term_nf(asg[m], depth + 1)
            return memo[m]
        if t[0] == "zero":
            return (0, {})
        if t[0] == "param":
            return (0, {t: 0})
        if t[0] == "succ":
            c, m = term_nf(t[1], depth + 1)
            return (c + 1, {a: k + 1 for a, k in m.items()})
        if t[0] == "max":
            return nmax(term_nf(t[1], depth + 1), term_nf(t[2], depth + 1))
        if t[0] == "imax":
            b = term_nf(t[2], depth + 1)
            if b[0] >= 1 or any(k >= 1 for k in b[1].values()):
                return nmax(term_nf(t[1], depth + 1), b)
            if not b[1] and b[0] == 0:
                return (0, {})
            raise Unknown("imax with a possibly-zero right side")
        raise Unknown(f"level form {t[0]}")

    # own levels
    own = {}                                   # source level -> nf of its own metavariable / parameter
    for src, v in r["own"]:
        own.setdefault(src, term_nf(S.parse(v)))
    params = {l: "u_" + l.replace(".", "_") for l in own}
    for l, p in params.items():
        facts.param.setdefault(p, l.split("__c")[0] if l not in facts.param.values() else l)
    # constraints: (kind, data, why)
    cons = []
    for a, b in r["postponed"]:
        cons.append(("eq", (term_nf(S.parse(a)), term_nf(S.parse(b))), "postponed"))
    bare = defaultdict(set)                    # unknown -> source levels it stands for bare (implicit levels)
    occ_nf = []
    for occ in r["occurrences"]:
        v, src = occ[0], occ[1]
        const = occ[2] if len(occ) > 2 else "?"
        n = term_nf(S.parse(v))
        occ_nf.append(n)
        why = f"occurrence of {src} at {const}"
        if src in own:
            cons.append(("coh", (src, n, own[src]), why))
        else:
            cons.append(("nr", (src, n, const), why))
        u = unknowns_of(n)
        if len(u) == 1 and n[0] == 0 and list(n[1].values()) == [0]:
            bare[next(iter(u))].add(src)
    srcs = [l for l in own]
    for (a, b), rel in facts.index.items():
        if (a in own or b in own) and (a in own or a == "Set") and (b in own or b == "Set"):
            cons.append(("fact", (a, rel, b), f"native fact {a} {rel} {b}"))
    # candidates
    own_unknown = {}
    for l, n in own.items():
        u = unknowns_of(n)
        if len(u) == 1 and n == (0, {("mvar", next(iter(u))): 0}):
            own_unknown[next(iter(u))] = l
    rd = readings(facts, srcs, params) if pol.it else {}
    mm = {}
    for l in own:
        lo = (0, {})
        for (a, b), rel in facts.index.items():
            if b != l:
                continue
            k = 1 if rel == "lt" else 0
            if a == "Set":
                lo = nmax(lo, (k, {}))
            elif a in own:
                lo = nmax(lo, (0, {("param", params[a]): k}))
        mm[l] = lo
    unk = set()
    for kind, data, _ in cons:
        for x in data:
            if isinstance(x, tuple) and len(x) == 2 and isinstance(x[1], dict):
                unk |= unknowns_of(x)
    unk_base = set(unk)
    for n in own.values():
        unk |= unknowns_of(n)
    cand = {}
    for m in unk:
        if m in own_unknown:
            l = own_unknown[m]
            # its parameter, its minimal model, its reading, or identified with another own level
            cs = [(0, {("param", params[l]): 0}), mm[l]] + ([rd[l]] if l in rd else [])
            cs += [(0, {("param", params[o]): 0}) for o in sorted(own) if o != l]
        else:
            cs = [(0, {("param", params[s] if s in params else "u_" + s.replace(".", "_")): 0}) for s in sorted(bare.get(m, ()))]
            for s in bare.get(m, ()):
                facts.param.setdefault("u_" + s.replace(".", "_"), s)
            cs.append((0, {}))
        seen, uniq = set(), []
        for c in cs:
            if norm(c) not in seen:
                seen.add(norm(c))
                uniq.append(c)
        cand[m] = uniq

    # R3G: a level chosen as an implicit level is an own level of the attempt from then on, so every occurrence of
    # it is a coherence occurrence (argument `u_r`, or a lowered one with R3↓)
    occ_by_src = defaultdict(list)
    for kind, data, _ in cons:
        if kind == "nr":
            occ_by_src[data[0]].append(data[1])
    holders = defaultdict(set)
    for m, cs in cand.items():
        for c in cs:
            for a in c[1]:
                if a[0] == "param" and a[1] not in params.values():
                    holders[a[1]].add(m)
    for p_, ms in holders.items():
        r_ = facts.source_of(p_)
        if r_ is None or not occ_by_src.get(r_):
            continue
        cons.append(("imp", (r_, p_, frozenset(ms), occ_by_src[r_]), f"implicit level {r_}: its occurrences"))

    def check(kind, data, val):
        if kind == "imp":
            r_, p_, ms, occs = data
            if not any(("param", p_) in val[m][1] for m in ms if m in val):
                return True
            u = (0, {("param", p_): 0})
            return all(pol.coherent(r_, nsub(n, val), u) for n in occs)
        if kind == "eq":
            return norm(nsub(data[0], val)) == norm(nsub(data[1], val))
        if kind == "coh":
            l, n, o = data
            return pol.coherent(l, nsub(n, val), nsub(o, val))
        if kind == "nr":
            l, n, const = data
            return pol.raise_ok(l, nsub(n, val), const)
        if kind == "fact":
            a, rel, b = data
            k = 1 if rel == "lt" and not (pol.cu and a == "Set") else 0
            lhs = [("Set", 0)] if a == "Set" else pol.summ(nsub(own[a], val))
            rhs = [("Set", 0)] if b == "Set" else pol.summ(nsub(own[b], val))
            return pol.leq(lhs, rhs, k)
        raise ValueError(kind)

    def deps(kind, data):
        out = set()
        if kind == "imp":
            out = set(data[2])
            for n in data[3]:
                out |= unknowns_of(n)
            return out
        if kind == "eq":
            out = unknowns_of(data[0]) | unknowns_of(data[1])
        elif kind == "coh":
            out = unknowns_of(data[1]) | unknowns_of(data[2])
        elif kind == "nr":
            out = unknowns_of(data[1])
        elif kind == "fact":
            for x in (data[0], data[2]):
                if x != "Set":
                    out |= unknowns_of(own[x])
        return out

    cdeps = [(k, d, w, deps(k, d)) for k, d, w in cons]
    # constraints with no unknowns are decided now
    for k, d, w, ds in cdeps:
        if not ds and not check(k, d, {}):
            raise Unsat(f"{w}: fails with every assignment (no free level involved)", [w])
    # unknowns that occur in no constraint: any candidate
    involved = set().union(*[ds for *_, ds in cdeps]) if cdeps else set()
    val = {m: cand[m][0] for m in unk - involved}
    order = sorted(involved, key=lambda m: (len(cand[m]), m))
    by_last = defaultdict(list)                # constraints checked when their last unknown is assigned
    pos = {m: i for i, m in enumerate(order)}
    for k, d, w, ds in cdeps:
        if ds:
            by_last[max(ds, key=lambda x: pos[x])].append((k, d, w))
    steps = 0
    fail_at = Counter()

    def bt(i):
        nonlocal steps
        if i == len(order):
            return True
        m = order[i]
        for c in cand[m]:
            steps += 1
            if steps > LIMIT:
                raise Unknown("search limit")
            val[m] = c
            bad = next(((k, d, w) for k, d, w in by_last[m] if not check(k, d, val)), None)
            if bad is None and bt(i + 1):
                return True
            if bad is not None:
                fail_at[bad[2]] += 1
            del val[m]
        return False

    sys.setrecursionlimit(10000)
    if not bt(0):
        worst = [w for w, _ in fail_at.most_common(3)]
        raise Unsat("no candidate combination satisfies the system", worst)
    # the witness, over the own levels (`o:<level>`; an implicit level becomes an extra own level)
    inv = {p: l for l, p in params.items()}
    implicit = set()

    def fmt(n):
        c, m = norm(n)
        parts = []
        if c or not m:
            t = "0"
            for _ in range(c):
                t = f"S({t})"
            parts.append(t)
        for a, k in m:
            if a[0] != "param":
                raise Unknown("unknown left in the witness")
            l = inv.get(a[1])
            if l is None:
                l = facts.source_of(a[1])
                if l is None:
                    raise Unknown(f"witness parameter {a[1]}")
                implicit.add(l)
            t = f"o:{l}"
            for _ in range(k):
                t = f"S({t})"
            parts.append(t)
        out = parts[0]
        for q in parts[1:]:
            out = f"M({out},{q})"
        return out
    witness = {"occ": [fmt(nsub(n, val)) for n in occ_nf], "own": {l: fmt(nsub(n, val)) for l, n in own.items()}}
    witness["extra_own"] = sorted(implicit - set(own))
    return {"own": {l: show(nsub(n, val)) for l, n in own.items()}, "unknowns": len(unk), "steps": steps,
            "witness": witness}


def main():
    shadow, source = sys.argv[1], sys.argv[2]
    timing = next((a for a in sys.argv[3:] if a.endswith("timing.json")), None)
    report = next((a for a in sys.argv[3:] if a.endswith("translation_report.json")), None)
    out_path = next((a for a in sys.argv[3:] if a.endswith(".json") and a not in (timing, report)), None)
    motive = {}
    for row in (P.report_rows(report) if report else []):
        for t in (row.get("target"), row.get("source")):
            if t:
                motive[t] = set(row.get("admitting_levels") or [])
    facts = P.Facts(source)
    tiers = {}
    if timing:
        for x in json.load(open(timing))["declarations"]:
            tiers[x["source"]] = (x["status"], x.get("tier_times") or [])
    out, cnt, ex, save = {}, Counter(), {}, Counter()
    for line in open(shadow):
        if not line.strip():
            continue
        rec = json.loads(line)
        if not rec.get("record"):
            continue
        n = rec["decl"]
        lab = parse_label(rec.get("tier"))
        allow, group = set(lab[3]) if lab else set(), []
        st, tt = tiers.get(n, (None, []))
        if lab:
            for i, (l2, ms, s2) in enumerate(tt):
                p2 = parse_label(l2)
                if p2 and p2[:3] == lab[:3]:
                    group.append((i, ms, s2.split(" |")[0]))
                    allow |= p2[3]
        try:
            w = solve(rec, facts, allow, motive)
            res = dict(w, result="SAT")
            # the earliest allowance set (in ladder order) that has a solution: the variant to run
            for flags in ([], ["it"], ["cu"], ["cu", "lo"], ["it", "cu"], ["it", "cu", "lo"]):
                if not set(flags) <= allow:
                    continue
                try:
                    w2 = solve(rec, facts, set(flags), motive)
                    res.update(w2, flags=flags)
                    break
                except (Unsat, Unknown):
                    continue
            res.setdefault("flags", sorted(allow & {"it", "cu", "lo"}))
        except Unsat as e:
            res = {"result": "UNSAT", "why": e.why, "certificate": e.cert}
        except Unknown as e:
            res = {"result": "UNKNOWN", "why": str(e)}
        res.update(accepted=bool(rec.get("accepted")), tier=rec.get("tier"), allow=sorted(allow))
        g_ok = any(s in OK for _, _, s in group)
        res["group_succeeded"] = g_ok
        # the group's attempts the late-tier budget aborted that allow the witness's flags (full-budget retry)
        if res["result"] == "SAT" and not res["accepted"]:
            want = frozenset(res.get("flags", []))
            res["retry"] = [tt[i][0] for i, _, s2 in group
                            if s2 == "RESOURCE_LIMIT" and parse_label(tt[i][0])[3] >= want]
        out[n] = res
        key = (res["result"], "accepted" if res["accepted"] else "failed")
        cnt[key] += 1
        ex.setdefault(key, (n[-70:], res.get("why") or res.get("own")))
        if res["result"] == "UNSAT":
            if g_ok or res["accepted"]:
                cnt[("UNSOUND", "group had a success")] += 1
                ex.setdefault(("UNSOUND", "group had a success"), (n, res["why"], res.get("certificate")))
            else:
                save["skippable_ms"] += sum(ms for _, ms, _ in group[1:])
                save["group_attempts"] += max(len(group) - 1, 0)
    for k, v in sorted(cnt.items(), key=str):
        print(v, k, "e.g.", str(ex.get(k))[:400])
    if timing:
        print("skip on UNSAT (attempts after the group's first):", dict(save))
    if out_path:
        json.dump(out, open(out_path, "w"), indent=1, ensure_ascii=False)
        with open(out_path.rsplit(".", 1)[0] + ".retry.tsv", "w") as fh:
            for n, res in out.items():
                for lab in res.get("retry", []):
                    fh.write(f"{n}\t{lab}\n")
        # witnesses of failed declarations, for the translator's witness attempt (`R2L_WITNESS`)
        with open(out_path.rsplit(".", 1)[0] + ".witness.jsonl", "w") as fh:
            for n, res in out.items():
                if res["result"] == "SAT" and not res["accepted"]:
                    fh.write(json.dumps(dict(res["witness"], decl=n, tier=res["tier"], flags=res["flags"])) + "\n")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Solver stage A: policy constraints over the shadow variables, checked against the accepted rows.

Constraint R3 (coherence): an occurrence of a source level the referring declaration also has (a *shared*
level) takes the referring declaration's own level for it. From each record (`R2L_SHADOW`), the reading the
accepted row determines (`solver_check.solve_record`) gives the value of every own level and every reference
argument; each shared occurrence is classified:

* COHERENT: the occurrence's value is the own level's value (identity of levels);
* LOWER: it differs, is not raising (as below), and the row reports a lowering (`universe_lowered`: R3↓);
* EXCEPTION: it differs otherwise; listed by the constant it occurs in and the shape of the two values, so that each
  exception can be matched with a translator rule (rule R, rule H, R-CARRIER copies, R2F readings, …);
* UNDETERMINED: the occurrence's metavariable is not determined by the row (it occurs at no site).

Constraint R3 (no raising), with the source (`SOURCE.ndjson`, its native facts): an occurrence of a level `l`
the referring declaration does not have takes a value `max(c, u_m + k, …)` with `Set + c ≤ l` and `m + k ≤ l`
entailed by the native facts (`k = 0`: `≤`, `k = 1`: `<`, more: a chain of strict steps). Classified:

* NO_RAISING: entailed;
* LIFT: not entailed, but `l ≤ m` with offset 0 (R3↑, cumulativity tier, reported per declaration);
* RAISING: neither (with offset 1 at a parameter possibly an R8 motive-level parameter, `u_m + 1`);
* FOREIGN: a summand that is not the image of a source level (R3′ residuals, copies' bookkeeping).

With the translation report (`translation_report.json`), exceptions are matched with what the rows report:
LIFT only on a row with `universe_cumulativity` (else LIFT_UNREPORTED); RAISING by one at a level that is an R8
motive level of some accepted constant (`admitting_levels`), with `m + k - 1 ≤ l` entailed, is R8.

Usage: solver_policy.py SHADOW.jsonl [SOURCE.ndjson] [translation_report.json] [OUT.json]"""
import json
import sys
from collections import Counter, defaultdict

sys.path.insert(0, sys.argv[0].rsplit("/", 1)[0])
import solver_check as S


def value(t, theta):
    return S.canon(S.nf(S.subst(t, theta)))


def show(c):
    k, m = c
    parts = ([str(k)] if k or not m else []) + [f"{a[1] if a[0] == 'param' else '?' + str(a[1])}{'+' + str(o) if o else ''}" for a, o in m]
    return parts[0] if len(parts) == 1 else "max(" + ", ".join(parts) + ")"


def shape(own, occ):
    """How an incoherent occurrence differs from the own level."""
    (ko, mo), (kc, mc) = own, occ
    po = {a[1] for a, _ in mo if a[0] == "param"}
    pc = {a[1] for a, _ in mc if a[0] == "param"}
    if not mc:
        return "constant"
    if len(mc) > 1:
        return "max" if po <= pc else "max-other"
    (a, o), = mc
    if a[0] == "param" and any(p.split("__c")[0] == a[1].split("__c")[0] for p in po):
        return "copy" if o == 0 else "copy+offset"
    if po and a[0] == "param" and a[1] in po:
        return "offset"
    return "other-level"


def report_rows(path):
    """Rows of a translation report: streamed (one row per line) or a single JSON document."""
    with open(path) as fh:
        if not fh.readline().startswith('{"report"'):
            yield from json.load(open(path))["results"]
            return
        for line in fh:
            line = line.strip().rstrip(",")
            if not line.startswith('{"'):                  # a head field (`"key": value`) or the closing `]}`
                continue
            try:
                yield json.loads(line)
            except json.JSONDecodeError:                   # the last row, followed by the closing `]}`
                yield json.loads(line[:-2])


class Facts:
    def __init__(self, source):
        self.index, self.lt_succ, self.param = {}, defaultdict(list), {}
        with open(source) as fh:
            for i, line in enumerate(fh):
                if i > 6:
                    break
                d = json.loads(line)
                if d.get("kind") != "universe_facts":
                    continue
                for x in d["relations"]:
                    self.index[(x["l"], x["r"])] = x["rel"]
                    if x["rel"] == "lt":
                        self.lt_succ[x["l"]].append(x["r"])
                for n in d["levels"]:
                    self.param["u_" + n.replace(".", "_")] = n

    def rel(self, a, b):
        return "eq" if a == b else self.index.get((a, b), "none")

    def entails(self, a, b, k):
        """`a + k ≤ b` (as the translator's `entails`)."""
        if k == 0:
            return a == b or a == "Set" or self.rel(a, b) in ("le", "lt")
        if k == 1:
            return self.rel(a, b) == "lt" or (a == "Set" and self.rel(a, b) == "lt")
        return any(self.entails(c, b, k - 1) for c in self.lt_succ.get(a, []))

    def source_of(self, p):
        base = p.split("__c")[0]
        return self.param.get(base)


def no_raising(facts, l, v, motive=frozenset()):
    c, m = v
    if c and not facts.entails("Set", l, c):
        return "RAISING", f"Set + {c} ≤ {l}"
    worst = "NO_RAISING"
    for a, k in m:
        if a[0] != "param":
            return "UNDETERMINED", None
        src = facts.source_of(a[1])
        if src is None:
            return "FOREIGN", a[1]
        if facts.entails(src, l, k):
            continue
        if k == 0 and facts.entails(l, src, 0):
            worst = "LIFT"
            continue
        if k >= 1 and l in motive and facts.entails(src, l, k - 1):
            worst = "R8" if worst == "NO_RAISING" else worst
            continue
        return "RAISING", f"{src} + {k} ≤ {l}"
    return worst, None


class Rows:
    """What the report says per row (R8 motive levels, cumulativity tier, lowering)."""
    def __init__(self, report=None):
        self.motive, self.cumul, self.lowered, self.known = set(), set(), set(), report is not None
        for row in (report_rows(report) if report else []):
            self.motive.update(row.get("admitting_levels") or [])
            if row.get("universe_cumulativity"):
                self.cumul.add(row["source"])
            if row.get("universe_lowered"):
                self.lowered.add(row["source"])


VIOLATIONS = {"EXCEPTION", "RAISING", "LIFT_UNREPORTED"}


def check_policy(rec, theta, facts, rows):
    """(constraint, result, details) for every occurrence of an accepted record."""
    r = rec["record"]
    own, out = {}, []
    for src, v in r["own"]:
        try:
            own.setdefault(src, []).append(value(S.parse(v), theta))
        except KeyError:
            out.append(("own", "UNDETERMINED", {"level": src}))
    for occ in r["occurrences"]:
        v, src = occ[0], occ[1]
        const = occ[2] if len(occ) > 2 else "?"
        where = "statement" if const.endswith(".statement") else ("?" if const == "?" else "constant")
        try:
            ov = value(S.parse(v), theta)
        except KeyError:
            out.append(("coherence" if own.get(src) else "no_raising", "UNDETERMINED", {"level": src}))
            continue
        d = {"decl": rec["decl"], "constant": const, "where": where, "level": src, "argument": show(ov)}
        if not own.get(src):
            if facts is None:
                continue
            res, why = no_raising(facts, src, ov, rows.motive)
            if res == "LIFT" and rows.known and rec["decl"] not in rows.cumul:
                res = "LIFT_UNREPORTED"
            out.append(("no_raising", res, dict(d, why=why)))
            continue
        if ov in own[src] or ov == (0, ((("param", "u_" + src.replace(".", "_")), 0),)):
            out.append(("coherence", "COHERENT", d))
        elif facts and rec["decl"] in rows.lowered and no_raising(facts, src, ov, rows.motive)[0] in ("NO_RAISING", "R8"):
            out.append(("coherence", "LOWER", d))
        else:
            out.append(("coherence", "EXCEPTION", dict(d, own=show(own[src][0]), shape=shape(own[src][0], ov))))
    return out


def main():
    args = sys.argv[2:]
    facts = next((Facts(a) for a in args if a.endswith(".ndjson")), None)
    report = next((a for a in args if a.endswith("translation_report.json")), None)
    out_path = next((a for a in args if a.endswith(".json") and a != report), None)
    rows = Rows(report)
    cnt, decls, ex, per_decl = Counter(), Counter(), defaultdict(list), []
    for line in open(sys.argv[1]):
        if not line.strip():
            continue
        rec = json.loads(line)
        res, _, theta = S.solve_record(rec)
        if res != "OK":
            decls[res] += 1
            continue
        found = check_policy(rec, theta, facts, rows)
        bad = 0
        for kind, res, d in found:
            cnt[(kind, res)] += 1
            if res in VIOLATIONS | {"LIFT", "LOWER", "FOREIGN"}:
                key = (kind, res, d.get("where"), d.get("shape"))
                if len(ex[key]) < 3:
                    ex[key].append(d)
            bad += res in VIOLATIONS
        decls["OK, policy satisfied" if not bad else "OK, policy violated"] += 1
        per_decl.append({"decl": rec["decl"], "tier": rec.get("tier"), "violations": bad})
    summary = {"schema": "rocq2lean-solver-stage-a-policy/1", "declarations": dict(decls),
               "occurrences": {f"{k}:{r}": n for (k, r), n in sorted(cnt.items())},
               "examples": [{"constraint": k, "result": r, "where": w, "shape": sh, "examples": e}
                            for (k, r, w, sh), e in ex.items()]}
    print(json.dumps(summary, indent=1, ensure_ascii=False))
    if out_path:
        json.dump({"summary": summary, "rows": per_decl}, open(out_path, "w"), indent=1)
    sys.exit(1 if decls["OK, policy violated"] else 0)


if __name__ == "__main__":
    main()

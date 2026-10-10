#!/usr/bin/env python3
"""Independent structural audit: source IR  vs  accepted Lean terms.

    audit.py SOURCE.ndjson CONTRACT.json TRANSLATION_REPORT.json AUDIT_OUT.json

Kernel acceptance only shows that a generated body has the generated type. This audit checks
that each accepted target term is the image of its *source* term under the documented rules,
recomputed here from scratch (pure de Bruijn, no Lean code, its own copy of the rule table):

  rel i        -> bvar i                    prod/lam/let -> forall/lam/let (binder names ignored)
  app f a1..an -> app(...app(f, a1)..., an) sort         -> closed level, compared by value
  const c      -> const Rocq.<c>            ind/construct -> bootstrap target or Rocq.<...>
  cast t _     -> t                         (the translator validated the annotation)
  case         -> I.rec params motive minors indices major; motive/minor binder types and the
                  major's indices are forced by the kernel-checked recursor type and not compared;
                  each minor binds the constructor fields plus one recursive result per recursive
                  field (counted here from the source constructor), which the branch ignores
  fix          -> lam a0..an. I.rec params motive minors idx a_r Q; lambda types compared; the
                  motive is forced by the (audited) declared type; minor bodies compared with
                  each recursive call f P.. y rest  ->  (recursive result for field y) rest

Documented equivalences: binder names and binder info are not compared; the universe argument
of a template-rule constant (Eq) is not compared, because the kernel forces it to be the sort
level of the first argument; source global levels become universe parameters named
u_<name with . -> _>, and references to such generalized constants must carry that many universe
arguments, whose values (solved by Lean's unifier) are constrained by kernel typing and are not
compared; universe levels are compared through a semantic normal form max(c, u_i + k_i).
Anything outside these rules (case, fix, proj, ...) is reported as UNAUDITABLE, which fails.
"""

import json
import sys
from pathlib import Path

# Independent copy of the bootstrap table (names and universe rule only).
BOOTSTRAP = {
    "Corelib.Init.Datatypes.nat": {"types": ["Nat"], "ctors": [["Nat.zero", "Nat.succ"]], "univ": "mono"},
    "Corelib.Init.Logic.eq": {"types": ["Eq"], "ctors": [["Eq.refl"]], "univ": "template"},
}


class Mismatch(Exception):
    pass


FACTS = None     # native universe facts of the audited export (set by main)


def target_name(key):
    comps = [c for part in key.split("/") for c in part.split(".")]
    return "Rocq." + ".".join(comps)


def key_module(key):
    return key.rsplit(".", 1)[0]


def generated_names(mind, body, ctors):
    t = target_name(key_module(mind) + "." + body)
    return t, [t + "." + c for c in ctors]


def level_param(name):
    """Independent copy of the naming rule for generalized global levels."""
    return "u_" + name.replace(".", "_")


def poly_param(i):
    """Independent copy of rule R6's naming: universe variable i of a polymorphic constant."""
    return f"v_{i}"


def level_nf(l):
    """Normal form of a Lean level without imax: (constant, {param: offset}), meaning
    max(constant, param_i + offset_i). The constant is dropped when some offset dominates it
    (params are >= 0), so semantically equal levels have equal normal forms."""
    return canon(*level_raw(l))


def level_raw(l):
    k = l["k"]
    if k == "zero":
        c, ps = 0, {}
    elif k == "param":
        c, ps = None, {l["n"]: 0}
    elif k == "succ":
        c, ps = level_raw(l["l"])
        c = None if c is None else c + 1
        ps = {p: o + 1 for p, o in ps.items()}
    elif k == "max":
        c1, p1 = level_raw(l["a"])
        c2, p2 = level_raw(l["b"])
        cs = [x for x in (c1, c2) if x is not None]
        c = max(cs) if cs else None
        ps = dict(p1)
        for p, o in p2.items():
            ps[p] = max(ps.get(p, o), o)
    else:
        raise Mismatch(f"level outside the audited fragment: {k}")
    return c, ps


def canon(c, ps):
    if ps and c is not None and c <= max(ps.values()):
        c = None
    if not ps and c is None:
        c = 0
    return (c, tuple(sorted(ps.items())))


def fact_reduce(us):
    """R2⁺, independently: drop a summand Set+k of an algebraic universe when another summand l+j is
    at least as large under the native facts (k <= j for a global or variable level, or Set+(k-j) <= l
    entailed). The two universes are equal in Rocq."""
    out = []
    for e in us:
        if e["l"]["k"] == "set" and any(
                (o["l"]["k"] == "global" and (e["n"] <= o["n"] or (FACTS is not None and FACTS.entails("Set", o["l"]["n"], e["n"] - o["n"]))))
                or (o["l"]["k"] == "var" and e["n"] <= o["n"]) for o in us):
            continue
        out.append(e)
    return out


REDUCE = [False]        # the row being audited was accepted with fact-reduced universes (R2⁺)
ADMIT = [set()]         # motive levels of the row being audited (R8: Type@{l + n} -> Sort(u_l + n))


def motive_levels(ty):
    """R8, independently: levels occurring in a source type only as the codomain sort Type@{l} (one
    summand, offset 0) of a binder type with at least one argument; any other occurrence (another
    sort, a universe instance) disqualifies the level."""
    mot, oth = set(), set()

    def codomain(t, n):
        while t["k"] == "prod":
            t, n = t["b"], n + 1
        if n >= 1 and t["k"] == "sort" and t["s"]["k"] == "type" and len(t["s"]["u"]) == 1 \
                and t["s"]["u"][0]["l"]["k"] == "global" and t["s"]["u"][0]["n"] == 0:
            return t["s"]["u"][0]["l"]["n"]
        return None

    def go(t):
        if isinstance(t, list):
            for x in t:
                go(x)
            return
        if not isinstance(t, dict):
            return
        k = t.get("k")
        if k == "sort":
            if t["s"]["k"] == "type":
                oth.update(e["l"]["n"] for e in t["s"]["u"] if e["l"]["k"] == "global")
            return
        if k in ("const", "ind", "construct"):
            oth.update(l["n"] for l in t.get("u") or [] if l["k"] == "global")
        if k == "prod":
            l = codomain(t["ty"], 0)
            if l is not None:
                mot.add(l)
                d = t["ty"]
                while d["k"] == "prod":
                    go(d["ty"])
                    d = d["b"]
                go(t["b"])
                return
        for key, v in t.items():
            if key == "u" and k in ("const", "ind", "construct"):
                continue
            go(v)
    go(ty)
    return mot - oth


def source_sort_nf(s, body=None):
    """Normal form of the target sort a source sort must become: global levels of the declaration's
    type are parameters u_<name> (R2); proof-local levels (R2B) are read through their solutions
    `body[name]` (a Lean level JSON, as claimed by the report and checked by check_body_levels)."""
    if s["k"] == "prop":
        return canon(0, {})
    if s["k"] == "type":
        c, ps = None, {}
        for e in (fact_reduce(s["u"]) if REDUCE[0] else s["u"]):
            if e["l"]["k"] == "set":
                c = max(c or 0, e["n"] + 1)
            elif e["l"]["k"] == "global" and body is not None and e["l"]["n"] in body:
                bc, bps = level_raw(body[e["l"]["n"]])
                inc = 0 if e["l"]["n"] in ADMIT[0] else 1          # R8: a motive level's solution is the sort level
                if bc is not None:
                    c = max(c or 0, bc + e["n"] + inc)
                for p, o in bps.items():
                    ps[p] = max(ps.get(p, 0), o + e["n"] + inc)
            elif e["l"]["k"] == "global":
                p = level_param(e["l"]["n"])
                off = e["n"] if e["l"]["n"] in ADMIT[0] else e["n"] + 1      # R8: motive level is a sort level
                ps[p] = max(ps.get(p, 0), off)
            elif e["l"]["k"] == "var":           # R6: universe variable of a polymorphic constant
                p = poly_param(e["l"]["i"])
                ps[p] = max(ps.get(p, 0), e["n"] + 1)
            else:
                raise Mismatch(f"source universe outside the audited fragment: {e}")
        return canon(c, ps)
    raise Mismatch(f"source sort outside the audited fragment: {s}")


def source_inst_nf(l, body=None):
    """R6: normal form of the Lean level a source instance *level* must become (no successor:
    Type@{l} is Sort(l+1), so the level l itself maps to its parameter): Set -> 0, var i -> v_i,
    a global level -> its parameter u_<name>, or its reported solution when proof-local."""
    if l["k"] == "set":
        return canon(0, {})
    if l["k"] == "var":
        return canon(None, {poly_param(l["i"]): 0})
    if l["k"] == "global":
        if body is not None and l["n"] in body:
            return level_nf(body[l["n"]])
        return canon(None, {level_param(l["n"]): 0})
    raise Mismatch(f"instance level outside the audited fragment: {l}")


def source_globals(t, acc):
    if isinstance(t, dict):
        if t.get("k") in ("const", "ind", "construct"):     # R6: global levels of universe instances
            for l in t.get("u") or []:
                if l["k"] == "global":
                    acc.add(l["n"])
        if t.get("k") == "sort" and t["s"]["k"] == "type":
            for e in t["s"]["u"]:
                if e["l"]["k"] == "global":
                    acc.add(e["l"]["n"])
        for v in t.values():
            source_globals(v, acc)
    elif isinstance(t, list):
        for v in t:
            source_globals(v, acc)
    return acc


def ind_globals(d):
    """Source global levels of an inductive block (arity and constructor types), sorted: they
    become the Lean universe parameters u_<name> (rule R2T)."""
    return sorted(source_globals([[b["type"], [c["type"] for c in b["ctors"]]] for b in d["bodies"]], set()))


def own_level_interp(facts, own):
    """Independent copy of rule R2F: the Lean level standing for each own level l of a non-template
    inductive block is max(u_l, interp(m) + k) over native facts m <= l (k = 0) / m < l (k = 1)
    between own levels; mutually <= (equal) levels contribute their parameter directly."""
    rel = lambda a, b: facts.rel.get((a, b))
    leq = lambda a, b: rel(a, b) in ("le", "lt")

    def go(l, fuel):
        acc = {"k": "param", "n": level_param(l)}
        if fuel == 0:
            return acc
        for m in own:
            if m == l or not leq(m, l):
                continue
            base = {"k": "param", "n": level_param(m)} if leq(l, m) else go(m, fuel - 1)
            if rel(m, l) == "lt":
                base = {"k": "succ", "l": base}
            acc = {"k": "max", "a": acc, "b": base}
        return acc
    return {l: go(l, len(own) + 1) for l in own}


def ind_params(d, r):
    """Universe parameters (source levels) of a generated inductive: for a non-template block all its
    levels (R2T); for a template block its levels minus the reported solved ones (R5S), which must
    include every template level. Returns (params, solutions, template binding or None)."""
    tb = template_binding(d)
    if tb is None:
        # R3G: implicit levels (free reference levels taken as parameters) join the block's parameters
        implicit = set(r.get("implicit_levels") or [])
        if implicit & set(ind_globals(d)):
            raise Mismatch(f"implicit levels {sorted(implicit & set(ind_globals(d)))} occur explicitly in the source")
        return sorted(set(ind_globals(d)) | implicit), {}, None
    sol = {x["level"]: x["sigma"] for x in r.get("solved_levels", [])}
    params = sorted(set(ind_globals(d)) - set(sol))
    if not set(sol) <= set(ind_globals(d)) - set(tb) or not set(tb) <= set(params):
        raise Mismatch(f"solved levels {sorted(sol)} must be non-template levels of the block")
    return params, sol, tb


TEMPLATE_LEVELS = set()     # template levels of the export's template inductives (R5, not R3)


def template_binding(d):
    """For a template inductive, from the Rocq kernel's own record (native.template_info, round-trip
    checked): {level name: parameter position (regular order)}; None if not template."""
    if not (d.get("native") or {}).get("template"):
        return None
    ti = d["native"].get("template_info") or {}
    out = {}
    params = list(reversed(d["params"]))              # regular order
    for k, pa in enumerate(ti.get("param_arguments", [])):
        if pa is None:
            continue
        us = pa.get("u", [])
        if pa.get("k") not in ("type", "quality_sort") or len(us) != 1 or us[0].get("n") != 0 or us[0].get("bound") is None:
            raise Mismatch(f"template parameter {k} outside the audited fragment")
        # the quoted parameter is an arity `∀ zs, Type@{l}`; record how many binders precede the sort
        t, nz = params[k]["ty"], 0
        while t["k"] == "prod":
            t, nz = t["b"], nz + 1
        if t != {"k": "sort", "s": {"k": "type", "u": [{"l": {"k": "global", "n": us[0]["l"]}, "n": 0}]}}:
            raise Mismatch(f"template parameter {k} is not an arity ending in Type@{{{us[0]['l']}}}")
        out[us[0]["l"]] = (k, nz)
    if sorted(out) != sorted(ti.get("defaults", [])):
        raise Mismatch("template binding does not cover exactly the template levels")
    return out


def changed_params(t, nl, r, depth=0, acc=None):
    """Independent copy of the rule deciding generalized fixpoint arguments: positions i < r of the
    leading arguments that some recursive call changes (`depth` binders below the fix binder: the
    function is rel depth, leading lambda i is rel depth-1-i)."""
    acc = set() if acc is None else acc
    if isinstance(t, list):
        for v in t:
            changed_params(v, nl, r, depth, acc)
        return acc
    if not isinstance(t, dict):
        return acc
    k = t.get("k")
    go = lambda u, d: changed_params(u, nl, r, depth + d, acc)
    if k == "app":
        if t["f"] == {"k": "rel", "i": depth} and depth >= nl:
            for i, a in enumerate(t["args"][:r]):
                if a != {"k": "rel", "i": depth - 1 - i}:
                    acc.add(i)
        go(t["f"], 0)
        for a in t["args"]:
            go(a, 0)
    elif k in ("prod", "lam"):
        go(t["ty"], 0); go(t["b"], 1)
    elif k == "let":
        go(t["v"], 0); go(t["ty"], 0); go(t["b"], 1)
    elif k == "case":
        for x in t["p"]["params"]:
            go(x, 0)
        go(t["p"]["ret"], len(t["p"]["ctx"])); go(t["c"], 0)
        for br in t["brs"]:
            go(br["body"], len(br["ctx"]))
    elif k in ("fix", "cofix"):
        for d in t["defs"]:
            go(d["ty"], 0); go(d["body"], len(t["defs"]))
    else:
        for key, v in t.items():
            if isinstance(v, (dict, list)) and key not in ("n",):
                go(v, 0)
    return acc


class Auditor:
    def __init__(self, decls, results, recursors=None):
        self.body = None          # proof-local level solutions of the declaration being audited
        self.recursors = recursors
        self.decls = decls
        self.ok = {r["source"]: r for r in results
                   if r["status"] in ("TRANSLATED_AND_CHECKED", "BOOTSTRAP_RESOLVED")}

    def ind_target(self, ref):
        mind, idx = ref["mind"], ref["i"]
        if mind in BOOTSTRAP:
            b = BOOTSTRAP[mind]
            return b["types"][idx], b["ctors"][idx], b["univ"]
        r = self.ok.get(mind)
        if r is not None and r["status"] == "TRANSLATED_AND_CHECKED" and self.decls[mind]["kind"] == "inductive":
            body = self.decls[mind]["bodies"][idx]
            t, cs = generated_names(mind, body["name"], [c["name"] for c in body["ctors"]])
            n = len(ind_params(self.decls[mind], r)[0])
            return t, cs, ("mono" if n == 0 else ("params", n))
        raise Mismatch(f"inductive {mind} has no audited realisation")

    def head(self, t):
        """(expected const name, universe rule) for a global head."""
        k = t["k"]
        if k == "const":
            if t["c"] not in self.ok or self.ok[t["c"]]["status"] != "TRANSLATED_AND_CHECKED":
                raise Mismatch(f"reference to non-accepted constant {t['c']}")
            n = len(self.ok[t["c"]].get("level_params", []))
            kp = poly_count(self.decls[t["c"]], self.ok[t["c"]])
            if len(t["u"]) != kp:
                raise Mismatch(f"universe instance of {len(t['u'])} levels on {t['c']}, which has {kp} universe variables")
            if kp:
                return target_name(t["c"]), ("poly", kp, n, t["u"])
            return target_name(t["c"]), ("mono" if n == 0 else ("params", n))
        if k == "ind":
            name, _, univ = self.ind_target(t["ind"])
            return name, univ
        if k == "construct":
            _, ctors, univ = self.ind_target(t["ind"])
            return ctors[t["c"]], univ
        return None

    # Variable environments: env[i] is what source `rel i` must become in the target, either
    # ("bvar", j) or ("const", name) (a block self-reference in a constructor type).
    @staticmethod
    def shift(env, n):
        """The target has `n` extra binders that the source does not."""
        out = []
        for x in env:
            if x[0] == "bvar":
                out.append(("bvar", x[1] + n, *x[2:]))
            elif x[0] == "tgt":
                out.append(("tgt", lift(x[1], n)))
            elif x[0] == "expect":
                out.append(("expect", x[1], Auditor.shift(x[2], n)))
            else:
                out.append(x)
        return out

    @classmethod
    def push(cls, env, n=1):
        for _ in range(n):
            env = [("bvar", 0)] + cls.shift(env, 1)
        return env

    def check(self, s, e, path, env=()):
        """Compare source term `s` with target Lean expr JSON `e` under `env`."""
        env = list(env)
        k = s["k"]
        C = lambda s2, e2, seg, env2=env: self.check(s2, e2, path + [seg], env2)
        if e["k"] == "mdata":
            raise Mismatch(f"{path}: unexpected metadata node in target")
        if k == "cast":
            return C(s["t"], e, "cast")
        if k == "rel":
            if s["i"] >= len(env):
                raise Mismatch(f"{path}: source rel {s['i']} out of scope")
            want = env[s["i"]]
            if want[0] == "expect":       # a source variable that denotes a source term here
                return self.check(want[1], e, path + ["as-term"], want[2])
            if want[0] == "tgt":          # a target expression forced by typing (constructor parameters)
                if e != want[1]:
                    raise Mismatch(f"{path}: expected the parameter {want[1]}, found {e}")
                return
            if want[0] not in ("bvar", "const"):
                raise Mismatch(f"{path}: source rel {s['i']} refers to {want[0]} binder outside a supported call")
            ok = (e == {"k": "bvar", "i": want[1]}) if want[0] == "bvar" else \
                (e == {"k": "const", "n": want[1], "u": want[2] if len(want) > 2 else []})
            if not ok:
                raise Mismatch(f"{path}: source rel {s['i']} should be {want}, found {e}")
            return
        if k == "sort":
            if e["k"] != "sort" or level_nf(e["l"]) != source_sort_nf(s["s"], self.body):
                raise Mismatch(f"{path}: sort mismatch")
            return
        if k in ("prod", "lam"):
            want = "forall" if k == "prod" else "lam"
            if e["k"] != want:
                raise Mismatch(f"{path}: expected {want}, found {e['k']}")
            C(s["ty"], e["t"], k + ".ty")
            C(s["b"], e["b"], k + ".b", self.push(env))
            return
        if k == "let":
            if e["k"] != "let":
                raise Mismatch(f"{path}: expected let, found {e['k']}")
            C(s["ty"], e["t"], "let.ty")
            C(s["v"], e["v"], "let.v")
            C(s["b"], e["b"], "let.b", self.push(env))
            return
        if k == "app" and s["f"]["k"] == "rel" and s["f"]["i"] < len(env) and env[s["f"]["i"]][0] == "rec":
            return self.check_rec_call(s, e, path, env, env[s["f"]["i"]][1])
        if k == "app":
            args = s["args"]
            cur = e
            for i in reversed(range(len(args))):
                if cur["k"] != "app":
                    raise Mismatch(f"{path}: expected application with {len(args)} arguments")
                C(args[i], cur["a"], f"arg{i}")
                cur = cur["f"]
            return self.check_head(s["f"], cur, path + ["f"], env)
        if k in ("const", "ind", "construct"):
            return self.check_head(s, e, path, env)
        if k == "case":
            return self.check_case(s, e, path, env)
        if k == "proj":
            # primitive projection -> Lean kernel projection on the same field of the generated structure
            tname, _, _ = self.ind_target(s["p"]["ind"])
            if e["k"] != "proj" or e["s"] != tname or e["i"] != s["p"]["arg"]:
                raise Mismatch(f"{path}: projection {s['p']['arg']} of {tname} expected, found {e.get('k')}")
            return C(s["t"], e["e"], "proj")
        if k == "fix":
            return self.check_fix(s, e, path, env)
        raise Mismatch(f"{path}: UNAUDITABLE source node '{k}'")

    def check_head(self, s, e, path, env=()):
        h = self.head(s) if s["k"] in ("const", "ind", "construct") else None
        if h is None:
            return self.check(s, e, path, env)
        name, univ = h
        if e["k"] != "const" or e["n"] != name:
            raise Mismatch(f"{path}: expected constant {name}, found {e.get('n', e['k'])}")
        if univ == "mono" and e["u"]:
            raise Mismatch(f"{path}: unexpected universe arguments on {name}")
        if univ == "template" and len(e["u"]) != 1:
            raise Mismatch(f"{path}: template constant {name} must have one universe argument")
        if isinstance(univ, tuple) and univ[0] == "poly":
            # R6: the first arguments are the source instance, level by level; the others obey R3
            _, kp, n, src = univ
            if len(e["u"]) != n:
                raise Mismatch(f"{path}: polymorphic constant {name} must have {n} universe arguments")
            for i in range(kp):
                if level_nf(e["u"][i]) != source_inst_nf(src[i], self.body):
                    raise Mismatch(f"{path}: universe argument {i} of {name} is not the image of the source instance level {src[i]}")
        elif isinstance(univ, tuple) and len(e["u"]) != univ[1]:
            raise Mismatch(f"{path}: generalized constant {name} must have {univ[1]} universe arguments")

    def recursive_fields(self, ref, ctor):
        """Number of recursive constructor arguments (Lean adds one recursive result for each)."""
        return len(self.recursive_positions(ref, ctor))

    def recursive_positions(self, ref, ctor):
        """Outermost-first positions of the recursive constructor arguments."""
        mib = self.decls[ref["mind"]]
        if len(mib["bodies"]) != 1:
            raise Mismatch("UNAUDITABLE: case on a mutual block")
        args = list(reversed(mib["bodies"][ref["i"]]["ctors"][ctor]["args"]))  # outermost first
        pos = []
        for p, a in enumerate(args):
            t, depth = a["ty"], 0
            while t["k"] == "prod":
                t, depth = t["b"], depth + 1
            while t["k"] == "app":
                t = t["f"]
            if t == {"k": "rel", "i": p + mib["npars"] + depth}:
                if depth:
                    raise Mismatch("UNAUDITABLE: functional recursive field")
                pos.append(p)
        return pos

    @staticmethod
    def strip_lams(e, n, path):
        for _ in range(n):
            if e["k"] != "lam":
                raise Mismatch(f"{path}: expected {n} binders")
            e = e["b"]
        return e

    def check_case(self, s, e, path, env):
        ref = s["ci"]["ind"]
        tname, _, _ = self.ind_target(ref)
        spine = []
        cur = e
        while cur["k"] == "app":
            spine.append(cur["a"])
            cur = cur["f"]
        spine.reverse()
        if cur["k"] != "const" or cur["n"] != tname + ".rec":
            raise Mismatch(f"{path}: match must lower to {tname}.rec, found {cur.get('n', cur['k'])}")
        p, brs = s["p"], s["brs"]
        npar, nidx = len(p["params"]), len(p["ctx"]) - 1
        if len(spine) != npar + 1 + len(brs) + nidx + 1:
            raise Mismatch(f"{path}: {tname}.rec applied to {len(spine)} arguments")
        for i, a in enumerate(p["params"]):
            self.check(a, spine[i], path + [f"param{i}"], env)
        motive = self.strip_lams(spine[npar], len(p["ctx"]), path + ["motive"])
        self.check(p["ret"], motive, path + ["motive"], self.push(env, len(p["ctx"])))
        self.check_rec_binders(cur, spine, npar, len(brs), nidx, path, [self.recursive_fields(ref, k) for k in range(len(brs))],
                               [len(br["ctx"]) for br in brs], 0)
        for k, br in enumerate(brs):
            nf, nih = len(br["ctx"]), self.recursive_fields(ref, k)
            body = self.strip_lams(spine[npar + 1 + k], nf + nih, path + [f"minor{k}"])
            self.check(br["body"], body, path + [f"minor{k}"], self.shift(self.push(env, nf), nih))
        # Indices of the major premise are forced by the recursor's (kernel-checked) type.
        self.check(s["c"], spine[-1], path + ["major"], env)

    def check_rec_binders(self, head, spine, npar, nmin, nidx, path, nihs, nfs, nq):
        """Recursor identity/levels (kernel metadata) and the binder types of the motive and of
        every minor premise, reconstructed from the kernel-checked recursor type instantiated
        with the actual parameters and motive, compared modulo beta and binder names."""
        rec = self.recursors.get(head["n"]) if self.recursors is not None else None
        if rec is None:
            raise Mismatch(f"{path}: no kernel metadata for recursor {head['n']} (fail closed)")
        if len(head["u"]) != len(rec["level_params"]):
            raise Mismatch(f"{path}: {head['n']} applied to {len(head['u'])} universe levels, kernel expects {len(rec['level_params'])}")
        if (rec["num_params"], rec["num_indices"], rec["num_minors"], rec["num_motives"]) != (npar, nidx, nmin, 1):
            raise Mismatch(f"{path}: recursor shape differs from the source match")
        if [rec["rule_nfields"][k] for k in range(nmin)] != nfs:
            raise Mismatch(f"{path}: constructor field counts differ from the kernel recursor rules")
        ty = inst_levels(rec["type"], dict(zip(rec["level_params"], head["u"])))
        ty = inst_forall(ty, spine[:npar], path)
        mdoms, _ = foralls(ty, 1, path + ["motive"])
        want, _ = foralls(mdoms[0], nidx + 1, path + ["motive type"])
        got, _ = lam_domains(spine[npar], nidx + 1, path + ["motive"])
        for i, (w, g) in enumerate(zip(want, got)):
            if not same_mod_beta(w, g):
                raise Mismatch(f"{path}: motive binder {i} type differs from the recursor's")
        ty = inst_forall(ty, [spine[npar]], path)
        for k in range(nmin):
            ty = beta(ty)
            if ty["k"] != "forall":
                raise Mismatch(f"{path}: recursor has fewer minors than expected")
            mty = ty["t"]
            nb = nfs[k] + nihs[k]
            want, rest = foralls(mty, nb, path + [f"minor{k} type"])
            if nq:
                qwant, _ = foralls(rest, nq, path + [f"minor{k} result"])
                want = want + qwant
            got, _ = lam_domains(spine[npar + 1 + k], nb + nq, path + [f"minor{k}"])
            for i, (w, g) in enumerate(zip(want, got)):
                if not same_mod_beta(w, g):
                    raise Mismatch(f"{path}: minor {k} binder {i} type differs from the recursor's")
            ty = subst(ty["b"], spine[npar + 1 + k])

    @staticmethod
    def unspine(e):
        spine = []
        while e["k"] == "app":
            spine.append(e["a"])
            e = e["f"]
        return e, list(reversed(spine))

    def check_fix(self, s, e, path, env):
        """fix f a0..a_{n-1} {struct a_r} := match a_r with ... end
           ->  lam a0..a_{n-1}. I.rec params motive minors idx a_r Q   (Q = a_{r+1}..)"""
        if len(s["defs"]) != 1 or s["idx"] != 0:
            raise Mismatch(f"{path}: UNAUDITABLE mutual fixpoint")
        d = s["defs"][0]
        r = d["rarg"]
        lams, b = [], d["body"]
        while b["k"] == "lam":
            lams.append(b)
            b = b["b"]
        nl = len(lams)
        if b["k"] != "case" or b["c"] != {"k": "rel", "i": nl - 1 - r}:
            raise Mismatch(f"{path}: UNAUDITABLE fixpoint shape")
        senv = [("forbid",)] + list(env)      # the source binds f; the target does not
        cur = e
        for i, lam in enumerate(lams):
            if cur["k"] != "lam":
                raise Mismatch(f"{path}: expected {nl} lambdas")
            self.check(lam["ty"], cur["t"], path + [f"lam{i}"], senv)
            senv = self.push(senv)
            cur = cur["b"]
        # Index positions: earlier parameters that are indices of the decreasing argument's type.
        xty = lams[r]["ty"]
        xargs = []
        while xty["k"] == "app":
            xargs = xty["args"] + xargs
            xty = xty["f"]
        ref = b["ci"]["ind"]
        npar = b["ci"]["npar"]
        idx_pos = {r - 1 - a["i"] for a in xargs[npar:] if a["k"] == "rel" and a["i"] < r}
        # Leading arguments changed by recursive calls (not indices) are generalized in the motive.
        gpos = sorted(changed_params(d["body"], nl, r) - idx_pos)
        ng = len(gpos)
        head, spine = self.unspine(cur)
        tname, _, _ = self.ind_target(ref)
        if head["k"] != "const" or head["n"] != tname + ".rec":
            raise Mismatch(f"{path}: fixpoint must lower to {tname}.rec")
        nmin, nq, nidx = len(b["brs"]), nl - r - 1, len(b["p"]["ctx"]) - 1
        if len(spine) != npar + 1 + nmin + nidx + 1 + ng + nq:
            raise Mismatch(f"{path}: {tname}.rec applied to {len(spine)} arguments")
        # Major premise, then the generalized arguments, then Q, in order.
        self.check({"k": "rel", "i": nl - 1 - r}, spine[npar + 1 + nmin + nidx], path + ["major"], senv)
        for j, i in enumerate(gpos):
            self.check({"k": "rel", "i": nl - 1 - i}, spine[npar + 1 + nmin + nidx + 1 + j], path + [f"g{j}"], senv)
        for j in range(nq):
            self.check({"k": "rel", "i": nq - 1 - j}, spine[len(spine) - nq + j], path + [f"q{j}"], senv)
        # Parameters and indices given to the recursor are those of the decreasing argument's
        # source type (its lambda type, under the first r lambdas).
        env_r = [("forbid",)] + list(env)
        for _ in range(r):
            env_r = self.push(env_r)
        env_r = self.shift(env_r, nl - r)
        if len(xargs) != npar + nidx:
            raise Mismatch(f"{path}: decreasing argument's type has {len(xargs)} arguments, expected {npar + nidx}")
        for i in range(npar):
            self.check(xargs[i], spine[i], path + [f"param{i}"], env_r)
        for j in range(nidx):
            self.check(xargs[npar + j], spine[npar + 1 + nmin + j], path + [f"index{j}"], env_r)
        # Motive body = the source fixpoint type after P and x, under: x -> motive binder 0,
        # index parameters -> motive index binders, other parameters -> the outer lambdas.
        idx_of = {}
        for j, a in enumerate(xargs[npar:]):
            if a["k"] == "rel" and a["i"] < r:
                idx_of[r - 1 - a["i"]] = j
        def lead_env(i, extra):
            """Target images of the source context of leading lambda i's type (lambdas 0..i-1, then
            the fix binder, then the outer context), at `extra` binders below the motive's
            binders (idx, x): generalized arguments map to their motive foralls."""
            e = []
            for kk in reversed(range(i)):
                if kk in gpos:
                    e.append(("bvar", extra - 1 - gpos.index(kk)))
                elif kk in idx_of:
                    e.append(("bvar", extra + nidx - idx_of[kk]))
                else:
                    e.append(("bvar", (nl - 1 - kk) + nidx + 1 + extra))
            return e + [("forbid",)] + self.shift(list(env), nl + nidx + 1 + extra)

        menv = [("bvar", ng)]
        for i in reversed(range(r)):
            if i in gpos:
                menv.append(("bvar", ng - 1 - gpos.index(i)))
            else:
                menv.append(("bvar", ng + nidx - idx_of[i]) if i in idx_of else ("bvar", (nl - 1 - i) + nidx + 1 + ng))
        menv += self.shift(list(env), nl + nidx + 1 + ng)
        fty = d["ty"]
        for _ in range(r + 1):
            if fty["k"] != "prod":
                raise Mismatch(f"{path}: fixpoint type has fewer than {r + 1} binders")
            fty = fty["b"]
        mbody = self.strip_lams(spine[npar], nidx + 1, path + ["motive"])
        for j, i in enumerate(gpos):          # ∀ G: the generalized arguments' source types
            if mbody["k"] != "forall":
                raise Mismatch(f"{path}: motive lacks the generalized argument {i}")
            self.check(lams[i]["ty"], mbody["t"], path + [f"motive g{j}"], lead_env(i, j))
            mbody = mbody["b"]
        self.check(fty, mbody, path + ["motive body"], menv)
        self.check_rec_binders(head, spine, npar, nmin, nidx, path,
                               [len(self.recursive_positions(ref, k)) for k in range(nmin)],
                               [len(br["ctx"]) for br in b["brs"]], ng + nq)
        for k, br in enumerate(b["brs"]):
            nf = len(br["ctx"])
            rpos = self.recursive_positions(ref, k)
            nih = len(rpos)
            body = self.strip_lams(spine[npar + 1 + k], nf + nih + ng + nq, path + [f"minor{k}"])
            depth = nf + nih + ng + nq
            benv = [("bvar", q + nih + ng + nq, "field", k, q) for q in range(nf)]   # q: innermost-first
            # In branch k (run at every recursion depth) the decreasing argument denotes the
            # constructor applied to the parameters and fields, and its index variables denote that
            # constructor's indices (source `ctor.indices`, in the context params + fields).
            ctor_env = [("bvar", q + nih + ng + nq) for q in range(nf)] + \
                [("tgt", lift(spine[npar - 1 - qq], depth)) for qq in range(npar)] + [("forbid",)]
            xk = {"k": "construct", "ind": ref, "c": k, "u": []}
            if npar + nf:
                xk = {"k": "app", "f": xk, "args": [{"k": "rel", "i": nf + npar - 1 - pi} for pi in range(npar)]
                      + [{"k": "rel", "i": nf - 1 - pp} for pp in range(nf)]}
            cidx = self.decls[ref["mind"]]["bodies"][ref["i"]]["ctors"][k]["indices"]
            for t in range(nl):                                               # a_{nl-1} .. a_0
                i = nl - 1 - t
                if i > r:
                    benv.append(("bvar", nq - 1 - (i - r - 1)))
                elif i == r:
                    benv.append(("expect", xk, ctor_env))
                elif i in gpos:
                    benv.append(("bvar", nq + ng - 1 - gpos.index(i), "gen", i))
                elif i in idx_of:
                    benv.append(("expect", cidx[idx_of[i]], ctor_env))
                else:
                    benv.append(("bvar", senv[t][1] + depth, "param", i))
            info = {"minor": k, "r": r, "nf": nf, "nq": nq, "rec_q": [nf - 1 - p for p in rpos], "idx_pos": idx_pos,
                    "gpos": gpos}
            benv.append(("rec", info))
            benv += self.shift(senv[nl + 1:], depth)
            self.check(br["body"], body, path + [f"minor{k}"], benv)

    def check_rec_call(self, s, e, path, env, info):
        args, r = s["args"], info["r"]
        if len(args) < r + 1:
            raise Mismatch(f"{path}: recursive call without its decreasing argument")
        for i in range(r):
            if i in info["idx_pos"] or i in info.get("gpos", []):
                continue        # index arguments are fixed by the field's type; generalized ones are passed on
            a = args[i]
            ent = env[a["i"]] if a["k"] == "rel" and a["i"] < len(env) else None
            if not (ent and ent[0] == "bvar" and ent[2:4] == ("param", i)):
                raise Mismatch(f"{path}: recursive call changes parameter {i}")
        y = args[r]
        ent = env[y["i"]] if y["k"] == "rel" and y["i"] < len(env) else None
        if not (ent and ent[0] == "bvar" and len(ent) == 5 and ent[2] == "field" and ent[3] == info["minor"]):
            raise Mismatch(f"{path}: recursive call not on a constructor field")
        q = ent[4]
        if q not in info["rec_q"]:
            raise Mismatch(f"{path}: recursive call on a non-recursive field")
        m = info["rec_q"].index(q)
        ih = ent[1] - 1 - m - q
        rest = [args[i] for i in info.get("gpos", [])] + args[r + 1:]
        cur = e
        for j in reversed(range(len(rest))):
            if cur["k"] != "app":
                raise Mismatch(f"{path}: recursive result applied to too few arguments")
            self.check(rest[j], cur["a"], path + [f"rec-arg{j}"], env)
            cur = cur["f"]
        if cur != {"k": "bvar", "i": ih}:
            raise Mismatch(f"{path}: recursive call must become recursive result bvar {ih}, found {cur}")


# ---------- de Bruijn utilities on Lean expression JSON (independent of the translator) ----------

def lift(e, n, k=0):
    """Add n to every bvar >= k."""
    t = e["k"]
    if t == "bvar":
        return {"k": "bvar", "i": e["i"] + n} if e["i"] >= k else e
    if t == "app":
        return {"k": "app", "f": lift(e["f"], n, k), "a": lift(e["a"], n, k)}
    if t in ("lam", "forall"):
        return dict(e, t=lift(e["t"], n, k), b=lift(e["b"], n, k + 1))
    if t == "let":
        return dict(e, t=lift(e["t"], n, k), v=lift(e["v"], n, k), b=lift(e["b"], n, k + 1))
    if t in ("mdata", "proj"):
        return dict(e, e=lift(e["e"], n, k))
    return e


def subst(e, arg, k=0):
    """Replace bvar k by arg (lifted under binders) and lower the bvars above it."""
    t = e["k"]
    if t == "bvar":
        if e["i"] == k:
            return lift(arg, k)
        return {"k": "bvar", "i": e["i"] - 1} if e["i"] > k else e
    if t == "app":
        return {"k": "app", "f": subst(e["f"], arg, k), "a": subst(e["a"], arg, k)}
    if t in ("lam", "forall"):
        return dict(e, t=subst(e["t"], arg, k), b=subst(e["b"], arg, k + 1))
    if t == "let":
        return dict(e, t=subst(e["t"], arg, k), v=subst(e["v"], arg, k), b=subst(e["b"], arg, k + 1))
    if t in ("mdata", "proj"):
        return dict(e, e=subst(e["e"], arg, k))
    return e


def inst_levels(e, m):
    if isinstance(e, dict):
        if e.get("k") == "param" and e.get("n") in m and set(e) == {"k", "n"}:
            return m[e["n"]]
        return {k: inst_levels(v, m) for k, v in e.items()}
    if isinstance(e, list):
        return [inst_levels(v, m) for v in e]
    return e


def beta(e):
    """Full beta normal form."""
    t = e["k"]
    if t == "app":
        f, a = beta(e["f"]), beta(e["a"])
        if f["k"] == "lam":
            return beta(subst(f["b"], a))
        return {"k": "app", "f": f, "a": a}
    if t in ("lam", "forall"):
        return dict(e, t=beta(e["t"]), b=beta(e["b"]))
    if t == "let":
        return dict(e, t=beta(e["t"]), v=beta(e["v"]), b=beta(e["b"]))
    if t == "mdata":
        return beta(e["e"])
    return e


def anon(e):
    if isinstance(e, dict):
        return {k: anon(v) for k, v in e.items() if k != "n" or e.get("k") in ("const", "param")}
    if isinstance(e, list):
        return [anon(v) for v in e]
    return e


def same_mod_beta(a, b):
    return anon(beta(a)) == anon(beta(b))


def foralls(e, n, path):
    """Domains of the first n foralls of e (each under the previous binders) and the rest."""
    doms = []
    for _ in range(n):
        e = beta(e)
        if e["k"] != "forall":
            raise Mismatch(f"{path}: expected {n} binders in the recursor type")
        doms.append(e["t"])
        e = e["b"]
    return doms, e


def lam_domains(e, n, path):
    doms = []
    for _ in range(n):
        if e["k"] != "lam":
            raise Mismatch(f"{path}: expected {n} lambdas")
        doms.append(e["t"])
        e = e["b"]
    return doms, e


def inst_forall(ty, args, path):
    """Instantiate leading foralls of ty with args (all in the same outer context)."""
    for a in args:
        ty = beta(ty)
        if ty["k"] != "forall":
            raise Mismatch(f"{path}: recursor type has too few binders")
        ty = subst(ty["b"], a)
    return ty


class Facts:
    """Native universe facts of the export (independent reading of the IR record)."""

    def __init__(self, rec):
        self.levels = ["Set"] + list(rec["levels"])
        self.rel = {(x["l"], x["r"]): x["rel"] for x in rec["relations"]}

    def entails(self, a, b, k):
        """a + k <= b in the source universe graph."""
        if k <= 0:
            return a == b or self.rel.get((a, b)) in ("le", "lt")
        if k == 1:
            return self.rel.get((a, b)) == "lt"
        return any(self.rel.get((a, c)) == "lt" and self.entails(c, b, k - 1) for c in self.levels)


def const_occurrences(e, acc):
    stack = [e]
    while stack:
        x = stack.pop()
        if isinstance(x, dict):
            if x.get("k") == "const":
                acc.append((x["n"], x["u"]))
            stack.extend(v for v in x.values() if isinstance(v, (dict, list)))
        elif isinstance(x, list):
            stack.extend(x)
    return acc


def check_universe_args(facts, own, gen, exprs, body=None, poly=None, admit=None, own_admit=frozenset(), lift=False):
    """Rule R3 (docs/UNIVERSE_TRANSLATION.md) for every reference in `exprs`.
    own: source global levels of the referring declaration; gen: target name -> source levels;
    poly: target name -> number of leading R6 instance arguments (checked structurally, not by R3)."""
    n = 0
    own_params = {level_param(g): g for g in own}
    for e in exprs:
        for name, us in const_occurrences(e, []):
            if name not in gen:
                continue
            us = us[(poly or {}).get(name, 0):]
            ls = gen[name]
            c_adm = (admit or {}).get(name, set())
            if len(us) != len(ls):
                raise Mismatch(f"{name}: {len(us)} universe arguments for {len(ls)} parameters")
            for l, sigma in zip(ls, us):
                if l in TEMPLATE_LEVELS:
                    continue                      # R5: instantiated from the arguments, checked by InstanceLevels
                c, ps = level_nf(sigma)
                ca, da = l in c_adm, l in own_admit      # R8: motive-level parameters (one above the image)
                if da and not ca:
                    raise Mismatch(f"{name}: source level {l} is a motive level of the referring declaration only")
                bump = (lambda x: {"k": "succ", "l": x}) if ca and not da else (lambda x: x)
                if body and l in body:
                    if (c, ps) != level_nf(bump(body[l])):
                        raise Mismatch(f"{name}: source level {l} is proof-local, argument must be its solution {body[l]}")
                elif l in own:
                    if (c, ps) != level_nf(bump({"k": "param", "n": level_param(l)})):
                        raise Mismatch(f"{name}: source level {l} is shared, argument must be {level_param(l)}")
                else:
                    if c is not None and not (ca and c == 0) and not facts.entails("Set", l, c - 1 if ca else c):
                        raise Mismatch(f"{name}: Set + {c} <= {l} not entailed by the source universe graph")
                    for p, k in ps:
                        if p not in own_params:
                            raise Mismatch(f"{name}: argument mentions {p}, not a parameter of the referring declaration")
                        m = own_params[p]
                        e = k + (1 if m in own_admit else 0) - (1 if ca else 0)
                        # no raising; in rows of the cumulativity tier only (R3-up), also the own level
                        # itself (effective offset 0) with l <= m
                        if not (facts.entails(m, l, max(e, 0)) or (lift and e == 0 and facts.entails(l, m, 0))):
                            raise Mismatch(f"{name}: {m} + {k} <= {l} not entailed by the source universe graph")
                n += 1
    return n


# ---------- instance levels of template constants and recursors (independent recomputation) ----------

_ZERO = {"k": "zero"}
_ONE = {"k": "succ", "l": _ZERO}
# Types of the bootstrap targets (independent copy): Nat : Type, Eq.{u} : {α : Sort u} → α → α → Prop.
BOOT_TYPES = {
    "Nat": ({"k": "sort", "l": _ONE}, []),
    "Eq": ({"k": "forall", "n": "α", "t": {"k": "sort", "l": {"k": "param", "n": "u"}},
            "b": {"k": "forall", "n": "a", "t": {"k": "bvar", "i": 0},
                  "b": {"k": "forall", "n": "b", "t": {"k": "bvar", "i": 1}, "b": {"k": "sort", "l": _ZERO}}}}, ["u"]),
}


class InstanceLevels:
    """Recomputes, from the audited target terms alone, the universe arguments that kernel typing
    determines and that no source instance records (docs/UNIVERSE_TRANSLATION.md, R4):

      Eq.{u} A …, Eq.refl.{u} A …   u = the sort level of A's type
      Eq.rec.{v, u} A …             u as above
      I.rec.{v, …} params motive …  v = the sort level of the motive's codomain (large eliminators)

    Types of heads come from the report rows (already structurally audited against the source)
    and from an independent copy of the bootstrap types; recursor shapes from the kernel metadata.
    Occurrences whose level this small inference cannot determine are counted as deferred; the
    consumer checks every occurrence (`instance_levels` obligation) in a fresh Lean process."""

    def __init__(self, rows, recursors):
        self.types = dict(BOOT_TYPES)
        for r in rows:
            if r.get("status") != "TRANSLATED_AND_CHECKED" or r.get("target_type") is None:
                continue
            self.types[r["target"]] = (r["target_type"], r.get("level_params", []))
            for c in r.get("target_ctors", []):
                self.types[c["name"]] = (c["type"], [])
        self.recursors = recursors or {}
        self.checked = self.deferred = 0
        # template inductives (R5): head -> ([(level index, parameter position)], level offset)
        self.template = {}

    def head_type(self, h):
        t = self.types.get(h["n"])
        if t is None or len(t[1]) != len(h["u"]):
            return None
        return inst_levels(t[0], dict(zip(t[1], h["u"])))

    @staticmethod
    def result_sort(ty, nargs):
        if ty is None:
            return None
        for _ in range(nargs):
            ty = beta(ty)
            if ty["k"] != "forall":
                return None
            ty = ty["b"]
        ty = beta(ty)
        return ty["l"] if ty["k"] == "sort" else None

    def sort_of_type(self, t, ctx):
        """Level l with t : Sort l, or None."""
        k = t["k"]
        if k == "sort":
            return {"k": "succ", "l": t["l"]}
        if k == "forall":
            sb = self.sort_of_type(t["b"], [t["t"]] + ctx)
            if sb is None:
                return None
            if level_nf(sb) == canon(0, {}):
                return _ZERO                       # imax(_, 0) = 0
            sa = self.sort_of_type(t["t"], ctx)
            c, ps = level_nf(sb)
            if sa is None or not ((c or 0) >= 1 or any(o >= 1 for _, o in ps)):
                return None                       # imax with a possibly-zero codomain level
            return {"k": "max", "a": sa, "b": sb}
        if k == "let":
            return self.sort_of_type(t["b"], [t["t"]] + ctx)
        if k == "mdata":
            return self.sort_of_type(t["e"], ctx)
        head, args = Auditor.unspine(t)
        if head["k"] == "const":
            return self.result_sort(self.head_type(head), len(args))
        if head["k"] == "bvar" and head["i"] < len(ctx):
            return self.result_sort(ctx[head["i"]], len(args))
        return None

    def arity_level(self, a, nz, ctx):
        """Codomain sort level of the type of a type family `a` taking `nz` arguments (nz = 0: the
        sort level of the type `a`)."""
        for _ in range(nz):
            if a["k"] != "lam":
                head, args = Auditor.unspine(a)
                if head["k"] == "const":
                    return self.result_sort(self.head_type(head), len(args) + nz)
                if head["k"] == "bvar" and head["i"] < len(ctx):
                    return self.result_sort(ctx[head["i"]], len(args) + nz)
                return None
            ctx = [a["t"]] + ctx
            a = a["b"]
            nz -= 1
        return self.sort_of_type(a, ctx)

    def expect(self, got, want, what, problems):
        if want is None:
            self.deferred += 1
            return
        self.checked += 1
        if level_nf(got) != level_nf(want):
            problems.append(f"{what}: universe argument {got} differs from the level determined by typing {want}")

    def visit(self, e, ctx, problems, where):
        k = e["k"]
        if k in ("lam", "forall"):
            self.visit(e["t"], ctx, problems, where)
            self.visit(e["b"], [e["t"]] + ctx, problems, where)
            return
        if k == "let":
            self.visit(e["t"], ctx, problems, where)
            self.visit(e["v"], ctx, problems, where)
            self.visit(e["b"], [e["t"]] + ctx, problems, where)
            return
        if k in ("mdata", "proj"):
            self.visit(e["e"], ctx, problems, where)
            return
        head, args = Auditor.unspine(e) if k == "app" else (e, [])
        if head["k"] == "const":
            n, us = head["n"], head["u"]
            if n in ("Eq", "Eq.refl") and args and len(us) == 1:
                self.expect(us[0], self.sort_of_type(args[0], ctx), f"{where}: {n}", problems)
            if n in self.template:
                # R5: each template level is the level of its template parameter's argument (A : Sort (σ+1))
                bind, off = self.template[n]
                if off is None:
                    rec_ = self.recursors.get(n)
                    off = 1 if rec_ is not None and self.large(rec_) else 0
                for j, k, nz in bind:
                    if k < len(args) and j + off < len(us):
                        self.expect({"k": "succ", "l": us[j + off]}, self.arity_level(args[k], nz, ctx),
                                    f"{where}: {n} (template level {j} from parameter {k})", problems)
            rec = self.recursors.get(n)
            if rec is not None and rec["num_motives"] == 1 and us:
                if n == "Eq.rec" and args and len(us) == 2:
                    self.expect(us[1], self.sort_of_type(args[0], ctx), f"{where}: {n} (type level)", problems)
                if self.large(rec) and len(args) > rec["num_params"]:
                    m, mctx = args[rec["num_params"]], list(ctx)
                    for _ in range(rec["num_indices"] + 1):
                        if m["k"] != "lam":
                            m = None
                            break
                        mctx = [m["t"]] + mctx
                        m = m["b"]
                    self.expect(us[0], None if m is None else self.sort_of_type(m, mctx), f"{where}: {n} (motive level)", problems)
        if k == "app":
            if head["k"] != "const":
                self.visit(head, ctx, problems, where)
            for a in args:
                self.visit(a, ctx, problems, where)

    @staticmethod
    def large(rec):
        """The recursor eliminates into any sort: its motive's codomain is its first level parameter."""
        ty = rec["type"]
        for _ in range(rec["num_params"]):
            ty = ty["b"] if ty["k"] == "forall" else ty
        if ty["k"] != "forall":
            return False
        mt = ty["t"]
        for _ in range(rec["num_indices"] + 1):
            mt = mt["b"] if mt["k"] == "forall" else mt
        return mt["k"] == "sort" and bool(rec["level_params"]) and mt["l"] == {"k": "param", "n": rec["level_params"][0]}


def canon_levels(e):
    """Expression JSON with every universe level replaced by its semantic normal form (comparison
    up to level normalization)."""
    if isinstance(e, list):
        return [canon_levels(x) for x in e]
    if not isinstance(e, dict):
        return e
    if e.get("k") == "sort":
        return {"k": "sort", "l": repr(level_nf(e["l"]))}
    if e.get("k") == "const":
        return {"k": "const", "n": e["n"], "u": [repr(level_nf(u)) for u in e["u"]]}
    return {k: canon_levels(v) for k, v in e.items()}


def check_residuals(r):
    """Defaulted universe levels carry a justification record whose generic declaration, with its
    residual parameters set to zero, is exactly the reported one (the kernel acceptance of the
    generic declaration is re-checked by the consumer)."""
    n = r.get("universe_level_defaults", 0)
    res = r.get("universe_residuals")
    if not n and res is None:
        return
    if res is None:
        raise Mismatch(f"{n} defaulted universe level(s) without a justification record")
    ps = res.get("params", [])
    if len(ps) != n or len(set(ps)) != n or set(ps) & set(r.get("level_params", [])):
        raise Mismatch(f"residual parameters {ps} do not match {n} defaulted level(s)")
    ds = res.get("defaults", [])
    if len(ds) != n or any(p in json.dumps(d_) for d_ in ds for p in ps):
        raise Mismatch("residual defaults missing or mentioning residual parameters")
    dflt = dict(zip(ps, ds))
    if canon_levels(inst_levels(res.get("generic_type"), dflt)) != canon_levels(r.get("target_type")) or \
            canon_levels(inst_levels(res.get("generic_value"), dflt)) != canon_levels(r.get("target_value")):
        raise Mismatch("generic declaration with residual levels at their defaults differs from the reported declaration")


def poly_count(d, r):
    """R6: number of universe variables of a polymorphic source constant (0 if monomorphic); the
    report's count must agree with the source declaration."""
    u = d.get("universes") or {}
    k = len(u.get("names", [])) if u.get("k") == "polymorphic" else 0
    if (r.get("universe_poly_params") or 0) != k:
        raise Mismatch(f"reported {r.get('universe_poly_params')} universe variables, the source declares {k}")
    return k


def own_partition(d, r):
    """Rule R2S, independently: the own global levels of a constant (type and body) are exactly the
    union of its parameters (reported `level_params`, which must come from the type's levels) and
    its solved levels (reported `solved_levels`); returns (parameter levels, solutions). R6: the
    universe variables of a polymorphic constant come first, as v_0 .. v_{k-1}."""
    params, sol, interp = own_partition_full(d, r)
    return params, {**sol, **interp}


def own_partition_full(d, r):
    """own_partition, also returning the R2F-c interpretation separately: (params, proof-local
    solutions, interpretation of the own levels). R3G: the reported implicit levels (levels of
    referenced declarations, absent from the source sorts) count as type levels; R2F-c: the reported
    interpretation must be exactly the auditor's own R2F recomputation over the native facts among
    the explicit type levels and the implicit levels."""
    tl = set(source_globals(d["type"], set()))
    own = tl | source_globals(d["body"], set())
    implicit = set(r.get("implicit_levels") or [])
    if implicit & own:
        raise Mismatch(f"implicit levels {sorted(implicit & own)} occur explicitly in the source")
    tl, own = tl | implicit, own | implicit
    sol = {x["level"]: x["sigma"] for x in r.get("solved_levels", [])}
    interp = {x["level"]: x["sigma"] for x in r.get("level_interp") or []}
    if interp:
        if FACTS is None:
            raise Mismatch("level interpretation without native facts")
        if not set(interp) <= tl or set(interp) & set(sol):
            raise Mismatch(f"interpreted levels {sorted(interp)} must be type or implicit levels {sorted(tl)}, not solved ones")
        want = own_level_interp(FACTS, sorted(interp))
        for l, x in interp.items():
            if level_nf(x) != level_nf(want[l]):
                raise Mismatch(f"interpretation of {l} is {x}, the R2F interpretation is {want[l]}")
    back = {level_param(g): g for g in own}
    kp = poly_count(d, r)
    lps = r.get("level_params", [])
    if lps[:kp] != [poly_param(i) for i in range(kp)]:
        raise Mismatch(f"universe parameters {lps} do not start with the {kp} universe variables v_0 ..")
    lps = lps[kp:]
    if any(p not in back for p in lps):
        raise Mismatch(f"universe parameters {lps} are not parameters for source levels")
    params = [back[p] for p in lps]
    def mentions(j, name):
        if isinstance(j, dict):
            return (j.get("k") == "param" and j.get("n") == name) or any(mentions(v, name) for v in j.values())
        return isinstance(j, list) and any(mentions(v, name) for v in j)
    in_type = [sol[l] for l in tl if l in sol] + list(interp.values())
    if set(params) & set(sol) or set(params) | set(sol) != own or any(
            p not in tl and not mentions(in_type, level_param(p)) for p in params):
        raise Mismatch(f"parameters {params} and solved levels {sorted(sol)} do not partition the own levels "
                       f"{sorted(own)} (a parameter must be a type level or occur in a type level's solution)")
    if lps != [level_param(g) for g in sorted(params)]:
        raise Mismatch(f"universe parameters {lps} are not in source-level order")
    return params, sol, interp


def check_body_levels(facts, d, sol, params=None, admit=frozenset(), prop_offset=False):
    """Rules R2S/R2B, independently: each solution is a level over the declaration's parameters, and
    every native fact between a solved level and Set / a parameter / another solved level holds with
    solved levels read as their solutions (summand-wise entailment in the native graph)."""
    tl = sorted(params if params is not None else source_globals(d["type"], set()))
    back = {level_param(g): g for g in tl}

    def summ(x):
        if x not in sol:
            return [(x, 0)]
        c, ps = level_raw(sol[x])
        dec = 1 if x in admit else 0                 # R8: a solved motive level's solution is one above its image
        out = [("Set", max((c or 0) - dec, 0))]
        for p, k in ps.items():
            if p not in back:
                raise Mismatch(f"solution of {x} mentions {p}, not a parameter of the declaration")
            out.append((back[p], max(k + (1 if back[p] in admit else 0) - dec, 0)))     # R8: u_m is one above m
        return out

    def leq(lhs, rhs, k):
        return all((a == "Set" and i + k == 0) or any(
            (facts.entails(a, b, 0) or a == "Set") if i + k <= j else facts.entails(a, b, i + k - j) for b, j in rhs)
            for a, i in lhs)

    mine = set(tl) | set(sol) | {"Set"}
    for (a, b), r in facts.rel.items():
        if (a in sol or b in sol) and a in mine and b in mine:
            # R2B-P (cumulativity-tier rows only): a fact Set < m may stem from Prop's typing
            # (Type@{Set+1} in Rocq, Sort 1 in Lean)
            if not leq(summ(a), summ(b), 1 if (r == "lt" and not (prop_offset and a == "Set")) else 0):
                raise Mismatch(f"proof-local level solution violates the native fact {a} {r} {b}")


def closure_refs(t, acc):
    """Independent reimplementation of dependency extraction (not shared with tools/contract.py)."""
    stack = [t]
    while stack:
        x = stack.pop()
        if isinstance(x, list):
            stack.extend(x)
        elif isinstance(x, dict):
            k = x.get("k")
            if k == "const":
                acc.add(x["c"])
            elif k in ("ind", "construct"):
                acc.add(x["ind"]["mind"])
            elif k == "case":
                acc.add(x["ci"]["ind"]["mind"])
            elif k == "proj":
                acc.add(x["p"]["ind"]["mind"])
            stack.extend(x.values())
    return acc


def required_closure(decls, roots):
    seen, todo = set(), list(roots)
    while todo:
        n = todo.pop()
        if n in seen:
            continue
        if n not in decls:
            raise Mismatch(f"required declaration {n} absent from the export")
        seen.add(n)
        d = decls[n]
        refs = closure_refs([d["type"], d["body"]] if d["kind"] == "constant" else [d["params"], d["bodies"]], set())
        refs.discard(n)
        todo.extend(refs - seen)
    return seen


def sha256_path(p):
    import hashlib
    return hashlib.sha256(open(p, "rb").read()).hexdigest()


def main(src_path, contract_path, report_path, out_path, metadata_path=None):
    from collections import Counter
    lines = [json.loads(l) for l in open(src_path)]
    decls = {d["name"]: d for d in lines if d["kind"] in ("constant", "inductive")}
    con = json.load(open(contract_path))
    report = json.load(open(report_path))
    results = report.get("results", [])
    problems, verdicts = [], []

    def problem(det, msg):
        problems.append({"detector": det, "message": msg})

    # Binding.
    ir_sha = sha256_path(src_path)
    if con.get("ir_sha256") != ir_sha:
        problem("binding", "contract IR digest differs from the audited source")
    if report.get("input_sha256") != ir_sha:
        problem("binding", "report input digest differs from the audited source")
    if report.get("run_id") != con.get("run_id"):
        problem("binding", "report run id differs from the contract")
    # Requested roots, re-derived from the source root records.
    request = con.get("request") or []
    if not request:
        problem("coverage", "empty request")
    src_roots = lines[1]["roots"]
    if [r["requested"] for r in src_roots] != request:
        problem("coverage", "source root records differ from the contract request")
    canon = [r["name"] for r in src_roots]
    if len(set(canon)) != len(canon):
        problem("coverage", "two requested roots resolve to the same declaration")
    for r in src_roots:
        if r["term"]["k"] not in ("const", "ind"):
            problem("coverage", f"unsupported root form {r['term']['k']} for {r['requested']}")
    if [c["canonical"] for c in con.get("roots", [])] != canon:
        problem("coverage", "contract roots differ from the source root records")
    # Required closure, recomputed here.
    try:
        closure = required_closure(decls, canon)
    except Mismatch as e:
        closure = set()
        problem("coverage", str(e))
    if sorted(closure) != con.get("required_closure"):
        problem("coverage", "contract closure differs from the closure recomputed from the source")
    if sorted(decls) != con.get("exported"):
        problem("coverage", "contract export list differs from the source")
    # Result rows: exactly one per exported declaration.
    counts = Counter(r.get("source") for r in results)
    for s, n in counts.items():
        if n != 1:
            problem("coverage", f"{s}: {n} result rows")
        if s not in decls:
            problem("coverage", f"{s}: result for a declaration that was not exported")
    for s in decls:
        if counts[s] == 0:
            problem("coverage", f"{s}: exported declaration has no result")
    rows = {r["source"]: r for r in results if counts[r.get("source")] == 1}
    ok_status = lambda s: rows.get(s, {}).get("status")
    for s in sorted(closure):
        st = ok_status(s)
        if not (st == "TRANSLATED_AND_CHECKED" or (st == "BOOTSTRAP_RESOLVED" and s in BOOTSTRAP)):
            problem("coverage", f"required declaration {s} has status {st}")
    for c in canon:
        if ok_status(c) != "TRANSLATED_AND_CHECKED":
            problem("coverage", f"requested root {c} has status {ok_status(c)}")
    rep_roots = report.get("roots", [])
    if [(r.get("requested"), r.get("name")) for r in rep_roots] != [(r["requested"], r["name"]) for r in src_roots] \
            or any(r.get("status") != ok_status(r.get("name")) for r in rep_roots):
        problem("coverage", "report root records disagree with the contract or with the result rows")
    if report.get("status") != "OK":
        problem("coverage", f"report status is {report.get('status')!r}, not 'OK'")
    # Summary counts, recomputed.
    accepted = [s for s in closure if ok_status(s) == "TRANSLATED_AND_CHECKED"]
    want_summary = {"roots": len(canon),
                    "translated_dependencies": len([s for s in accepted if s not in canon]),
                    "bootstrap_resolved": len([s for s in decls if ok_status(s) == "BOOTSTRAP_RESOLVED"]),
                    "generated_helpers": 0,
                    "not_ok": len([s for s in decls if ok_status(s) not in ("TRANSLATED_AND_CHECKED", "BOOTSTRAP_RESOLVED")])}
    if report.get("summary") != want_summary:
        problem("coverage", f"report summary {report.get('summary')} differs from recomputed {want_summary}")
    if not accepted:
        problem("coverage", "no accepted declaration")
    # Universe interpretation (rule R3), checked independently of the translator.
    facts = Facts(lines[4]) if lines[4].get("kind") == "universe_facts" else None
    global FACTS
    FACTS = facts
    if facts is None:
        problem("universe", "source IR has no native universe facts")
    gen, poly, gen_admit = {}, {}, {}
    for s_, r_ in rows.items():
        if r_.get("status") == "TRANSLATED_AND_CHECKED" and r_.get("level_params"):
            d_ = decls[s_]
            if d_["kind"] == "constant":
                try:
                    poly[r_["target"]] = poly_count(d_, r_)
                except Mismatch:
                    poly[r_["target"]] = 0
                gen_admit[r_["target"]] = set(r_.get("admitting_levels") or [])
                try:
                    gen[r_["target"]] = sorted(own_partition(d_, r_)[0])
                except Mismatch:
                    gen[r_["target"]] = sorted(source_globals(d_["type"], set()))
            else:
                # level-parameter inductive: references obey R3 (type, constructors) on its non-template
                # levels; its template levels obey R5 (TEMPLATE_LEVELS, skipped by R3)
                try:
                    params_, _, tb_ = ind_params(d_, r_)
                except Mismatch:
                    params_, tb_ = ind_globals(d_), None
                TEMPLATE_LEVELS.update(tb_ or {})
                for n_ in [r_["target"]] + [c["name"] for c in r_.get("target_ctors", [])]:
                    gen[n_] = params_
    univ_checked = 0
    if facts is not None:
        for s_, r_ in rows.items():
            if r_.get("status") != "TRANSLATED_AND_CHECKED":
                continue
            d_ = decls[s_]
            own, bl = set(), {}
            exprs = [r_.get("target_type"), r_.get("target_value")] + [c["type"] for c in r_.get("target_ctors", [])]
            try:
                own_admit = frozenset()
                if d_["kind"] == "constant":
                    params, sol_only, interp_ = own_partition_full(d_, r_)
                    own = set(params)
                    own_admit = frozenset(r_.get("admitting_levels") or [])
                    # R8: reported motive levels must be motive levels of the source type, and type levels
                    if not own_admit <= motive_levels(d_["type"]) & set(source_globals(d_["type"], set())):
                        raise Mismatch(f"admitting levels {sorted(own_admit)} are not motive levels of the source type")
                    check_body_levels(facts, d_, sol_only, params, own_admit, bool(r_.get("universe_cumulativity")))
                    bl = {**sol_only, **interp_}            # coherence: an own level's argument is its image
                    # R3G: an implicit level must be the source level of a parameter of a referenced
                    # declaration, and occur as that parameter's argument in the accepted terms
                    for l in r_.get("implicit_levels") or []:
                        want = level_nf(interp_[l] if l in interp_ else {"k": "param", "n": level_param(l)})
                        if not any(len(us) - (poly or {}).get(nm, 0) == len(gen[nm]) and any(
                                g == l and level_nf(u) == want
                                for g, u in zip(gen[nm], us[(poly or {}).get(nm, 0):]))
                                for e_ in exprs if e_ is not None for nm, us in const_occurrences(e_, []) if nm in gen):
                            raise Mismatch(f"implicit level {l} is not the argument of a reference for that level")
                else:
                    # an inductive block's own levels: its parameters, and (template blocks) its solved levels;
                    # for a non-template block, an argument for an own level must be its R2F interpretation
                    params_i, bl, tb_i = ind_params(d_, r_)
                    own = set(params_i)
                    if tb_i is None:
                        bl = own_level_interp(facts, params_i)     # explicit and implicit levels (R2F)
                    self_n = {r_.get("target")} | {c["name"] for c in r_.get("target_ctors", [])}
                    for l in r_.get("implicit_levels") or []:
                        want = level_nf(bl[l]) if l in bl else level_nf({"k": "param", "n": level_param(l)})
                        if not any(nm not in self_n and len(us) - (poly or {}).get(nm, 0) == len(gen[nm]) and any(
                                g == l and level_nf(u) == want for g, u in zip(gen[nm], us[(poly or {}).get(nm, 0):]))
                                for e_ in exprs if e_ is not None for nm, us in const_occurrences(e_, []) if nm in gen):
                            raise Mismatch(f"implicit level {l} is not the argument of a reference for that level")
                # a block's references to itself (its constructors' result types) are at its own
                # parameters by construction, not R3 obligations
                self_names = {r_.get("target")} | {c["name"] for c in r_.get("target_ctors", [])}
                gen_ = {k: v for k, v in gen.items() if k not in self_names} if d_["kind"] == "inductive" else gen
                univ_checked += check_universe_args(facts, own, gen_, [x for x in exprs if x is not None], bl, poly,
                                                    gen_admit, own_admit, bool(r_.get("universe_cumulativity")))
            except Mismatch as e:
                problem("universe", f"{s_}: {e}")
    # Structural fidelity of every accepted translation.
    recursors = None
    if metadata_path and Path(metadata_path).exists():
        recursors = {r["name"]: r for r in json.load(open(metadata_path)).get("recursors", [])}
    # Defaulted universe levels (justification records) and typing-determined instance levels.
    inst = InstanceLevels(list(rows.values()), recursors)
    for s_, r_ in rows.items():
        d_ = decls[s_]
        if r_.get("status") == "TRANSLATED_AND_CHECKED" and d_["kind"] == "inductive":
            try:
                tb = template_binding(d_)
            except Mismatch:
                tb = None
            if tb:
                try:
                    params_ = ind_params(d_, r_)[0]
                except Mismatch:
                    params_ = sorted(tb)
                lps = [level_param(g) for g in params_]
                bind = [(lps.index(level_param(l)), k, nz) for l, (k, nz) in tb.items() if level_param(l) in lps]
                inst.template[r_["target"]] = (bind, 0)
                for c in r_.get("target_ctors", []):
                    inst.template[c["name"]] = (bind, 0)
                inst.template[r_["target"] + ".rec"] = (bind, None)       # offset 1 for large eliminators
    for s_, r_ in rows.items():
        if r_.get("status") != "TRANSLATED_AND_CHECKED":
            continue
        try:
            check_residuals(r_)
        except Mismatch as e:
            problem("universe", f"{s_}: {e}")
        ips = []
        for part in ("target_type", "target_value"):
            if r_.get(part) is not None:
                inst.visit(r_[part], [], ips, part)
        for c in r_.get("target_ctors", []):
            inst.visit(c["type"], [], ips, "ctor " + c["name"])
        for m in ips:
            problem("instance_levels", f"{s_}: {m}")
    aud = Auditor(decls, list(rows.values()), recursors)
    for s in sorted(decls):
        r, d = rows.get(s), decls[s]
        v = {"source": s, "status": r.get("status") if r else None,
             "role": "root" if s in canon else ("required" if s in closure else "extra_not_required")}
        try:
            if r is None:
                raise Mismatch("no unique result row")
            if r["status"] == "TRANSLATED_AND_CHECKED" and d["kind"] == "inductive":
                if len(d["bodies"]) != 1:
                    raise Mismatch("UNAUDITABLE: mutual block")
                b = d["bodies"][0]
                t, cs = generated_names(d["name"], b["name"], [c["name"] for c in b["ctors"]])
                if r["target"] != t or [c["name"] for c in r["target_ctors"]] != cs:
                    raise Mismatch(f"target names {r['target']} / {r['target_ctors']} are not the images of the source")
                if r.get("num_params") != d["npars"]:
                    raise Mismatch("parameter count differs from the source")
                params0, sol0, _ = ind_params(d, r)
                want_lp = [level_param(g) for g in params0]
                if r.get("level_params", []) != want_lp:
                    raise Mismatch(f"universe parameters {r.get('level_params')} are not the generalized globals {want_lp}")
                if bool(b["projs"]) != bool(r.get("primitive_record")) or (b["projs"] and (
                        len(b["ctors"]) != 1 or b["indices"] or len(b["projs"]) != len(b["ctors"][0]["args"]))):
                    raise Mismatch("primitive-record status differs from the source or the record is not structure-like")
                tb = template_binding(d)
                if bool(r.get("template")) != (tb is not None) or \
                        sorted((x["level"], x["param"]) for x in r.get("template_params", [])) != \
                        sorted((l, kn[0]) for l, kn in (tb or {}).items()):
                    raise Mismatch("template status/binding differs from the source kernel record")
                # R2F: sorts of a non-template block are read through the fact-respecting interpretation
                # R2F (non-template): sorts read through the fact-respecting interpretation;
                # R5S (template): other levels read through their reported solutions (fact-checked)
                if tb is None:
                    aud.body = own_level_interp(FACTS, params0) if FACTS is not None else None   # explicit and implicit levels
                else:
                    if FACTS is not None:
                        check_body_levels(FACTS, d, sol0, params0)
                    aud.body = sol0
                try:
                    aud.check(b["type"], r["target_type"], ["arity"])
                    self_ref = ("const", t, [{"k": "param", "n": l} for l in want_lp])
                    for c, tc in zip(b["ctors"], r["target_ctors"]):
                        aud.check(c["type"], tc["type"], ["ctor " + c["name"]], [self_ref])
                finally:
                    aud.body = None
                v["verdict"] = "MATCH"
            elif r["status"] == "TRANSLATED_AND_CHECKED":
                if d["kind"] != "constant":
                    raise Mismatch("UNAUDITABLE: declaration kind")
                if r["target"] != target_name(d["name"]):
                    raise Mismatch(f"target name {r['target']} is not the image of {d['name']}")
                want_kinds = {"transparent": {"def"}, "opaque_present": {"theorem", "opaque"},
                              "sealed_implementation": {"def"}}.get(d["body_state"], set())
                if r["target_kind"] not in want_kinds:
                    raise Mismatch(f"{d['body_state']} source emitted as {r['target_kind']}")
                if r.get("target_type") is None or r.get("target_value") is None:
                    raise Mismatch("success claimed without target type/value")
                params, sol = own_partition(d, r)
                aud.body = sol
                REDUCE[0] = bool(r.get("sort_fact_reduced"))
                ADMIT[0] = set(r.get("admitting_levels") or [])
                try:
                    aud.check(d["type"], r["target_type"], ["type"])
                    aud.check(d["body"], r["target_value"], ["body"])
                finally:
                    aud.body = None
                    REDUCE[0] = False
                    ADMIT[0] = set()
                v["verdict"] = "MATCH"
            elif r["status"] == "BOOTSTRAP_RESOLVED":
                b = BOOTSTRAP.get(d["name"])
                if b is None or r["target"] != b["types"][0]:
                    raise Mismatch("bootstrap resolution not in the audited table")
                v["verdict"] = "MATCH"
            else:
                v["verdict"] = "NOT_ACCEPTED"
        except Mismatch as e:
            v["verdict"] = "MISMATCH"
            v["reason"] = str(e)
            problem("structure", f"{s}: {e}")
        verdicts.append(v)
    out = {"schema": "rocq2lean-audit/2", "status": "OK" if not problems else "AUDIT_REJECTED",
           "universe_arguments_checked": univ_checked,
           "instance_levels": {"checked": inst.checked, "deferred_to_consumer": inst.deferred},
           "coverage": {"requested_roots": len(canon), "required_closure": len(closure), "accepted": len(accepted),
                        "extra_exported": sorted(set(decls) - closure)},
           "problems": problems, "verdicts": verdicts}
    json.dump(out, open(out_path, "w"), indent=2)
    print(out["status"], f"({len(problems)} problem(s))")
    return 0 if not problems else 1


if __name__ == "__main__":
    if len(sys.argv) not in (5, 6):
        print("usage: audit.py SOURCE.ndjson CONTRACT.json TRANSLATION_REPORT.json AUDIT_OUT.json [TARGET_METADATA.json]",
              file=sys.stderr)
        sys.exit(2)
    sys.exit(main(*sys.argv[1:]))

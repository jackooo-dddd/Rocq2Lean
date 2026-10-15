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

import copy
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
STATEMENT_MODE = [False]     # set by main_statement


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


def split_sort_interp(src_t, tgt_t, interp):
    """Coherence by unification for blocks (docs/COHERENCE_READINGS.md §6), independently: a plain block
    whose arity's final sort is read through the R2F interpretation `interp` (recomputed from the source).
    Checks that final sort and returns the arity pair with both final sorts neutralized, for the
    structural check with plain levels."""
    def fin(t, path):
        while t.get("k") in ("prod", "forall"):
            path.append("b")
            t = t["b"]
        return t
    sp, tp = [], []
    sf, tf = fin(src_t, sp), fin(tgt_t, tp)
    if sf.get("k") != "sort" or tf.get("k") != "sort":
        raise Mismatch("sort_interp: the arity does not end in a sort")
    if level_nf(tf["l"]) != source_sort_nf(sf["s"], interp):
        raise Mismatch(f"sort_interp: the arity's sort {tf['l']} is not the R2F reading of the source sort")

    def put(t, path, leaf):
        t = copy.deepcopy(t)
        cur = t
        for k in path[:-1]:
            cur = cur[k]
        if path:
            cur[path[-1]] = leaf
            return t
        return leaf
    return put(src_t, sp, {"k": "sort", "s": {"k": "prop"}}), put(tgt_t, tp, {"k": "sort", "l": {"k": "zero"}})


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


def own_level_interp(facts, own, explicit=(), minimal=frozenset()):
    """Independent copy of rule R2F: the Lean level standing for each own level l of a non-template
    inductive block is max(u_l, interp(m) + k) over native facts m <= l (k = 0) / m < l (k = 1)
    between own levels; mutually <= (equal) levels contribute their parameter directly."""
    rel = lambda a, b: facts.rel.get((a, b))
    leq = lambda a, b: rel(a, b) in ("le", "lt")

    def go(l, fuel):
        acc = {"k": "param", "n": level_param(l)}
        # R3G-F (docs/RESULT_SORT_LEVELS.md §2): a result-sort implicit level is not read through the levels
        # below it (it stands for an argument a <= l); it still raises the levels above it
        if fuel == 0 or (l in minimal and l not in explicit):
            return acc
        for m in own:
            if m == l or not leq(m, l):
                continue
            if (l, m) in DECOUPLED:           # R-CARRIER P1: not raised by its own block's other levels
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
    # R3G for template blocks (entry 14): implicit levels are non-template parameters, never solved
    implicit = set(r.get("implicit_levels") or [])
    if implicit & set(ind_globals(d)):
        raise Mismatch(f"implicit levels {sorted(implicit & set(ind_globals(d)))} occur explicitly in the source")
    params = sorted((set(ind_globals(d)) - set(sol)) | implicit)
    if not set(sol) <= set(ind_globals(d)) - set(tb) or not set(tb) <= set(params):
        raise Mismatch(f"solved levels {sorted(sol)} must be non-template levels of the block")
    return params, sol, tb


TEMPLATE_LEVELS = set()     # template levels of the export's template inductives (R5, not R3)
DEF_TYPE_CANDIDATES = []    # definitions whose type has a free-looking closed level (diagnostic only)


def PROTECTED_PIN():
    """The pinned protected-interface names (independently of the report's flags)."""
    try:
        root_dir = Path(__file__).resolve().parent.parent
        pin = json.load(open(root_dir / "tools" / "protected_interface.pin.json"))
        return set(json.loads((root_dir / pin["manifest"]).read_bytes())["protected"])
    except Exception:
        return set()


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


def changed_params(t, nl, r, depth=0, acc=None, nfun=1):
    """Independent copy of the rule deciding generalized fixpoint arguments: positions i < r of the
    leading arguments that some recursive call changes (`depth` binders below the fix binder: the
    function is rel depth, leading lambda i is rel depth-1-i; in a mutual block of nfun functions,
    calls to rel depth .. rel depth+nfun-1 count)."""
    acc = set() if acc is None else acc
    if isinstance(t, list):
        for v in t:
            changed_params(v, nl, r, depth, acc, nfun)
        return acc
    if not isinstance(t, dict):
        return acc
    k = t.get("k")
    go = lambda u, d: changed_params(u, nl, r, depth + d, acc, nfun)
    if k == "app":
        if t["f"].get("k") == "rel" and depth <= t["f"]["i"] < depth + nfun and depth >= nl:
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
        # M6 δβ-inlining: source bodies of the transparent monomorphic constants
        self.ir_bodies = {n: d["body"] for n, d in decls.items() if d.get("kind") == "constant"
                          and d.get("body_state") == "transparent" and d.get("body")
                          and (d.get("universes") or {}).get("k") == "monomorphic"}
        self.ok = {r["source"]: r for r in results
                   if r["status"] in ("TRANSLATED_AND_CHECKED", "BOOTSTRAP_RESOLVED")}
        # accepted transparent definitions (target name -> level parameters, value), for comparing
        # recursor binder types modulo delta (a source binder type may be a definition, PolC Z := Pol Z)
        self.defs = {r["target"]: (r.get("level_params") or [], r["target_value"]) for r in self.ok.values()
                     if r.get("target_kind") == "def" and r.get("target_value") is not None}
        # statement mode: unproved prerequisites (leaf -> its row) and pending definitions
        # (source -> (pending target, its hypotheses in order)); a reference to a leaf is its hypothesis
        # (env entry ("hyp", leaf, bvar)), a reference to a pending definition its artifact applied to
        # the hypotheses of its own telescope
        self.leaves = {}
        self.pending = {}
        # assembly (docs/ASSEMBLY.md): proof tasks whose final theorem `Rocq.<leaf>` was assembled
        # (leaf -> its accepted statement row); a reference to one is that theorem
        self.proved = {}
        self.pending_inds = {}      # mind -> its pending row (hypotheses as leading parameters)
        # B (docs/TERMINATION.md): termination obligations used by the Acc.rec lowerings of the
        # declaration being audited, in order (each must be one of its own termination leaves)
        self.wf_used = []

    def ind_target(self, ref):
        mind, idx = ref["mind"], ref["i"]
        if mind in BOOTSTRAP:
            b = BOOTSTRAP[mind]
            return b["types"][idx], b["ctors"][idx], b["univ"]
        r = self.ok.get(mind) or self.pending_inds.get(mind)
        if r is not None and r["status"] in ("TRANSLATED_AND_CHECKED", "PENDING_KERNEL_CHECKED") and self.decls[mind]["kind"] == "inductive":
            body = self.decls[mind]["bodies"][idx]
            t, cs = generated_names(mind, body["name"], [c["name"] for c in body["ctors"]])
            n = len(ind_params(self.decls[mind], r)[0])
            if mind in self.pending_inds:
                t, cs = pending_target_name(t[len("Rocq."):]), [pending_target_name(c[len("Rocq."):]) for c in cs]
            return t, cs, ("mono" if n == 0 else ("params", n))
        raise Mismatch(f"inductive {mind} has no audited realisation")

    def head(self, t):
        """(expected const name, universe rule) for a global head."""
        k = t["k"]
        if k == "const" and t["c"] in self.proved:
            r = self.proved[t["c"]]
            n = len(r.get("level_params", []))
            kp = poly_count(self.decls[t["c"]], r)
            if len(t["u"]) != kp:
                raise Mismatch(f"universe instance of {len(t['u'])} levels on {t['c']}, which has {kp} universe variables")
            if kp:
                return target_name(t["c"]), ("poly", kp, n, t["u"])
            return target_name(t["c"]), ("mono" if n == 0 else ("params", n))
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
            if x[0] == "bvar" and len(x) > 5:      # a field with its course-of-values result term
                out.append(("bvar", x[1] + n, *x[2:5], lift(x[5], n)))
            elif x[0] == "bvar":
                out.append(("bvar", x[1] + n, *x[2:]))
            elif x[0] == "tgt":
                out.append(("tgt", lift(x[1], n)))
            elif x[0] == "expect":
                out.append(("expect", x[1], Auditor.shift(x[2], n), *x[3:]))
            elif x[0] == "accrec":           # the induction hypothesis' position moves with the binders
                out.append(("accrec", dict(x[1], ih=x[1]["ih"] + n)))
            elif x[0] == "hyp":              # statement mode: a pending prerequisite's hypothesis
                out.append(("hyp", x[1], x[2] + n))
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
        # rule P, term level (docs/PROP_LIFT.md §3): in a row reporting coercions, `PULift.up X t` /
        # `PULift.down X t` with `PULift.{_, 0}` (X a proposition: the kernel checks t's type against it)
        # stands for t, the source term at that position (C1: up/down are the two sides of PULift X ≃ X)
        if COERCE[0]:
            inner = peel_lift_coercion(e)
            if inner is not None:
                return self.check(s, inner, path + ["lift"], env)
            # (η: a source function used at a function type differing by lifts is η-expanded, its
            # arguments and result coerced; the head is compared under the n extra binders, so it cannot
            # mention them)
            if e["k"] == "lam" and k not in ("lam", "cast"):
                eta = peel_eta(e)
                if eta is not None:
                    head, n = eta
                    return self.check(s, head, path + ["eta"], Auditor.shift(env, n))
        if k == "phantom_sort":           # rule Q-a: a phantom check's sort argument, lowered per occurrence
            if e["k"] != "sort":
                raise Mismatch(f"{path}: a phantom check's sort argument is not a sort")
            return
        if k == "cast":
            # the cast's term as is; otherwise a cast repair around it (a source convoy match has the
            # same outer shape as a repair, so the direct comparison comes first)
            try:
                return C(s["t"], e, "cast")
            except Mismatch:
                inner = self.peel_cast_repair(e, path)
                if inner is e:
                    raise
                return C(s["t"], inner, "cast")
        if k == "rel":
            if s["i"] >= len(env):
                raise Mismatch(f"{path}: source rel {s['i']} out of scope")
            want = env[s["i"]]
            if want[0] == "expect":       # a source variable that denotes a source term here
                return self.check(want[1], e, path + ["as-term"], want[2])
            if want[0] == "castpat":      # M6 convoy: the major of the return clause is the cast
                if not want[1](e):
                    raise Mismatch(f"{path}: the return clause's major is not the convoy cast")
                return
            if want[0] == "tgt":          # a target expression forced by typing (constructor parameters)
                if e != want[1]:
                    raise Mismatch(f"{path}: expected the parameter {want[1]}, found {e}")
                return
            if want[0] == "selfp":        # a pending block's self reference: applied to its hypotheses
                head = self.strip_hyp_args(e, want[3], env, path)
                if head != {"k": "const", "n": want[1], "u": want[2]}:
                    raise Mismatch(f"{path}: source rel {s['i']} should be {want[1]} applied to its hypotheses")
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
        if k == "app" and s["f"]["k"] == "rel" and s["f"]["i"] < len(env) and env[s["f"]["i"]][0] == "accrec":
            return self.check_rec_call_acc(s, e, path, env, env[s["f"]["i"]][1])
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

    def peel_cast_repair(self, e, path, depth=0):
        """M6 cast repair: a source cast may be translated as I.rec (lam v. A v -> T v) minors v c, a
        transport of the translated source term c along case analysis, into a proposition (the
        recursor's motive level is 0: a proof, computationally irrelevant). Every minor must end in its
        last binder h (the transported proof itself) or in a nested repair of h, so no other proof
        can replace the source's. Returns c (audited by the caller against the source term)."""
        if e.get("k") != "app" or depth > 8:
            return e
        head, spine = self.unspine(e["f"])
        if head.get("k") != "const" or not head["n"].endswith(".rec") or not head["u"] or head["u"][0] != {"k": "zero"}:
            return e
        rec = (self.recursors or {}).get(head["n"])
        if rec is None or rec["num_indices"] != 0 or rec["num_motives"] != 1:
            return e
        np, nm = rec["num_params"], rec["num_minors"]
        if len(spine) != np + 1 + nm + 1 or spine[-1].get("k") != "bvar":
            return e
        mot = spine[np]
        if mot.get("k") != "lam" or mot["b"].get("k") != "forall":
            return e
        for k in range(nm):
            m = spine[np + 1 + k]
            n = 0
            while m.get("k") == "lam":
                m, n = m["b"], n + 1
            leaf = m if m == {"k": "bvar", "i": 0} else self.peel_cast_repair(m, path, depth + 1)
            if n == 0 or leaf != {"k": "bvar", "i": 0}:
                raise Mismatch(f"{path}: cast repair minor {k} does not end in the transported source proof")
        return e["a"]

    @staticmethod
    def hyp_index(env, name, path):
        return Auditor.hyp_indices(env, name, path)[0]

    @staticmethod
    def hyp_indices(env, name, path):
        """P3: every hypothesis of the prerequisite (one per universe instance); the kernel checked that
        the one used has the right type."""
        out = [x[2] for x in env if x[0] == "hyp" and x[1] == name]
        if not out:
            raise Mismatch(f"{path}: reference to the unproved prerequisite {name} outside a pending declaration "
                           f"that has it as a hypothesis")
        return out

    def strip_hyp_args(self, e, hs, env, path):
        """A pending inductive (type or constructor) is applied to the hypotheses of its own telescope
        first: returns the head after checking them."""
        for h in reversed(hs):
            js = self.hyp_indices(env, h, path)
            if e.get("k") != "app" or e["a"] not in [{"k": "bvar", "i": j} for j in js]:
                raise Mismatch(f"{path}: pending inductive not applied to the hypothesis of {h}")
            e = e["f"]
        return e

    def check_prereq_ref(self, s, e, path, env):
        """Statement mode: a source reference to a leaf (proof task) is its hypothesis; a reference to a
        pending definition is its artifact applied to the hypotheses of its telescope, in order."""
        c = s["c"]
        if s.get("u"):
            raise Mismatch(f"{path}: universe-polymorphic prerequisite {c}")
        if c in self.leaves:
            js = self.hyp_indices(env, c, path)
            if e not in [{"k": "bvar", "i": j} for j in js]:
                raise Mismatch(f"{path}: {c} must be one of its hypotheses (bvar {js}), found {e.get('k')}")
            return
        tgt, hs = self.pending[c]
        cur = e
        for h in reversed(hs):
            js = self.hyp_indices(env, h, path)
            if cur.get("k") != "app" or cur["a"] not in [{"k": "bvar", "i": j} for j in js]:
                raise Mismatch(f"{path}: pending {c} must be applied to the hypothesis of {h}")
            cur = cur["f"]
        if cur.get("k") != "const" or cur["n"] != tgt:
            raise Mismatch(f"{path}: expected the pending artifact {tgt}, found {cur.get('n', cur.get('k'))}")

    def check_head(self, s, e, path, env=()):
        if s["k"] == "const" and (s["c"] in self.leaves or s["c"] in self.pending):
            return self.check_prereq_ref(s, e, path, env)
        h = self.head(s) if s["k"] in ("const", "ind", "construct") else None
        if h is None:
            return self.check(s, e, path, env)
        name, univ = h
        if s["k"] in ("ind", "construct") and s["ind"]["mind"] in self.pending_inds:
            e = self.strip_hyp_args(e, self.pending_inds[s["ind"]["mind"]].get("pending_hypotheses") or [], env, path)
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

    def split_nested(self, head, spine, npar, nmain, path):
        """M6 nested inductive (one type, trivial auxiliary eliminations): Lean's recursor takes one
        motive per auxiliary type after the main motive and one minor per auxiliary constructor after
        the main minors; they must be lam .. PUnit and lam .. PUnit.unit. Returns the spine without
        them, the auxiliary motives (for the binder check), and whether the block is nested."""
        rec = (self.recursors or {}).get(head.get("n"))
        if rec is None or rec["num_motives"] == 1:
            return spine, [], False
        na, nn = rec["num_motives"] - 1, rec["num_minors"] - nmain
        aux_m = spine[npar + 1:npar + 1 + na]
        aux_n = spine[npar + 1 + na + nmain:npar + 1 + na + nmain + nn]
        for x, want in [(m, "PUnit") for m in aux_m] + [(m, "PUnit.unit") for m in aux_n]:
            while x.get("k") == "lam":
                x = x["b"]
            if x.get("k") != "const" or x.get("n") != want:
                raise Mismatch(f"{path}: an auxiliary (nested) motive or minor is not the trivial {want}")
        return spine[:npar + 1] + spine[npar + 1 + na:npar + 1 + na + nmain] + spine[npar + 1 + na + nmain + nn:], aux_m, True

    def recursive_fields(self, ref, ctor, nested=False):
        """Number of recursive constructor arguments (Lean adds one recursive result for each)."""
        return len(self.recursive_positions(ref, ctor, nested))

    def recursive_positions(self, ref, ctor, nested=False):
        """Outermost-first positions of the recursive constructor arguments (with nested, also the
        fields of an auxiliary type, e.g. list I, which have a recursive result in Lean)."""
        mib = self.decls[ref["mind"]]
        if len(mib["bodies"]) != 1:
            raise Mismatch("UNAUDITABLE: case on a mutual block")
        args = list(reversed(mib["bodies"][ref["i"]]["ctors"][ctor]["args"]))  # outermost first
        pos = []
        for p, a in enumerate(args):
            if nested and mentions_src_rel(a["ty"], p + mib["npars"]):
                pos.append(p)
                continue
            t, depth = a["ty"], 0
            while t["k"] == "prod":
                t, depth = t["b"], depth + 1
            while t["k"] == "app":
                t = t["f"]
            if t == {"k": "rel", "i": p + mib["npars"] + depth}:
                pos.append(p)       # M6: a functional recursive field (depth > 0) has ih : forall zs, motive (y zs)
        return pos

    def functional_positions(self, ref, ctor):
        """Outermost-first positions of the functional recursive constructor arguments."""
        mib = self.decls[ref["mind"]]
        args = list(reversed(mib["bodies"][ref["i"]]["ctors"][ctor]["args"]))
        out = []
        for p in self.recursive_positions(ref, ctor):
            if args[p]["ty"]["k"] == "prod":
                out.append(p)
        return out

    @staticmethod
    def strip_lams(e, n, path):
        for _ in range(n):
            if e["k"] != "lam":
                raise Mismatch(f"{path}: expected {n} binders")
            e = e["b"]
        return e

    def nonuniform(self, ref):
        """Number of non-uniform parameters of a source block (native nparams_rec, round-trip checked)."""
        mib = self.decls[ref["mind"]]
        return mib["npars"] - (mib.get("native") or {}).get("nparams_rec", mib["npars"])

    def check_case(self, s, e, path, env):
        ref = s["ci"]["ind"]
        c = s["c"]
        if c["k"] == "rel" and c["i"] < len(env) and env[c["i"]][0] == "bvar" and len(env[c["i"]]) > 5:
            return self.check_case_cov(s, e, path, env, env[c["i"]][5])
        if c["k"] == "rel" and c["i"] < len(env) and env[c["i"]][0] == "expect" and len(env[c["i"]]) > 3:
            # M6 ι-generalized fix lowering: in minor k the decreasing argument is C_k params fields,
            # so a match on it is its branch k, with the branch's fields := the minor's fields
            _, _, cenv, (tag, k, nf, xref) = env[c["i"]]
            if tag != "iota" or ref != xref:
                raise Mismatch(f"{path}: ι-reduced match on a different inductive")
            br = s["brs"][k]
            if len(br["ctx"]) != nf:
                raise Mismatch(f"{path}: ι-reduction: branch {k} binds {len(br['ctx'])} names for {nf} fields")
            fenv = [("bvar", cenv[q][1], "field", k, q) + ((cenv[q][5],) if len(cenv[q]) > 5 else ()) for q in range(nf)]
            return self.check(br["body"], e, path + [f"iota{k}"], fenv + list(env))
        if self.nonuniform(ref):
            return self.check_case_nu(s, e, path, env)
        tname, _, _ = self.ind_target(ref)
        spine = []
        cur = e
        while cur["k"] == "app":
            spine.append(cur["a"])
            cur = cur["f"]
        spine.reverse()
        # B: in a termination lowering, a match whose branches contain a recursive call carries its
        # scrutinee equation: I.rec params (lam z. forall h : scrut = z. RET) minors z' (Eq.refl scrut),
        # each minor binding one more variable (h) that the source branch does not
        fi = next((i for i, x in enumerate(env) if x[0] == "accrec" and x[1].get("convoy")), None)
        convoy = fi is not None and any(mentions_rels(br["body"], fi + len(br["ctx"]), 1) for br in s["brs"])
        if convoy:
            if len(s["p"]["ctx"]) != 1:
                raise Mismatch(f"{path}: convoy on an indexed inductive")
            if not spine:
                raise Mismatch(f"{path}: convoy match without its equation argument")
            rh, ra = self.unspine(spine[-1])
            if rh.get("k") != "const" or rh.get("n") != "Eq.refl" or len(ra) != 2 or ra[1] != spine[-2]:
                raise Mismatch(f"{path}: convoy match not applied to Eq.refl of its scrutinee")
            spine = spine[:-1]
        if cur["k"] != "const" or cur["n"] != tname + ".rec":
            raise Mismatch(f"{path}: match must lower to {tname}.rec, found {cur.get('n', cur['k'])}")
        p, brs = s["p"], s["brs"]
        # statement mode: a pending inductive's recursor takes its hypotheses as first parameters
        hs = (self.pending_inds.get(ref["mind"]) or {}).get("pending_hypotheses") or []
        for i, h in enumerate(hs):
            if i >= len(spine) or spine[i] != {"k": "bvar", "i": self.hyp_index(env, h, path)}:
                raise Mismatch(f"{path}: {tname}.rec parameter {i} is not the hypothesis of {h}")
        npar, nidx = len(p["params"]) + len(hs), len(p["ctx"]) - 1
        spine, aux, nested = self.split_nested(cur, spine, npar, len(brs), path)
        if len(spine) != npar + 1 + len(brs) + nidx + 1:
            raise Mismatch(f"{path}: {tname}.rec applied to {len(spine)} arguments")
        for i, a in enumerate(p["params"]):
            self.check(a, spine[len(hs) + i], path + [f"param{i}"], env)
        motive = self.strip_lams(spine[npar], len(p["ctx"]), path + ["motive"])
        if convoy:
            mh, ma = self.unspine(motive.get("t", {})) if motive.get("k") == "forall" else ({}, [])
            if mh.get("n") != "Eq" or len(ma) != 3 or ma[1] != lift(spine[-1], len(p["ctx"])) or ma[2] != {"k": "bvar", "i": 0}:
                raise Mismatch(f"{path}: convoy motive is not forall h : scrutinee = z, RET")
            self.check(p["ret"], motive["b"], path + ["motive"], self.shift(self.push(env, len(p["ctx"])), 1))
        else:
            self.check(p["ret"], motive, path + ["motive"], self.push(env, len(p["ctx"])))
        self.check_rec_binders(cur, spine, npar, len(brs), nidx, path,
                               [self.recursive_fields(ref, k, nested) for k in range(len(brs))],
                               [len(br["ctx"]) for br in brs], 1 if convoy else 0, aux)
        for k, br in enumerate(brs):
            nf, nih = len(br["ctx"]), self.recursive_fields(ref, k, nested)
            body = self.strip_lams(spine[npar + 1 + k], nf + nih + (1 if convoy else 0), path + [f"minor{k}"])
            self.check(br["body"], body, path + [f"minor{k}"], self.shift(self.push(env, nf), nih + (1 if convoy else 0)))
        # Indices of the major premise are forced by the recursor's (kernel-checked) type.
        self.check(s["c"], spine[-1], path + ["major"], env)

    def check_case_cov(self, s, e, path, env, res):
        """M6 course-of-values: match z (z with a known result r_z) ->
           I.rec params (lam z. forall h, RET) minors z r_z, minor_k = lam fields ihs h. B_k, the recursive
           field m's result being proj0 (proj1^m (proj1 h)); h's type is forced by the application to r_z."""
        ref = s["ci"]["ind"]
        tname, _, _ = self.ind_target(ref)
        if e["k"] != "app" or e["a"] != res:
            raise Mismatch(f"{path}: course-of-values match must pass its scrutinee's result {res}")
        head, spine = self.unspine(e["f"])
        if head.get("k") != "const" or head.get("n") != tname + ".rec":
            raise Mismatch(f"{path}: match must lower to {tname}.rec, found {head.get('n', head['k'])}")
        p, brs = s["p"], s["brs"]
        npar, nidx = len(p["params"]), len(p["ctx"]) - 1
        if nidx or self.nonuniform(ref) or len(spine) != npar + 1 + len(brs) + 1:
            raise Mismatch(f"{path}: UNAUDITABLE course-of-values match shape")
        for i, a in enumerate(p["params"]):
            self.check(a, spine[i], path + [f"param{i}"], env)
        motive = self.strip_lams(spine[npar], 1, path + ["motive"])
        if motive["k"] != "forall":
            raise Mismatch(f"{path}: course-of-values motive is not a function of the scrutinee's result")
        self.check(p["ret"], motive["b"], path + ["motive"], self.shift(self.push(env, 1), 1))
        nihs = [self.recursive_fields(ref, k) for k in range(len(brs))]
        self.check_rec_binders(head, spine, npar, len(brs), 0, path, nihs, [len(br["ctx"]) for br in brs], 1)
        for k, br in enumerate(brs):
            nf, nih = len(br["ctx"]), nihs[k]
            if self.functional_positions(ref, k):
                raise Mismatch(f"{path}: UNAUDITABLE course-of-values match with a functional field")
            body = self.strip_lams(spine[npar + 1 + k], nf + nih + 1, path + [f"minor{k}"])
            rq = [nf - 1 - pp for pp in self.recursive_positions(ref, k)]
            benv = []
            for q in range(nf):
                ent = ("bvar", q + nih + 1, "field", "cov", q)
                if q in rq:
                    r_ = {"k": "proj", "s": "PProd", "i": 1, "e": {"k": "bvar", "i": 0}}
                    for _ in range(rq.index(q)):
                        r_ = {"k": "proj", "s": "PProd", "i": 1, "e": r_}
                    ent = ent + ({"k": "proj", "s": "PProd", "i": 0, "e": r_},)
                benv.append(ent)
            self.check(br["body"], body, path + [f"minor{k}"], benv + self.shift(list(env), nf + nih + 1))
        self.check(s["c"], spine[-1], path + ["major"], env)

    def check_case_nu(self, s, e, path, env):
        """M6 convoy lowering of a match on a block with one non-uniform parameter u (a Lean index):
           I.rec P (λ i' idx h, ∀ e : u = i', RET[a0 := cast]) minors u idx major (Eq.refl u), with
           cast = Eq.rec U i' (λ y w, I P y idx) h u (Eq.rec U u (λ y w, y = u) (Eq.refl U u) i' e) and
           minor_k = λ i' fs ihs e, Eq.rec U u M (λ fs e0, B_k) i' e fs e  (M forced by kernel typing)."""
        ref = s["ci"]["ind"]
        tname, ctors, _ = self.ind_target(ref)
        if self.nonuniform(ref) != 1:
            raise Mismatch(f"{path}: UNAUDITABLE match with {self.nonuniform(ref)} non-uniform parameters")
        head, spine = self.unspine(e)
        if head["k"] != "const" or head["n"] != tname + ".rec":
            raise Mismatch(f"{path}: match must lower to {tname}.rec, found {head.get('n', head['k'])}")
        p, brs = s["p"], s["brs"]
        npar, nridx, nmin = len(p["params"]), len(p["ctx"]) - 1, len(brs)
        nu = npar - 1
        if len(spine) != nu + 1 + nmin + 1 + nridx + 1 + 1:
            raise Mismatch(f"{path}: {tname}.rec applied to {len(spine)} arguments (convoy shape)")
        for i in range(nu):
            self.check(p["params"][i], spine[i], path + [f"param{i}"], env)
        ut = spine[nu + 1 + nmin]
        self.check(p["params"][nu], ut, path + ["nonuniform"], env)
        self.check(s["c"], spine[-2], path + ["major"], env)
        rf, rargs = self.unspine(spine[-1])
        if rf["k"] != "const" or rf["n"] != "Eq.refl" or len(rargs) != 2 or rargs[1] != ut:
            raise Mismatch(f"{path}: convoy equation must be applied to Eq.refl u")
        U = rargs[0]
        # motive: λ i' idx.. h, ∀ e : Eq U (u) i', RET with a0 the cast
        nb = 1 + nridx + 1
        mb = self.strip_lams(spine[nu], nb, path + ["motive"])
        if mb["k"] != "forall":
            raise Mismatch(f"{path}: convoy motive lacks its equation binder")
        eq_h, eq_a = self.unspine(mb["t"])
        if eq_h.get("n") != "Eq" or eq_a != [lift(U, nb), lift(ut, nb), {"k": "bvar", "i": nb - 1}]:
            raise Mismatch(f"{path}: convoy equation binder is not u = i'")
        # expected cast at depth nb + 1 (below λ i' idx h and ∀ e): bvars i' = nb, h = 1, e = 0
        params_t = [lift(spine[i], nb + 1) for i in range(nu)]
        def is_cast(t):
            h_, a_ = self.unspine(t)
            if h_.get("n") != "Eq.rec" or len(a_) != 6:
                return False
            if a_[0] != lift(U, nb + 1) or a_[1] != {"k": "bvar", "i": nb} or a_[3] != {"k": "bvar", "i": 1} \
                    or a_[4] != lift(ut, nb + 1):
                return False
            m = a_[2]
            if m["k"] != "lam" or m["b"]["k"] != "lam":
                return False
            ih, ia = self.unspine(m["b"]["b"])
            # below λ i' idx.. h, ∀ e, λ y w: Rocq index j (outermost first, j = 1..n) is bvar n - j + 4
            if ih.get("n") != tname or [lift(x, 2) for x in params_t] != ia[:nu] or ia[nu] != {"k": "bvar", "i": 1} \
                    or ia[nu + 1:] != [{"k": "bvar", "i": nridx - j + 4} for j in range(1, 1 + nridx)]:
                return False
            sh, sa = self.unspine(a_[5])
            return sh.get("n") == "Eq.rec" and len(sa) == 6 and sa[0] == lift(U, nb + 1) and sa[1] == lift(ut, nb + 1) \
                and sa[4] == {"k": "bvar", "i": nb} and sa[5] == {"k": "bvar", "i": 0}
        # rel 0 = the major binder a0 -> the cast; rel 1.. = Rocq indices, innermost first (bvar 2..)
        menv = [("castpat", is_cast)] + [("bvar", 2 + j) for j in range(nridx)] + self.shift(list(env), nb + 1)
        self.check(p["ret"], mb["b"], path + ["motive"], menv)
        # minors
        for kk, br in enumerate(brs):
            nf = len(br["ctx"])
            nih = self.recursive_fields(ref, kk)
            mn = self.strip_lams(spine[nu + 1 + kk], 1 + nf + nih + 1, path + [f"minor{kk}"])
            depth = 1 + nf + nih + 1
            eh, ea = self.unspine(mn)
            # Eq.rec U u M reflE i' e  fields(1..) e
            if eh.get("n") != "Eq.rec" or len(ea) != 6 + nf + 1:
                raise Mismatch(f"{path}: minor {kk} is not the convoy elimination")
            if ea[0] != lift(U, depth) or ea[1] != lift(ut, depth) or ea[4] != {"k": "bvar", "i": depth - 1} \
                    or ea[5] != {"k": "bvar", "i": 0} or ea[-1] != {"k": "bvar", "i": 0}:
                raise Mismatch(f"{path}: minor {kk}: convoy elimination arguments differ")
            for q in range(nf):           # the constructor's own fields, passed on unchanged
                if ea[6 + q] != {"k": "bvar", "i": depth - 2 - q}:
                    raise Mismatch(f"{path}: minor {kk}: field {q} not passed on")
            refl = self.strip_lams(ea[3], nf + 1, path + [f"minor{kk} refl"])
            benv = [("bvar", 1 + q) for q in range(nf)] + self.shift(list(env), depth + nf + 1)
            self.check(br["body"], refl, path + [f"minor{kk}"], benv)

    def check_rec_binders(self, head, spine, npar, nmin, nidx, path, nihs, nfs, nq, aux=()):
        """Recursor identity/levels (kernel metadata) and the binder types of the motive and of
        every minor premise, reconstructed from the kernel-checked recursor type instantiated
        with the actual parameters and motive, compared modulo beta and binder names."""
        rec = self.recursors.get(head["n"]) if self.recursors is not None else None
        if rec is None:
            raise Mismatch(f"{path}: no kernel metadata for recursor {head['n']} (fail closed)")
        if len(head["u"]) != len(rec["level_params"]):
            raise Mismatch(f"{path}: {head['n']} applied to {len(head['u'])} universe levels, kernel expects {len(rec['level_params'])}")
        naux_n = rec["num_minors"] - nmin if aux else 0
        if (rec["num_params"], rec["num_indices"], rec["num_minors"], rec["num_motives"]) != (npar, nidx, nmin + naux_n, 1 + len(aux)):
            raise Mismatch(f"{path}: recursor shape differs from the source match")
        if [rec["rule_nfields"][k] for k in range(nmin)] != nfs:
            raise Mismatch(f"{path}: constructor field counts differ from the kernel recursor rules")
        ty = inst_levels(rec["type"], dict(zip(rec["level_params"], head["u"])))
        ty = inst_forall(ty, spine[:npar], path)
        mdoms, _ = foralls(ty, 1, path + ["motive"])
        want, _ = foralls(mdoms[0], nidx + 1, path + ["motive type"])
        got, _ = lam_domains(spine[npar], nidx + 1, path + ["motive"])
        for i, (w, g) in enumerate(zip(want, got)):
            if not self.same_mod_beta_delta(w, g):
                raise Mismatch(f"{path}: motive binder {i} type differs from the recursor's")
        ty = inst_forall(ty, [spine[npar]] + list(aux), path)
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
                if not self.same_mod_beta_delta(w, g):
                    raise Mismatch(f"{path}: minor {k} binder {i} type differs from the recursor's")
            ty = subst(ty["b"], spine[npar + 1 + k])

    def unfold_src_alias(self, t, fuel=8):
        """A source type whose head is a transparent constant (a definition alias such as Tauto's
        clause or TFormula := GFormula …), delta-beta-unfolded until its head is not one: the
        inductive the translator reaches by whnf."""
        for _ in range(fuel):
            h = t["f"] if t.get("k") == "app" else t
            if h.get("k") != "const" or h["c"] not in self.ir_bodies:
                return t
            t = src_flatten_apps(beta_app(self.ir_bodies[h["c"]], t["args"] if t.get("k") == "app" else []))
        return t

    def same_mod_beta_delta(self, a, b, fuel=6):
        """Equal modulo beta and binder names, unfolding a head that is an accepted transparent
        definition (its audited target value, at the reference's universe arguments) when needed."""
        if same_mod_beta(a, b):
            return True
        for _ in range(fuel):
            a2, b2 = self.unfold_head(beta(a)), self.unfold_head(beta(b))
            if a2 is None and b2 is None:
                return False
            a, b = a2 or a, b2 or b
            if same_mod_beta(a, b):
                return True
        return False

    def unfold_head(self, e):
        h, sp = self.unspine(e)
        if h.get("k") != "const" or h["n"] not in self.defs:
            return None
        lps, val = self.defs[h["n"]]
        if len(lps) != len(h["u"]):
            return None
        v = inst_levels(val, dict(zip(lps, h["u"])))
        for x in sp:
            v = {"k": "app", "f": v, "a": x}
        return beta(v)

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
        # M6 δβ: constants to which the block passes its own functions are inlined; ζ: let-bound
        # partial applications of the block's functions are inlined (both definitional)
        need = [d["rarg"] + 1 for d in reversed(s["defs"])]
        s = dict(s, defs=[dict(d, body=zeta_fix_lets(inline_rec_args(d["body"], need, self.ir_bodies), len(s["defs"])))
                          for d in s["defs"]])
        if len(s["defs"]) != 1:
            return self.check_fix_mutual(s, e, path, env)
        if s["idx"] != 0:
            raise Mismatch(f"{path}: UNAUDITABLE fixpoint index")
        d = s["defs"][0]
        r = d["rarg"]
        lams, b = [], d["body"]
        while b["k"] == "lam":
            lams.append(b)
            b = b["b"]
        nl = len(lams)
        # M6 accessibility lowering (structural recursion on a proof, into data)
        tgt_body = e
        for _ in range(nl):
            if tgt_body["k"] != "lam":
                break
            tgt_body = tgt_body["b"]
        th, tsp = self.unspine(tgt_body)
        if th.get("k") == "const" and th.get("n") == "Acc.rec":
            # B: well-foundedness given by a termination obligation (a hypothesis, or its final
            # theorem), not constructed: the termination lowering of a recursion on data
            if STATEMENT_MODE[0] and len(tsp) > 5 and self.wf_term_of(tsp[5], env, nl) is not None:
                return self.check_fix_acc(s, e, path, env, wf=True)
            return self.check_fix_acc(s, e, path, env)
        # M6 course-of-values: (I.rec params (λ x, PProd (M x) (Below x)) minors x).1 G Q
        cov = th.get("k") == "proj" and th.get("s") == "PProd" and th.get("i") == 0
        # The body is a match on the decreasing argument (M3c), or any term (M6 ι-generalized
        # lowering: each minor is the whole body, matches on the decreasing argument ι-reduced).
        iota = not (b["k"] == "case" and b["c"] == {"k": "rel", "i": nl - 1 - r})
        senv = [("forbid",)] + list(env)      # the source binds f; the target does not
        cur = e
        for i, lam in enumerate(lams):
            if cur["k"] != "lam":
                raise Mismatch(f"{path}: expected {nl} lambdas")
            self.check(lam["ty"], cur["t"], path + [f"lam{i}"], senv)
            senv = self.push(senv)
            cur = cur["b"]
        # Index positions: earlier parameters that are indices of the decreasing argument's type.
        xty = self.unfold_src_alias(lams[r]["ty"])
        xargs = []
        while xty["k"] == "app":
            xargs = xty["args"] + xargs
            xty = xty["f"]
        if iota:
            if xty["k"] != "ind":
                raise Mismatch(f"{path}: UNAUDITABLE fixpoint shape (decreasing argument not of an inductive type)")
            ref = xty["ind"]
            npar = self.decls[ref["mind"]]["npars"]
            if self.nonuniform(ref):
                raise Mismatch(f"{path}: UNAUDITABLE ι-generalized fixpoint on a non-uniform inductive")
            if len(self.decls[ref["mind"]]["bodies"]) != 1:
                raise Mismatch(f"{path}: UNAUDITABLE fixpoint on a mutual block")
            branches = [(len(c["args"]), None) for c in self.decls[ref["mind"]]["bodies"][ref["i"]]["ctors"]]
            nidx = len(xargs) - npar
        else:
            ref = b["ci"]["ind"]
            npar = b["ci"]["npar"]
            branches = [(len(br["ctx"]), br["body"]) for br in b["brs"]]
            nidx = len(b["p"]["ctx"]) - 1
        # M6: non-uniform parameters are Lean indices (the leading ones) and the leading fields of
        # Lean's constructors; Rocq's match counts them as parameters, its branches bind the others
        nu = 0 if iota else self.nonuniform(ref)
        rnpar, npar, nidx = npar, npar - nu, nidx + nu
        idx_pos = {r - 1 - a["i"] for a in xargs[npar:] if a["k"] == "rel" and a["i"] < r}
        # Leading arguments changed by recursive calls (not indices) are generalized in the motive.
        gpos = sorted(changed_params(d["body"], nl, r) - idx_pos)
        ng = len(gpos)
        head, spine = self.unspine(cur)
        if cov:
            if nu or nidx:
                raise Mismatch(f"{path}: UNAUDITABLE course-of-values recursion on an indexed or non-uniform inductive")
            head, spine = self.unspine(head["e"])[0], self.unspine(head["e"])[1] + spine   # G Q after the major
        tname, _, _ = self.ind_target(ref)
        if head["k"] != "const" or head["n"] != tname + ".rec":
            raise Mismatch(f"{path}: fixpoint must lower to {tname}.rec")
        nmin, nq = len(branches), nl - r - 1
        spine, aux, nested = self.split_nested(head, spine, npar, nmin, path)
        if nested and cov:
            raise Mismatch(f"{path}: UNAUDITABLE course-of-values recursion on a nested inductive")
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
        if nu and any(not (a["k"] == "rel" and a["i"] < r) for a in xargs[npar:npar + nu]):
            raise Mismatch(f"{path}: UNAUDITABLE non-uniform parameter of the decreasing argument that is not a leading argument")
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
        if cov:
            ph, pa = self.unspine(mbody)
            if ph.get("k") != "const" or ph.get("n") != "PProd" or len(pa) != 2:
                raise Mismatch(f"{path}: course-of-values motive is not PProd (M x) (Below x)")
            bh, ba = self.unspine(pa[1])
            if bh.get("k") != "const" or bh.get("n") != tname + ".rec" or len(ba) != npar + 2 + nmin \
                    or ba[-1] != {"k": "bvar", "i": 0} or any(ba[i] != lift(spine[i], 1) for i in range(npar)):
                raise Mismatch(f"{path}: course-of-values Below is not {tname}.rec over the motive's argument")
            mbody = pa[0]                     # Below's minors are kernel-forced by the audited chains
        for j, i in enumerate(gpos):          # ∀ G: the generalized arguments' source types
            if mbody["k"] != "forall":
                raise Mismatch(f"{path}: motive lacks the generalized argument {i}")
            self.check(lams[i]["ty"], mbody["t"], path + [f"motive g{j}"], lead_env(i, j))
            mbody = mbody["b"]
        self.check(fty, mbody, path + ["motive body"], menv)
        self.check_rec_binders(head, spine, npar, nmin, nidx, path,
                               [len(self.recursive_positions(ref, k, nested)) for k in range(nmin)],
                               [nf + nu for nf, _ in branches], 0 if cov else ng + nq, aux)
        for k, (nf, bbody) in enumerate(branches):
            rpos = self.recursive_positions(ref, k, nested)
            nih = len(rpos)
            if cov:
                if self.functional_positions(ref, k):
                    raise Mismatch(f"{path}: UNAUDITABLE course-of-values recursion with a functional field")
                vh, va = self.unspine(self.strip_lams(spine[npar + 1 + k], nf + nih, path + [f"minor{k}"]))
                if vh.get("k") != "const" or vh.get("n") != "PProd.mk" or len(va) != 4:
                    raise Mismatch(f"{path}: course-of-values minor {k} is not a pair")
                chain = va[3]                  # ⟨ih_1, ⟨ih_2, … PUnit.unit⟩⟩ in field order
                for m in range(nih):
                    ch, ca = self.unspine(chain)
                    if ch.get("k") != "const" or ch.get("n") != "PProd.mk" or len(ca) != 4 or ca[2] != {"k": "bvar", "i": nih - 1 - m}:
                        raise Mismatch(f"{path}: course-of-values minor {k}: the below chain is not the recursive results in order")
                    chain = ca[3]
                if chain.get("k") != "const" or chain.get("n") != "PUnit.unit":
                    raise Mismatch(f"{path}: course-of-values minor {k}: the below chain does not end in PUnit.unit")
                body = self.strip_lams(va[2], ng + nq, path + [f"minor{k}"])
            else:
                body = self.strip_lams(spine[npar + 1 + k], nf + nu + nih + ng + nq, path + [f"minor{k}"])
            depth = nf + nu + nih + ng + nq
            nuvar = lambda t: ("bvar", nf + (nu - 1 - t) + nih + ng + nq)   # Lean field of non-uniform parameter t
            benv = [("bvar", q + nih + ng + nq, "field", k, q) for q in range(nf)]   # q: innermost-first
            if cov:                                  # recursive field q: its result is its ih (a pair)
                rq = [nf - 1 - p for p in rpos]
                benv = [x + ({"k": "bvar", "i": nih - 1 - rq.index(x[4]) + ng + nq},) if x[4] in rq else x for x in benv]
            # In branch k (run at every recursion depth) the decreasing argument denotes the
            # constructor applied to the parameters and fields, and its index variables denote that
            # constructor's indices (source `ctor.indices`, in the context params + fields).
            ctor_env = [("bvar", q + nih + ng + nq) for q in range(nf)] + \
                [("tgt", lift(spine[rnpar - 1 - qq], depth)) if rnpar - 1 - qq < npar else nuvar(rnpar - 1 - qq - npar)
                 for qq in range(rnpar)] + [("forbid",)]
            if cov:                                  # (fields of an ι-reduced match carry their results)
                ctor_env = [("bvar", q + nih + ng + nq, "ctor", k, q, {"k": "bvar", "i": nih - 1 - rq.index(q) + ng + nq})
                            if q in rq else ctor_env[q] for q in range(nf)] + ctor_env[nf:]
            xk = {"k": "construct", "ind": ref, "c": k, "u": []}
            if rnpar + nf:
                xk = {"k": "app", "f": xk, "args": [{"k": "rel", "i": nf + rnpar - 1 - pi} for pi in range(rnpar)]
                      + [{"k": "rel", "i": nf - 1 - pp} for pp in range(nf)]}
            cidx = [None] * nu + self.decls[ref["mind"]]["bodies"][ref["i"]]["ctors"][k]["indices"]
            for t in range(nl):                                               # a_{nl-1} .. a_0
                i = nl - 1 - t
                if i > r:
                    benv.append(("bvar", nq - 1 - (i - r - 1)))
                elif i == r:
                    benv.append(("expect", xk, ctor_env, ("iota", k, nf, ref)) if iota else ("expect", xk, ctor_env))
                elif i in gpos:
                    benv.append(("bvar", nq + ng - 1 - gpos.index(i), "gen", i))
                elif i in idx_of:
                    benv.append(nuvar(idx_of[i]) if idx_of[i] < nu else ("expect", cidx[idx_of[i]], ctor_env))
                else:
                    benv.append(("bvar", senv[t][1] + depth, "param", i))
            info = {"minor": k, "r": r, "nf": nf, "nq": nq, "rec_q": [nf - 1 - p for p in rpos], "idx_pos": idx_pos,
                    "gpos": gpos, "fun_q": [nf - 1 - p for p in self.functional_positions(ref, k)], "cov": cov, "ref": ref}
            benv.append(("rec", info))
            benv += self.shift(senv[nl + 1:], depth)
            if iota:
                self.check(b, body, path + [f"minor{k}"], benv[nf:])
            else:
                self.check(bbody, body, path + [f"minor{k}"], benv)

    def check_fix_mutual(self, s, e, path, env):
        """M6 mutual structural fixpoints over one inductive (all functions decrease on argument r,
        with the same leading argument types):
           fix f_0 .. f_{n-1} for f_j  ->  lam a_0..a_{r}  Q_j. (I.rec params motive minors idx a_r).j G Q_j
           motive  = lam idx x. PProd (forall G Q_0. T_0) (PProd .. (forall G Q_{n-1}. T_{n-1}))
           minor_k = lam fields ihs. PProd.mk _ _ (lam G Q_0. b_0k) (PProd.mk _ _ .. (lam G Q_{n-1}. b_{n-1,k}))
        `.j` is the PProd projection chain; a call f_i P y rest on a recursive field y becomes
        (ih_y).i G' rest; b_jk is branch k of b_j (a match on x) or b_j with matches on x ι-reduced."""
        defs, fidx = s["defs"], s["idx"]
        n = len(defs)
        r = defs[0]["rarg"]
        if any(d["rarg"] != r for d in defs):
            raise Mismatch(f"{path}: UNAUDITABLE mutual fixpoint (decreasing arguments at different positions)")
        peeled = []
        for d in defs:
            lams, b = [], d["body"]
            while b["k"] == "lam":
                lams.append(b)
                b = b["b"]
            if len(lams) <= r:
                raise Mismatch(f"{path}: UNAUDITABLE mutual fixpoint (decreasing argument not a leading lambda)")
            peeled.append((lams, b))
        for j in range(1, n):
            for i in range(r + 1):
                if src_anon(peeled[j][0][i]["ty"]) != src_anon(peeled[0][0][i]["ty"]):
                    raise Mismatch(f"{path}: UNAUDITABLE mutual fixpoint (argument {i} of function {j} has another type)")
        lamsF = peeled[fidx][0]
        nlF = len(lamsF)
        senv = [("forbid",)] * n + list(env)          # the source binds f_0..f_{n-1}; the target does not
        cur = e
        for i, lam in enumerate(lamsF):
            if cur["k"] != "lam":
                raise Mismatch(f"{path}: expected {nlF} lambdas")
            self.check(lam["ty"], cur["t"], path + [f"lam{i}"], senv)
            senv = self.push(senv)
            cur = cur["b"]
        xty = self.unfold_src_alias(lamsF[r]["ty"])
        xargs = []
        while xty["k"] == "app":
            xargs = xty["args"] + xargs
            xty = xty["f"]
        if xty["k"] != "ind":
            raise Mismatch(f"{path}: UNAUDITABLE mutual fixpoint (decreasing argument not of an inductive type)")
        ref = xty["ind"]
        mib = self.decls[ref["mind"]]
        if len(mib["bodies"]) != 1 or self.nonuniform(ref):
            raise Mismatch(f"{path}: UNAUDITABLE mutual fixpoint over a mutual or non-uniform inductive")
        npar = mib["npars"]
        nidx = len(xargs) - npar
        ctors = mib["bodies"][ref["i"]]["ctors"]
        nmin = len(ctors)
        idx_pos = {r - 1 - a["i"] for a in xargs[npar:] if a["k"] == "rel" and a["i"] < r}
        gacc = set()
        for j, d in enumerate(defs):
            changed_params(d["body"], len(peeled[j][0]), r, 0, gacc, n)
        gpos = sorted(gacc - idx_pos)
        ng = len(gpos)
        nqF = nlF - r - 1
        head, outer_args = self.unspine(cur)
        if len(outer_args) != ng + nqF:
            raise Mismatch(f"{path}: projection applied to {len(outer_args)} arguments, expected {ng + nqF}")
        for jj, i in enumerate(gpos):
            self.check({"k": "rel", "i": nlF - 1 - i}, outer_args[jj], path + [f"g{jj}"], senv)
        for jj in range(nqF):
            self.check({"k": "rel", "i": nqF - 1 - jj}, outer_args[ng + jj], path + [f"q{jj}"], senv)
        node = head
        for want in pprod_path(fidx, n):
            if node.get("k") != "proj" or node.get("s") != "PProd" or node.get("i") != want:
                raise Mismatch(f"{path}: function {fidx} must be projection {pprod_path(fidx, n)} of the joint recursor")
            node = node["e"]
        rhead, spine = self.unspine(node)
        tname, _, _ = self.ind_target(ref)
        if rhead["k"] != "const" or rhead["n"] != tname + ".rec":
            raise Mismatch(f"{path}: mutual fixpoint must lower to {tname}.rec")
        if len(spine) != npar + 1 + nmin + nidx + 1:
            raise Mismatch(f"{path}: {tname}.rec applied to {len(spine)} arguments")
        self.check({"k": "rel", "i": nlF - 1 - r}, spine[-1], path + ["major"], senv)
        env_r = [("forbid",)] * n + list(env)
        for _ in range(r):
            env_r = self.push(env_r)
        env_r = self.shift(env_r, nlF - r)
        for i in range(npar):
            self.check(xargs[i], spine[i], path + [f"param{i}"], env_r)
        for jj in range(nidx):
            self.check(xargs[npar + jj], spine[npar + 1 + nmin + jj], path + [f"index{jj}"], env_r)
        idx_of = {}
        for jj, a in enumerate(xargs[npar:]):
            if a["k"] == "rel" and a["i"] < r:
                idx_of[r - 1 - a["i"]] = jj

        def lead_env(i, extra):
            out = []
            for kk in reversed(range(i)):
                if kk in gpos:
                    out.append(("bvar", extra - 1 - gpos.index(kk)))
                elif kk in idx_of:
                    out.append(("bvar", extra + nidx - idx_of[kk]))
                else:
                    out.append(("bvar", (nlF - 1 - kk) + nidx + 1 + extra))
            return out + [("forbid",)] * n + self.shift(list(env), nlF + nidx + 1 + extra)
        menv = [("bvar", ng)]
        for i in reversed(range(r)):
            if i in gpos:
                menv.append(("bvar", ng - 1 - gpos.index(i)))
            else:
                menv.append(("bvar", ng + nidx - idx_of[i]) if i in idx_of else ("bvar", (nlF - 1 - i) + nidx + 1 + ng))
        menv += self.shift(list(env), nlF + nidx + 1 + ng)
        # motive: PProd chain of the components forall G Q_j. T_j
        mnode = self.strip_lams(spine[npar], nidx + 1, path + ["motive"])
        for j in range(n):
            if j + 1 < n:
                mh, ma = self.unspine(mnode)
                if mh.get("k") != "const" or mh.get("n") != "PProd" or len(ma) != 2:
                    raise Mismatch(f"{path}: motive is not a PProd of the {n} function types")
                comp, mnode = ma
            else:
                comp = mnode
            fty = defs[j]["ty"]
            for _ in range(r + 1):
                if fty["k"] != "prod":
                    raise Mismatch(f"{path}: type of function {j} has fewer than {r + 1} binders")
                fty = fty["b"]
            for jj, i in enumerate(gpos):
                if comp["k"] != "forall":
                    raise Mismatch(f"{path}: motive component {j} lacks the generalized argument {i}")
                self.check(lamsF[i]["ty"], comp["t"], path + [f"motive{j} g{jj}"], lead_env(i, jj))
                comp = comp["b"]
            self.check(fty, comp, path + [f"motive{j} body"], menv)
        nihs = [len(self.recursive_positions(ref, k)) for k in range(nmin)]
        nfs = [len(c["args"]) for c in ctors]
        self.check_rec_binders(rhead, spine, npar, nmin, nidx, path, nihs, nfs, 0)
        cidx_all = [c["indices"] for c in ctors]
        for k in range(nmin):
            nf, nih = nfs[k], nihs[k]
            rpos = self.recursive_positions(ref, k)
            vnode = self.strip_lams(spine[npar + 1 + k], nf + nih, path + [f"minor{k}"])
            for j in range(n):
                if j + 1 < n:
                    vh, va = self.unspine(vnode)
                    if vh.get("k") != "const" or vh.get("n") != "PProd.mk" or len(va) != 4:
                        raise Mismatch(f"{path}: minor {k} is not a PProd.mk tuple of the {n} branches")
                    comp, vnode = va[2], va[3]       # the component types va[0], va[1] are kernel-forced
                else:
                    comp = vnode
                lams_j, b_j = peeled[j]
                nl_j = len(lams_j)
                nq = nl_j - r - 1
                body = self.strip_lams(comp, ng + nq, path + [f"minor{k}.{j}"])
                depth = nf + nih + ng + nq
                iota = not (b_j["k"] == "case" and b_j["c"] == {"k": "rel", "i": nl_j - 1 - r})
                if not iota:
                    if b_j["ci"]["ind"] != ref or len(b_j["brs"]) != nmin or len(b_j["brs"][k]["ctx"]) != nf:
                        raise Mismatch(f"{path}: function {j}'s match disagrees with the recursor")
                benv = [("bvar", q + nih + ng + nq, "field", k, q) for q in range(nf)]
                ctor_env = [("bvar", q + nih + ng + nq) for q in range(nf)] + \
                    [("tgt", lift(spine[npar - 1 - qq], depth)) for qq in range(npar)] + [("forbid",)]
                xk = {"k": "construct", "ind": ref, "c": k, "u": []}
                if npar + nf:
                    xk = {"k": "app", "f": xk, "args": [{"k": "rel", "i": nf + npar - 1 - pi} for pi in range(npar)]
                          + [{"k": "rel", "i": nf - 1 - pp} for pp in range(nf)]}
                for t in range(nl_j):
                    i = nl_j - 1 - t
                    if i > r:
                        benv.append(("bvar", nq - 1 - (i - r - 1)))
                    elif i == r:
                        benv.append(("expect", xk, ctor_env, ("iota", k, nf, ref)) if iota else ("expect", xk, ctor_env))
                    elif i in gpos:
                        benv.append(("bvar", nq + ng - 1 - gpos.index(i), "gen", i))
                    elif i in idx_of:
                        benv.append(("expect", cidx_all[k][idx_of[i]], ctor_env))
                    else:
                        benv.append(("bvar", (nlF - 1 - i) + depth, "param", i))
                for fi in reversed(range(n)):                 # rel nl_j is f_{n-1}, the innermost
                    benv.append(("rec", {"minor": k, "r": r, "nf": nf, "nq": nq, "rec_q": [nf - 1 - p for p in rpos],
                                         "idx_pos": idx_pos, "gpos": gpos, "fn": fi, "nfn": n,
                                         "fun_q": [nf - 1 - p for p in self.functional_positions(ref, k)]}))
                benv += self.shift(list(env), nlF + depth)
                if iota:
                    self.check(b_j, body, path + [f"minor{k}.{j}"], benv[nf:])
                else:
                    self.check(b_j["brs"][k]["body"], body, path + [f"minor{k}.{j}"], benv)

    def wf_term_of(self, wf, env, depth):
        """B: the termination obligation a well-foundedness argument `T Γ.. x` comes from: T is the
        hypothesis of a termination leaf (env entry ("hyp", leaf, j), `depth` target binders below the
        env), or a proved leaf's final theorem; Γ are bound variables. None otherwise."""
        head, args = self.unspine(wf)
        if not args or any(a.get("k") != "bvar" for a in args):
            return None
        if head.get("k") == "bvar":
            for x in env:
                if x[0] == "hyp" and x[2] + depth == head["i"] and "__rocq2lean_termination_" in x[1]:
                    return x[1]
            return None
        if head.get("k") == "const":
            for leaf in self.proved:
                if "__rocq2lean_termination_" in leaf and head["n"] == target_name(leaf):
                    return leaf
        return None

    def check_fix_acc(self, s, e, path, env, wf=False):
        """fix f a0..a_{n-1} {struct a_r} := body, a_r a proof of a Prop inductive I (one or no index),
           result data  ->  lam a0..a_{n-1}. Acc.rec C R motive intro major wf G Q, with
           major = <idx, a_r> (PSigma.mk) or a_r, motive = lam s acc. forall G Q. T[s] and
           intro = lam s h ih. lam G Q. body' where every recursive call f P.. y rest becomes
           ih <j, y> cert G'' rest. C, R, wf and the certificates are types and proofs (forced by typing,
           no computational content) and are not compared."""
        d = s["defs"][0]
        r = d["rarg"]
        lams, b = [], d["body"]
        while b["k"] == "lam":
            lams.append(b)
            b = b["b"]
        nl = len(lams)
        senv = [("forbid",)] + list(env)
        cur = e
        for i, lam in enumerate(lams):
            if cur["k"] != "lam":
                raise Mismatch(f"{path}: expected {nl} lambdas")
            self.check(lam["ty"], cur["t"], path + [f"lam{i}"], senv)
            senv = self.push(senv)
            cur = cur["b"]
        head, spine = self.unspine(cur)
        xty = self.unfold_src_alias(lams[r]["ty"])
        xargs = []
        while xty["k"] == "app":
            xargs = xty["args"] + xargs
            xty = xty["f"]
        if xty["k"] != "ind":
            raise Mismatch(f"{path}: decreasing argument is not of an inductive type")
        mib = self.decls[xty["ind"]["mind"]]
        nrec = (mib.get("native") or {}).get("nparams_rec", mib["npars"])
        idx = xargs[nrec:]
        if len(idx) > 1 or any(a["k"] != "rel" or a["i"] >= r for a in idx):
            raise Mismatch(f"{path}: UNAUDITABLE accessibility lowering (indices)")
        has_idx = len(idx) == 1
        if wf and has_idx:
            raise Mismatch(f"{path}: termination lowering of a recursion on an indexed inductive")
        idx_pos = {r - 1 - a["i"] for a in idx}
        gpos = sorted(changed_params(d["body"], nl, r) - idx_pos)
        ng, nq = len(gpos), nl - r - 1
        if len(spine) != 6 + ng + nq:
            raise Mismatch(f"{path}: Acc.rec applied to {len(spine)} arguments")
        # carrier C (spine[0]), reconstructed from the source: PSigma (lam i : U. I params i) with the
        # second component a Prop family, or the decreasing argument's type itself
        C = spine[0]
        if has_idx:
            ch, ca = self.unspine(C)
            if ch.get("k") != "const" or ch.get("n") != "PSigma" or len(ca) != 2 or len(ch["u"]) != 2 \
                    or level_nf(ch["u"][1]) != canon(0, {}) or ca[1]["k"] != "lam":
                raise Mismatch(f"{path}: accessibility carrier is not PSigma of a Prop family")
            ip = next(iter(idx_pos))
            # U: the index lambda's type, in the context of the lambdas before it
            uenv = [("bvar", nl - 1 - k) for k in reversed(range(ip))] + [("forbid",)] + self.shift(list(env), nl)
            self.check(lams[ip]["ty"], ca[0], path + ["carrier index type"], uenv)
            # the family body: the decreasing argument's type with the index replaced by the binder
            fenv = [("bvar", 0) if k == ip else ("bvar", nl - 1 - k + 1) for k in reversed(range(r))] + [("forbid",)] \
                + self.shift(list(env), nl + 1)
            self.check(lams[r]["ty"], ca[1]["b"], path + ["carrier family"], fenv)
        else:
            cenv = [("bvar", nl - 1 - k) for k in reversed(range(r))] + [("forbid",)] + self.shift(list(env), nl)
            self.check(lams[r]["ty"], C, path + ["carrier"], cenv)
        # call-graph relation R (spine[1]): lam y s. D_1 \/ ... \/ D_n, one disjunct per recursive call of
        # the source body, each EXISTS ctx.., Eq C' y PAIR. (Its disjuncts' contents and the
        # well-foundedness proof and certificates are proofs/propositions checked by the kernel; R occurs
        # only in binder types of Acc.rec's minor premise, so it cannot change the computed value; a
        # relation not containing the call graph is kernel-rejected: test-m6 mutations.)
        def n_calls(t, depth):
            if isinstance(t, dict):
                n = 1 if (t.get("k") == "app" and t["f"] == {"k": "rel", "i": nl + depth}) else 0
                k = t.get("k")
                if k in ("lam", "prod"):
                    return n + n_calls(t["ty"], depth) + n_calls(t["b"], depth + 1)
                if k == "let":
                    return n + n_calls(t["v"], depth) + n_calls(t["ty"], depth) + n_calls(t["b"], depth + 1)
                if k == "case":
                    return n + n_calls(t["c"], depth) + sum(n_calls(x, depth) for x in t["p"]["params"]) \
                        + n_calls(t["p"]["ret"], depth + len(t["p"]["ctx"])) \
                        + sum(n_calls(br["body"], depth + len(br["ctx"])) for br in t["brs"])
                if k == "fix":
                    return n + sum(n_calls(dd["ty"], depth) + n_calls(dd["body"], depth + len(t["defs"])) for dd in t["defs"])
                return n + sum(n_calls(v, depth) for kk, v in t.items() if kk not in ("k",) and isinstance(v, (dict, list)))
            if isinstance(t, list):
                return sum(n_calls(v, depth) for v in t)
            return 0
        ncall = n_calls(b, 0)
        rb = self.strip_lams(spine[1], 2, path + ["relation"])
        disj = []
        while ncall - len(disj) > 1:
            oh, oa = self.unspine(rb)
            if oh.get("n") != "Or" or len(oa) != 2:
                raise Mismatch(f"{path}: call relation has fewer disjuncts than the source's {ncall} recursive calls")
            disj.append(oa[0])
            rb = oa[1]
        disj.append(rb)
        for q, dsj in enumerate(disj):
            dpt = 0
            while True:
                eh, ea = self.unspine(dsj)
                if eh.get("n") == "Exists" and len(ea) == 2 and ea[1]["k"] == "lam":
                    dsj, dpt = ea[1]["b"], dpt + 1
                    continue
                break
            if eh.get("n") != "Eq" or len(ea) != 3 or ea[1] != {"k": "bvar", "i": dpt + 1}:
                raise Mismatch(f"{path}: call relation disjunct {q} is not EXISTS ctx, y = <j, a>")
        # major
        xb = {"k": "bvar", "i": nl - 1 - r}
        maj = spine[4]
        if has_idx:
            mh, ma = self.unspine(maj)
            if mh.get("n") != "PSigma.mk" or len(ma) != 4 or ma[3] != xb:
                raise Mismatch(f"{path}: Acc.rec major is not <index, decreasing argument>")
        elif maj != xb:
            raise Mismatch(f"{path}: Acc.rec major is not the decreasing argument")
        if wf:
            # B: the well-foundedness argument is the termination obligation (hypothesis or final
            # theorem) applied to locals and then to the decreasing argument; its statement
            # (∀ Γ, ∀ s, Acc C R s) is kernel-checked against this Acc.rec's C and R
            leaf = self.wf_term_of(spine[5], env, nl)
            if leaf is None or self.unspine(spine[5])[1][-1] != xb:
                raise Mismatch(f"{path}: well-foundedness is not a termination obligation applied to the decreasing argument")
            self.wf_used.append(leaf)
        for j, i in enumerate(gpos):
            if spine[6 + j] != {"k": "bvar", "i": nl - 1 - i}:
                raise Mismatch(f"{path}: generalized argument {i} not passed on")
        for j in range(nq):
            if spine[6 + ng + j] != {"k": "bvar", "i": nq - 1 - j}:
                raise Mismatch(f"{path}: trailing argument {j} not passed on")
        proj = lambda i, sb: {"k": "proj", "s": "PSigma", "i": i, "e": {"k": "bvar", "i": sb}}

        def lead(i, depth, sidx, gbase):
            """Image of leading lambda i (< r) at `depth` binders below the lambdas: index -> s.1,
            generalized -> its G binder (gbase: index of G_0), other -> the outer lambda."""
            if i in idx_pos:
                return ("tgt", proj(0, sidx))
            if i in gpos:
                return ("bvar", gbase - gpos.index(i), "gen", i)
            return ("bvar", (nl - 1 - i) + depth, "param", i)

        # motive: lam s acc. forall G.. Q.. T
        mb = self.strip_lams(spine[2], 2, path + ["motive"])
        for j, i in enumerate(gpos):           # forall G: the generalized arguments' source types
            if mb["k"] != "forall":
                raise Mismatch(f"{path}: motive lacks the generalized argument {i}")
            depth = 2 + j
            menv = [lead(k, depth, depth - 1, j - 1) for k in reversed(range(i))] + [("forbid",)] + self.shift(list(env), nl + depth)
            self.check(lams[i]["ty"], mb["t"], path + [f"motive g{j}"], menv)
            mb = mb["b"]
        depth = 2 + ng
        xent = ("tgt", proj(1, depth - 1)) if has_idx else ("bvar", depth - 1)
        menv = [xent] + [lead(k, depth, depth - 1, ng - 1) for k in reversed(range(r))] + self.shift(list(env), nl + depth)
        fty = d["ty"]
        for _ in range(r + 1):
            if fty["k"] != "prod":
                raise Mismatch(f"{path}: fixpoint type has fewer than {r + 1} binders")
            fty = fty["b"]
        self.check(fty, mb, path + ["motive body"], menv)
        # intro: lam s h ih. lam G.. Q.. body
        ib = self.strip_lams(spine[3], 3 + ng + nq, path + ["intro"])
        depth = 3 + ng + nq
        sidx = depth - 1
        xent = ("tgt", proj(1, sidx)) if has_idx else ("bvar", sidx)
        benv = [("bvar", t) for t in range(nq)]                     # Q (innermost first)
        benv += [xent] + [lead(k, depth, sidx, nq + ng - 1) for k in reversed(range(r))]
        info = {"r": r, "ih": depth - 3, "gpos": gpos, "idx_pos": idx_pos, "has_idx": has_idx, "nq": nq, "convoy": wf}
        benv += [("accrec", info)] + self.shift(list(env), nl + depth)
        self.check(b, ib, path + ["intro"], benv)

    def check_rec_call_acc(self, s, e, path, env, info):
        """f P.. y rest  ->  ih <j, y> cert G'' rest   (j and cert forced by typing / proofs)."""
        args, r = s["args"], info["r"]
        if len(args) < r + 1:
            raise Mismatch(f"{path}: recursive call without its decreasing argument")
        for i in range(r):
            if i in info["idx_pos"] or i in info["gpos"]:
                continue
            a = args[i]
            ent = env[a["i"]] if a["k"] == "rel" and a["i"] < len(env) else None
            if not (ent and ent[0] == "bvar" and ent[2:4] == ("param", i)):
                raise Mismatch(f"{path}: recursive call changes parameter {i}")
        head, sp = self.unspine(e)
        # ih is bound at a fixed depth below the intro's binders; locate it through the env offset
        rest = [args[i] for i in info["gpos"]] + args[r + 1:]
        if len(sp) != 2 + len(rest) or head["k"] != "bvar":
            raise Mismatch(f"{path}: recursive call must become ih <j, y> cert ...")
        if head["i"] != info["ih"]:
            raise Mismatch(f"{path}: recursive call does not use the induction hypothesis (bvar {info['ih']})")
        pr = sp[0]
        if info["has_idx"]:
            ph, pa = self.unspine(pr)
            if ph.get("n") != "PSigma.mk" or len(pa) != 4:
                raise Mismatch(f"{path}: recursive call's argument is not a carrier pair")
            self.check(args[r], pa[3], path + ["rec-arg"], env)
        else:
            self.check(args[r], pr, path + ["rec-arg"], env)
        for j, a in enumerate(rest):
            self.check(a, sp[2 + j], path + [f"rec-arg{j}"], env)

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
        y, zs = args[r], []
        if y["k"] == "app" and y["f"]["k"] == "rel":      # a functional recursive field applied: g zs
            y, zs = y["f"], y["args"]
        ent = env[y["i"]] if y["k"] == "rel" and y["i"] < len(env) else None
        if info.get("cov"):
            # course-of-values: any subterm with a known result r becomes (r).1 G' rest
            if zs or not (ent and ent[0] == "bvar" and len(ent) > 5 and ent[2] == "field"):
                raise Mismatch(f"{path}: recursive call on a subterm without a course-of-values result")
            rest = [args[i] for i in info.get("gpos", [])] + args[r + 1:]
            cur = e
            for j in reversed(range(len(rest))):
                if cur["k"] != "app":
                    raise Mismatch(f"{path}: recursive result applied to too few arguments")
                self.check(rest[j], cur["a"], path + [f"rec-arg{j}"], env)
                cur = cur["f"]
            want = {"k": "proj", "s": "PProd", "i": 0, "e": ent[5]}
            if cur != want:
                raise Mismatch(f"{path}: recursive call must become the first component of its subterm's result {want}, found {cur}")
            return
        if not (ent and ent[0] == "bvar" and len(ent) == 5 and ent[2] == "field" and ent[3] == info["minor"]):
            raise Mismatch(f"{path}: recursive call not on a constructor field")
        q = ent[4]
        if q not in info["rec_q"]:
            raise Mismatch(f"{path}: recursive call on a non-recursive field")
        if bool(zs) != (q in info.get("fun_q", [])):
            raise Mismatch(f"{path}: recursive call on a functional field must apply it (and only then)")
        m = info["rec_q"].index(q)
        ih = ent[1] - 1 - m - q
        rest = [args[i] for i in info.get("gpos", [])] + args[r + 1:]
        cur = e
        for j in reversed(range(len(rest))):
            if cur["k"] != "app":
                raise Mismatch(f"{path}: recursive result applied to too few arguments")
            self.check(rest[j], cur["a"], path + [f"rec-arg{j}"], env)
            cur = cur["f"]
        if info.get("nfn", 1) > 1:              # mutual block: the component of the called function
            for i in pprod_path(info["fn"], info["nfn"]):
                if cur.get("k") != "proj" or cur.get("s") != "PProd" or cur.get("i") != i:
                    raise Mismatch(f"{path}: recursive call must select component {info['fn']} of the recursive result")
                cur = cur["e"]
        for j in reversed(range(len(zs))):          # a functional field's recursive result, applied: ih zs
            if cur["k"] != "app":
                raise Mismatch(f"{path}: recursive result of a functional field applied to too few arguments")
            self.check(zs[j], cur["a"], path + [f"rec-z{j}"], env)
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


COERCE = [False]      # whether the row being audited reports rule P coercions
PHANTOM = "Corelib.ssr.ssreflect_rw.phantom"


def phantom_def_pairs(d):
    """Rule Q-a (docs/PHANTOM_SORT.md), independently of the translator: a transparent monomorphic constant
    whose body, after its λs, is a chain of non-dependent products of `phantom X x`, X a λ-parameter whose
    type is a sort and x a λ-parameter of type X. Returns the (sort, value) parameter index pairs, or None.
    Every application of such a definition is inhabited (by phantom's constructor), whatever its sorts."""
    if d.get("kind") != "constant" or (d.get("universes") or {}).get("k") != "monomorphic":
        return None
    is_ph = lambda t: t.get("k") == "app" and t["f"].get("k") == "ind" and t["f"]["ind"] == {"mind": PHANTOM, "i": 0}
    tys = []
    if d.get("body_state") == "transparent" and d.get("body"):
        b = d["body"]                                   # a phantom check: the body after its λs
        while b.get("k") == "lam":
            tys.append(b["ty"])
            b = b["b"]
    else:                                               # a proof of one: the statement after its parameters
        b = d["type"]
        while b.get("k") == "prod" and not is_ph(b["ty"]):
            tys.append(b["ty"])
            b = b["b"]
        if not (is_ph(b) or (b.get("k") == "prod" and is_ph(b["ty"]))):
            return None
    n = len(tys)

    def factor(t, k):
        if t.get("k") != "app" or t["f"].get("k") != "ind" or t["f"]["ind"] != {"mind": PHANTOM, "i": 0} \
                or len(t["args"]) != 2 or any(a.get("k") != "rel" for a in t["args"]):
            return None
        ai, vi = t["args"][0]["i"], t["args"][1]["i"]
        if not (k <= ai < n + k and k <= vi < n + k):
            return None
        pa, pv = n - 1 - (ai - k), n - 1 - (vi - k)
        tv = tys[pv]
        if tys[pa].get("k") != "sort" or tv.get("k") != "rel" or not (tv["i"] < pv and pv - 1 - tv["i"] == pa):
            return None
        return pa, pv

    pairs, k = [], 0
    while b.get("k") == "prod":
        f = factor(b["ty"], k)
        if f is None or mentions_rels(b["b"], 0, 1):
            return None
        pairs.append(f)
        b, k = b["b"], k + 1
    f = factor(b, k)
    if f is None:
        return None
    return pairs + [f]


def erase_phantom_sorts(t, pd):
    """Rule Q-a: the sort arguments at the sort-parameter positions of phantom-definition applications,
    replaced by the marker {"k": "phantom_sort"} (which matches any target sort: the kernel fixes it as the
    type of the paired value)."""
    if isinstance(t, list):
        return [erase_phantom_sorts(x, pd) for x in t]
    if not isinstance(t, dict):
        return t
    out = {k: erase_phantom_sorts(v, pd) for k, v in t.items()}
    if t.get("k") == "app" and t["f"].get("k") == "const" and t["f"]["c"] in pd:
        args = list(out["args"])
        for si, _ in pd[t["f"]["c"]]:
            if si < len(args) and t["args"][si].get("k") == "sort":
                args[si] = {"k": "phantom_sort"}
        out["args"] = args
    return out


def peel_lift_coercion(e):
    """`PULift.up X t` or `PULift.down X t` with universe instance [r, 0] -> t; otherwise None."""
    if e.get("k") != "app" or e["f"].get("k") != "app":
        return None
    h = e["f"]["f"]
    if h.get("k") != "const" or h.get("n") not in ("PULift.up", "PULift.down") or len(h.get("u") or []) != 2:
        return None
    if level_nf(h["u"][1]) != level_nf({"k": "zero"}):
        raise Mismatch(f"rule P: {h['n']} at a non-Prop universe {h['u'][1]}")
    return e["a"]


def check_coinductive(d, r):
    """Rule T (docs/COINDUCTIVE.md), independently: a coinductive block is accepted as an inductive only when
    the row reports it and the block has one body, no constructor argument or index mentioning the block
    (the arguments are stored innermost first: args[k] lies under the block, the parameters and the
    len(args) - 1 - k earlier arguments)."""
    co = d.get("finite") == "CoFinite"
    if bool(r.get("coinductive_as_inductive")) != co:
        raise Mismatch("coinductive_as_inductive differs from the source block's kind")
    if not co:
        return
    if len(d["bodies"]) != 1:
        raise Mismatch("rule T: a mutual coinductive block")
    npars, nb = d["npars"], len(d["bodies"])
    for b in d["bodies"]:
        for c in b["ctors"]:
            n_ = len(c["args"])
            for k, a in enumerate(c["args"]):
                if mentions_rels(a["ty"], n_ - 1 - k + npars, nb):
                    raise Mismatch(f"rule T: constructor {c['name']} is recursive (an argument mentions the block)")
            for x in c.get("indices") or []:
                if mentions_rels(x, len(c["args"]) + npars, nb):
                    raise Mismatch(f"rule T: constructor {c['name']} has an index mentioning the block")


def peel_eta(e):
    """`fun x₀ … xₙ₋₁ => c (f a… c x₀ … c xₙ₋₁)` (c: optional lift coercions) -> (f a…, n); otherwise None."""
    n, b = 0, e
    while b.get("k") == "lam":
        n, b = n + 1, b["b"]
    while (x := peel_lift_coercion(b)) is not None:
        b = x
    args = []
    while b.get("k") == "app" and len(args) < n:
        args.append(b["a"])
        b = b["f"]
    if len(args) != n:
        return None
    for i, a in enumerate(args):               # args[0] is the last argument, x_{n-1} = bvar 0
        while (x := peel_lift_coercion(a)) is not None:
            a = x
        if a != {"k": "bvar", "i": i}:
            return None
    return b, n


def strip_prop_lift(r, tv, src_type, body):
    """Rule P (docs/PROP_LIFT.md, approved), independently: a row reporting `prop_lift = k` has,
    under its first k value binders, exactly `PULift.{r, 0} X`, where the source type after k binders is a
    sort `Type@{l}` and r is that sort's image (so `PULift.{r,0} X : Sort r` is exactly the declared
    type); the kernel checks that X is a proposition (`PULift.{_, 0}`). Returns the value with the wrapper
    replaced by X, for the structural check against the source."""
    k = r.get("prop_lift")
    if k is None:
        return tv
    if not isinstance(k, int) or k < 0:
        raise Mismatch(f"rule P: invalid lift depth {k}")
    st = src_type
    for _ in range(k):
        if st.get("k") != "prod":
            raise Mismatch("rule P: the source type has fewer binders than the lift depth")
        st = st["b"]
    if st.get("k") != "sort" or st["s"].get("k") != "type":
        raise Mismatch("rule P: the source type does not end in a Type at the lift depth")
    tv = copy.deepcopy(tv)
    holder, key, cur = None, None, tv
    for _ in range(k):
        if cur.get("k") != "lam":
            raise Mismatch("rule P: the value has fewer binders than the lift depth")
        holder, key, cur = cur, "b", cur["b"]
    if not (cur.get("k") == "app" and cur["f"].get("k") == "const" and cur["f"]["n"] == "PULift"
            and len(cur["f"]["u"]) == 2):
        raise Mismatch("rule P: no PULift at the lift depth")
    lv_r, lv_s = cur["f"]["u"]
    if level_nf(lv_s) != level_nf({"k": "zero"}):
        raise Mismatch("rule P: the lifted term is not lifted from Prop")
    if level_nf(lv_r) != source_sort_nf(st["s"], body):
        raise Mismatch(f"rule P: the lift's level {lv_r} is not the image of the source sort")
    if holder is None:
        return cur["a"]
    holder[key] = cur["a"]
    return tv


def src_has_univ_var(t):
    """Whether a source term mentions a universe variable ({"k": "var", "i": n}, in a sort or an instance)."""
    if isinstance(t, list):
        return any(src_has_univ_var(x) for x in t)
    if not isinstance(t, dict):
        return False
    if t.get("k") == "var" and "i" in t:
        return True
    return any(src_has_univ_var(v) for v in t.values() if isinstance(v, (dict, list)))


def erasing_poly_body(d):
    """Entry 14, independently: a transparent universe-polymorphic constant whose body, after its
    leading lambdas, mentions no universe variable (its applications are δβ-reducible without leaving
    any level of the instance). Returns the body, or None."""
    if d.get("kind") != "constant" or d.get("body_state") != "transparent" or d.get("body") is None:
        return None
    if (d.get("universes") or {}).get("k") != "polymorphic":
        return None
    b, n = d["body"], 0
    while b.get("k") == "lam":
        b, n = b["b"], n + 1
    return d["body"] if n > 0 and not src_has_univ_var(b) else None


def inline_erasing_block(d, bodies):
    """The block `d` with every application of the given erasing definitions δβ-reduced (no fuel bound:
    each reduct is smaller, the definitions erase their arguments' levels)."""
    def pre(x, k):
        if x.get("k") == "app" and x["f"].get("k") == "const" and x["f"]["c"] in bodies:
            return src_flatten_apps(beta_app(bodies[x["f"]["c"]], x["args"]))
        return None
    d2 = copy.deepcopy(d)
    for p_ in d2.get("params") or []:
        p_["ty"] = src_rewrite(p_["ty"], pre)        # (context declarations: n, body, ty)
    for b in d2.get("bodies") or []:
        b["type"] = src_rewrite(b["type"], pre)
        for c in b.get("ctors") or []:
            c["type"] = src_rewrite(c["type"], pre)
            for a in c.get("args") or []:
                a["ty"] = src_rewrite(a["ty"], pre)
        for pj in b.get("projs") or []:              # (primitive records: the projections' types)
            pj["type"] = src_rewrite(pj["type"], pre)
    return d2


def src_rewrite(t, pre, k=0, again=True):
    """Rewrite a source IR term top-down: pre(node, k) returns a replacement or None; k counts the
    binders above the node. With again, a replacement is itself rewritten (at the same k)."""
    if isinstance(t, list):
        return [src_rewrite(x, pre, k, again) for x in t]
    if not isinstance(t, dict):
        return t
    r = pre(t, k)
    if r is not None:
        return src_rewrite(r, pre, k, again) if again else r
    go = lambda u, d=0: src_rewrite(u, pre, k + d, again)
    kk = t.get("k")
    if kk in ("prod", "lam"):
        return dict(t, ty=go(t["ty"]), b=go(t["b"], 1))
    if kk == "let":
        return dict(t, v=go(t["v"]), ty=go(t["ty"]), b=go(t["b"], 1))
    if kk == "case":
        p = t["p"]
        return dict(t, p=dict(p, params=go(p["params"]), ret=go(p["ret"], len(p["ctx"]))), c=go(t["c"]),
                    brs=[dict(br, body=go(br["body"], len(br["ctx"]))) for br in t["brs"]])
    if kk in ("fix", "cofix"):
        n = len(t["defs"])
        return dict(t, defs=[dict(d, ty=go(d["ty"]), body=go(d["body"], n)) for d in t["defs"]])
    return {key: (go(v) if isinstance(v, (dict, list)) else v) for key, v in t.items()}


def src_lift(t, n):
    """Add n to every free rel of a source term."""
    if not n:
        return t
    return src_rewrite(t, lambda x, d: {"k": "rel", "i": x["i"] + n} if x.get("k") == "rel" and x["i"] >= d else None,
                       again=False)


def src_subst0(b, v):
    """b[rel 0 := v] for a source term b under one binder (v in the context outside the binder)."""
    def pre(x, d):
        if x.get("k") != "rel" or x["i"] < d:
            return None
        return src_lift(v, d) if x["i"] == d else {"k": "rel", "i": x["i"] - 1}
    return src_rewrite(b, pre, again=False)


def src_flatten_apps(t):
    """app (app f a) b -> app f (a ++ b)."""
    def pre(x, d):
        if x.get("k") == "app" and x["f"].get("k") == "app":
            return {"k": "app", "f": x["f"]["f"], "args": x["f"]["args"] + x["args"]}
        return None
    return src_rewrite(t, pre)


def mentions_rels(t, lo, n):
    """Does the source term mention a free rel in [lo, lo+n) (counted at its top)?"""
    hit = []
    src_rewrite(t, lambda x, d: hit.append(1) if x.get("k") == "rel" and lo + d <= x["i"] < lo + d + n else None,
                again=False)
    return bool(hit)


def zeta_fix_lets(body, nfun):
    """M6 ζ-normalization of a fixpoint body (independent of the translator): a let whose value
    mentions a function of the block (a partial application, e.g. Pos.peano_rect's f2) is inlined,
    so its uses become recursive calls. The body is at depth 0 below the block's binders."""
    def pre(x, d):
        if x.get("k") == "let" and mentions_rels(x["v"], d, nfun):
            return src_flatten_apps(src_subst0(x["b"], x["v"]))
        return None
    return src_rewrite(body, pre)


def partial_rec_use(t, lo, need):
    """Does the source term use a function of a fixpoint block (rel lo+o, o < len(need); offset 0 is
    the block's last function) other than in a full call (fewer than need[o] arguments, or bare)?"""
    found = []

    def pre(x, d):
        if x.get("k") == "app" and x["f"].get("k") == "rel":
            i = x["f"]["i"] - lo - d
            if 0 <= i < len(need) and len(x["args"]) < need[i]:
                found.append(1)
            for a in x["args"]:
                src_rewrite(a, pre, d, again=False)
            return x                                   # handled (the head is not visited bare)
        if x.get("k") == "rel" and 0 <= x["i"] - lo - d < len(need):
            found.append(1)
        return None
    src_rewrite(t, pre, again=False)
    return bool(found)


def beta_app(f, args):
    """Source β-reduction of f args as far as f's leading lambdas go (rest stays applied, flattened)."""
    while args and f.get("k") == "lam":
        f, args = src_subst0(f["b"], args[0]), args[1:]
    if not args:
        return f
    if f.get("k") == "app":
        return {"k": "app", "f": f["f"], "args": f["args"] + args}
    return {"k": "app", "f": f, "args": args}


def inline_rec_args(body, need, bodies, fuel=16):
    """M6 δβ-inlining (independent of the translator): in a fixpoint body, c args with c a transparent
    monomorphic constant and some argument using a block function other than in a full call is
    replaced by c's source body β-reduced with args (Ring_polynom Padd/PaddI, Tauto xcnf/mk_and)."""
    def pre(x, d):
        nonlocal fuel
        if x.get("k") == "app" and x["f"].get("k") == "const" and x["f"]["c"] in bodies and fuel > 0 \
                and any(partial_rec_use(a, d, need) for a in x["args"]):
            fuel -= 1
            return src_flatten_apps(beta_app(bodies[x["f"]["c"]], x["args"]))
        return None
    return src_rewrite(body, pre)


def mentions_src_rel(t, i):
    """Does the source term mention rel i (counting binders)?"""
    found = []
    src_rewrite(t, lambda x, d: found.append(1) if x.get("k") == "rel" and x["i"] == i + d else None, again=False)
    return bool(found)


def has_set_motive(ty):
    """The source type has a binder of a Set-valued family (forall xs, Set with xs nonempty)."""
    while ty.get("k") == "prod":
        a, n = ty["ty"], 0
        while a.get("k") == "prod":
            a, n = a["b"], n + 1
        if n and a.get("k") == "sort" and a["s"]["k"] == "type" and a["s"]["u"] == [{"l": {"k": "set"}, "n": 0}]:
            return True
        ty = ty["b"]
    return False


def inline_consts(body, names, bodies, fuel=8):
    """M6 delta-inlining (independent): applications of the listed constants become their source
    bodies beta-reduced with the arguments."""
    left = [fuel]

    def pre(x, d):
        if x.get("k") == "app" and x["f"].get("k") == "const" and x["f"]["c"] in names and left[0] > 0:
            left[0] -= 1
            return src_flatten_apps(beta_app(bodies[x["f"]["c"]], x["args"]))
        return None
    return src_rewrite(body, pre)


def src_anon(t):
    """A source term without binder names (for comparing source types)."""
    if isinstance(t, dict):
        return {k: (len(v) if k == "ctx" else src_anon(v)) for k, v in t.items()
                if not (k == "n" and t.get("k") in ("prod", "lam", "let"))}
    if isinstance(t, list):
        return [src_anon(v) for v in t]
    return t


def pprod_path(j, n):
    """Projection indices, outermost first, of component j of a right-nested PProd of n types."""
    return ([0] if j + 1 < n else []) + [1] * j


def same_mod_beta(a, b):
    """Equal modulo beta, binder names and (documented) the semantic normal form of levels."""
    x, y = anon(beta(a)), anon(beta(b))
    if x == y:
        return True
    try:
        return canon_levels(x) == canon_levels(y)
    except Mismatch:
        return False


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
        # R-SPLIT: a copy of a level inherits its upper bounds (l <= m, l < m), never its lower bounds
        # and lies below it (a copy stands for an argument a <= l, R3 at every use)
        for c, l in SPLIT_COPIES.items():
            self.levels.append(c)
            self.rel[(c, l)] = "le"
            for (a, b), r in list(self.rel.items()):
                if a == l and b != l and r in ("le", "lt"):
                    self.rel[(c, b)] = r

    def entails(self, a, b, k):
        """a + k <= b in the source universe graph."""
        if k <= 0:
            return a == b or self.rel.get((a, b)) in ("le", "lt")
        if k == 1:
            return self.rel.get((a, b)) == "lt"
        return any(self.rel.get((a, c)) == "lt" and self.entails(c, b, k - 1) for c in self.levels)


GEN_COPY_POS = {}    # R-CARRIER P2: target -> universe-parameter positions that are P2 copies
HYP_STATEMENTS = set()  # rule H: the statement targets of the source's proof tasks (prerequisite hypotheses' types)
P2_COPIES = set()    # R-CARRIER P2: the reported (checked) copies of implicit levels
RSI_CHECKED = [0]   # R3G-F rows' levels checked (check_result_sort_implicit)
CARRIER_SET = set()  # R-CARRIER P1: parameter carrier levels of the exported non-template blocks
DECOUPLED = set()    # R-CARRIER P1: (carrier, other level of the same block) pairs, not raising the carrier in R2F


def carrier_levels(d):
    """R-CARRIER (docs/CARRIER_LEVELS.md), independently: the global levels occurring as the final sort of a
    parameter binder's type in the arity of a non-template inductive block."""
    if d.get("kind") != "inductive" or template_binding(d) is not None:
        return set()
    out = set()
    for b in d["bodies"]:
        t = b["type"]
        for _ in range(d["npars"]):
            if t.get("k") != "prod":
                break
            ty = t["ty"]
            while ty.get("k") == "prod":
                ty = ty["b"]
            if ty.get("k") == "sort" and ty["s"]["k"] == "type":
                out |= {e["l"]["n"] for e in ty["s"]["u"] if e["l"].get("k") == "global"}
            t = t["b"]
    return out


DECL_SRC = {}        # source name -> exported declaration (its dependency lists), set with RS_CLOSURE
ERASED = {}          # entry 15: constant -> erasing definitions δβ-inlined in its type and value
RS_CLOSURE = {}      # R3G-F: source name -> result-sort implicit levels in its dependency closure (itself included)


def rs_deps(d):
    """R3G-F: the result-sort implicit levels in the dependency closure of d's dependencies."""
    dd = d.get("deps") or {}
    out = set()
    for x in (dd.get("type") or []) + (dd.get("body") or []):
        out |= RS_CLOSURE.get(x, set())
    return out
SPLIT_COPIES = {}    # R-SPLIT: copy level -> its source level (set by main_statement; read by Facts and R3)


def _occ_paths(j, name, path=()):
    """Every path at which the string `name` occurs in the JSON value j (as a value)."""
    out = []
    stack = [(j, path)]
    while stack:
        x, pth = stack.pop()
        if isinstance(x, dict):
            stack.extend((v, pth + (k,)) for k, v in x.items())
        elif isinstance(x, list):
            stack.extend((v, pth + (i,)) for i, v in enumerate(x))
        elif x == name:
            out.append(pth)
    return set(out)


def _at(j, path):
    for k in path:
        j = j[k]
    return j


def _final_sort_paths(t, base, l):
    """Paths of `l` in the final sort of a term `forall ..., Sort s` (base: the term's path)."""
    pth = base
    while t.get("k") == "prod":
        t, pth = t["b"], pth + ("b",)
    if t.get("k") != "sort" or t["s"]["k"] != "type":
        return set()
    return {pth + ("s", "u", i, "l", "n") for i, e in enumerate(t["s"]["u"]) if e["l"].get("k") == "global" and e["l"].get("n") == l}


def _binders(t, base, kind, n):
    """(path of the binder type, binder type) of the first n `kind` binders of t, and the rest."""
    out = []
    pth = base
    while len(out) < n and t.get("k") == kind:
        out.append((pth + ("ty",), t["ty"]))
        t, pth = t["b"], pth + ("b",)
    return out, (pth, t)


def level_split_view(d):
    """R-SPLIT (docs/LEVEL_SPLIT.md), independently of the translator, by occurrence paths: a source
    global level `l` of a monomorphic declaration splits when every occurrence of the string `l` in
    the whole exported declaration lies in the final sort of a parameter binder (constants: the type's
    binder and the body's lambda at the same position; inductives: the arity's, the parameter
    context's and every constructor's binder at that position) whose binder type mentions `l` only
    there — at least two such binders — or in the declaration's final result sort. Returns
    (view, [{"level", "params", "copies"}]) or (None, [])."""
    if (d.get("universes") or {}).get("k") != "monomorphic":
        return None, []
    if d["kind"] == "constant":
        if d.get("body") is None:
            return None, []
        tb, (trp, trest) = _binders(d["type"], ("type",), "prod", 10 ** 9)
        bb, _ = _binders(d["body"], ("body",), "lam", 10 ** 9)
        np_ = min(len(tb), len(bb))
        tb, bb = tb[:np_], bb[:np_]
        trp, trest = ("type",) + ("b",) * np_, _at(d, ("type",) + ("b",) * np_)
        positions = [[tb[i], bb[i]] for i in range(np_)]
        results = [(trp, trest)]
    else:
        if len(d["bodies"]) != 1 or d["npars"] < 2 or (d.get("native") or {}).get("template"):
            return None, []
        np_ = d["npars"]
        b = d["bodies"][0]
        ab, (arp, arest) = _binders(b["type"], ("bodies", 0, "type"), "prod", np_)
        if len(ab) != np_:
            return None, []
        positions = []
        for k in range(np_):
            pos = [ab[k], (("params", np_ - 1 - k, "ty"), d["params"][np_ - 1 - k]["ty"])]
            for ci, c in enumerate(b["ctors"]):
                cb, _ = _binders(c["type"], ("bodies", 0, "ctors", ci, "type"), "prod", np_)
                if len(cb) != np_:
                    return None, []
                pos.append(cb[k])
            positions.append(pos)
        results = [(arp, arest)]
    levels = sorted(source_globals(d, set()))
    infos, ren = [], {}
    for l in levels:
        occ = _occ_paths(d, l)
        groups, allowed = [], set()
        for k, binders in enumerate(positions):
            fs = [_final_sort_paths(ty, pth, l) for pth, ty in binders]
            # a group: l in the final sort of every binder at this position, and nowhere else in them
            if all(f and f == {q for q in occ if q[:len(pth)] == pth} for f, (pth, _) in zip(fs, binders)):
                groups.append(k)
                allowed |= set().union(*fs)
        if len(groups) < 2:
            continue
        res = set().union(*(_final_sort_paths(t, pth, l) for pth, t in results))
        if d["kind"] == "inductive":
            srt = d["bodies"][0]["sort"]
            if srt.get("k") == "type":
                res |= {("bodies", 0, "sort", "u", i, "l", "n") for i, e in enumerate(srt["u"])
                        if e["l"].get("k") == "global" and e["l"].get("n") == l}
        if occ != allowed | res:
            continue
        copies = [f"{l}__s{k}" for k in groups]
        infos.append({"level": l, "params": groups, "copies": copies})
        for k, c in zip(groups, copies):
            for pth, ty in positions[k]:
                for q in _final_sort_paths(ty, pth, l):
                    ren[q] = [c]
        for q in res:
            ren[q] = copies
    if not infos:
        return None, []
    v = copy.deepcopy(d)
    # result sorts: an entry for l becomes one entry per copy (max of the copies), in place
    for q in sorted(ren, key=lambda q: (len(q), [str(x) for x in q]), reverse=True):
        u = _at(v, q[:-3])          # the sort's level list
        i = q[-3]
        e = u[i]
        u[i:i + 1] = [{**e, "l": {**e["l"], "n": c}} for c in ren[q]]
    return v, infos


def result_only_levels(d):
    """R3G-F (docs/RESULT_SORT_LEVELS.md), independently: the global levels of a single-body inductive
    every occurrence of which (anywhere in the exported declaration) lies in its result sort: the
    arity's final sort or the body's `sort`."""
    if d.get("kind") != "inductive" or len(d["bodies"]) != 1:
        return set()
    b = d["bodies"][0]
    out = set()
    for l in source_globals(b["type"], set()):
        occ = _occ_paths(d, l)
        res = set(_final_sort_paths(b["type"], ("bodies", 0, "type"), l))
        if b["sort"].get("k") == "type":
            res |= {("bodies", 0, "sort", "u", i, "l", "n") for i, e in enumerate(b["sort"]["u"])
                    if e["l"].get("k") == "global" and e["l"].get("n") == l}
        if res and occ == res:
            out.add(l)
    return out


def _sort_params(e, acc):
    """Universe parameters occurring inside a sort node of a Lean term (JSON), not in instances."""
    st = [e]
    while st:
        x = st.pop()
        if isinstance(x, dict):
            if x.get("k") == "sort":
                st2 = [x.get("l")]
                while st2:
                    y = st2.pop()
                    if isinstance(y, dict):
                        if y.get("k") == "param":
                            acc.add(y["n"])
                        st2.extend(v for v in y.values() if isinstance(v, (dict, list)))
                continue
            st.extend(v for v in x.values() if isinstance(v, (dict, list)))
        elif isinstance(x, list):
            st.extend(x)
    return acc


def _all_params(e, acc):
    st = [e]
    while st:
        x = st.pop()
        if isinstance(x, dict):
            if x.get("k") == "param":
                acc.add(x["n"])
            st.extend(v for v in x.values() if isinstance(v, (dict, list)))
        elif isinstance(x, list):
            st.extend(x)
    return acc


def check_result_sort_implicit(facts, d, r, gen, ro_of):
    """R3G-F, independently of the translator: every reported result-sort implicit level l of a block
    (1) is an implicit level, not a level of the block's source, of a non-template block; (2) occurs in a
    constructor field as the argument for l of a reference to a declaration in which l is result-sort-only
    (`ro_of`, from that declaration's source, or that declaration's own R3G-F levels); (3) is bounded by a
    level of the block's source result sort in the native graph; (4) changes no quantification range: its
    parameter occurs in no binder domain of the arity, and as a sort nowhere in a constructor type (only
    in universe arguments of references)."""
    rsi = r.get("result_sort_implicit_levels") or []
    if not rsi:
        return 0
    if template_binding(d) is not None or len(d["bodies"]) != 1:
        raise Mismatch("R3G-F levels on a template or mutual block")
    srt = d["bodies"][0]["sort"]
    res_lv = {e["l"]["n"] for e in srt.get("u") or [] if e["l"].get("k") == "global"} if srt.get("k") == "type" else set()
    imp = set(r.get("implicit_levels") or [])
    ctors = [c["type"] for c in r.get("target_ctors") or []]
    self_n = {r.get("target")} | {c["name"] for c in r.get("target_ctors") or []}
    for l in rsi:
        if l not in imp or l in ind_globals(d):
            raise Mismatch(f"R3G-F level {l} is not an implicit level of the block")
        if not any(nm not in self_n and nm in gen and l in ro_of(nm) and l in gen[nm]
                   for c in ctors for nm, _ in const_occurrences(c, [])):
            raise Mismatch(f"R3G-F level {l} is not result-sort-only in a declaration referenced by a field")
        if not any(facts.entails(l, s_, 0) for s_ in res_lv):
            raise Mismatch(f"R3G-F level {l} is not bounded by the block's result sort {sorted(res_lv)} in the source graph")
        p = level_param(l)
        x = r.get("target_type")
        while x is not None and x.get("k") == "forall":
            if p in _all_params(x["t"], set()):
                raise Mismatch(f"R3G-F level {l} occurs in a parameter or index range of the block")
            x = x["b"]
        for c in ctors:
            if p in _sort_params(c, set()):
                raise Mismatch(f"R3G-F level {l} occurs as a sort in a constructor type (a field range)")
    return len(rsi)


def level_unsplit(v, infos):
    """The diagonal: every copy renamed back to its level (a max of equal summands collapsed)."""
    back = {c: x["level"] for x in infos for c in x["copies"]}

    def go(j):
        if isinstance(j, list):
            return [go(x) for x in j]
        if not isinstance(j, dict):
            return j
        if j.get("k") == "type" and isinstance(j.get("u"), list):
            u = []
            for e in j["u"]:
                e = go(e)
                if e not in u:
                    u.append(e)
            return {**{k: go(x) for k, x in j.items() if k != "u"}, "u": u}
        if j.get("k") == "global" and j.get("n") in back:
            return {**j, "n": back[j["n"]]}
        return {k: go(x) for k, x in j.items()}
    return go(v)


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


def equal_at_models(facts, own_params, a, b):
    """Rule R (docs/COHERENCE_READINGS.md), independently: the levels a and b (u_m read as the source level m,
    a constant c as Set + c) are equal at every model of the source facts: every summand of either side lies
    below some summand of the other in the native graph."""
    def summ(x):
        c, ps = level_nf(x)
        out = [("Set", c or 0)]
        for p_, k in ps:
            if p_ not in own_params:
                return None
            out.append((own_params[p_], k))
        return out

    def leq(lhs, rhs):
        return all((x == "Set" and i == 0) or any(
            (x == y or facts.entails(x, y, 0) or x == "Set") if i <= j else facts.entails(x, y, i - j)
            for y, j in rhs) for x, i in lhs)
    sa, sb = summ(a), summ(b)
    return sa is not None and sb is not None and leq(sa, sb) and leq(sb, sa)


def check_universe_args(facts, own, gen, exprs, body=None, poly=None, admit=None, own_admit=frozenset(), lift=False,
                        lower=False):
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
            cpos = GEN_COPY_POS.get(name, set())
            # rule H (docs/COHERENCE_READINGS.md §5): at a proof task's statement (a prerequisite
            # hypothesis's type, instantiated where the prerequisite is used), an argument for a shared
            # level may lie below it: R3-down, checked below like any argument for another declaration
            low = lower or name in HYP_STATEMENTS
            for idx, (l, sigma) in enumerate(zip(ls, us)):
                if l in TEMPLATE_LEVELS:
                    continue                      # R5: instantiated from the arguments, checked by InstanceLevels
                # R-CARRIER P2: at a copy position, l is not shared (R3 entailment below, not coherence)
                own_l = own - {l} if idx in cpos else own
                c, ps = level_nf(sigma)
                ca, da = l in c_adm, l in own_admit      # R8: motive-level parameters (one above the image)
                if da and not ca:
                    raise Mismatch(f"{name}: source level {l} is a motive level of the referring declaration only")
                bump = (lambda x: {"k": "succ", "l": x}) if ca and not da else (lambda x: x)
                # Rule R (docs/COHERENCE_READINGS.md): for a shared level, max(u_l, s1, ...) whose other
                # summands pass the R3 check below equals l at every model of the source facts (an R2F
                # reading, not a specialization); not for motive-level (R8) parameters
                # (general form: the argument equals l at every model of the source facts, e.g. a summand
                # u_m of a source-equal level m)
                reading = not ca and not da and equal_at_models(facts, own_params, sigma, {"k": "param", "n": level_param(l)})
                # (rule R for a proof-local level or an R2F image: equal to it at every model of the facts)
                same_sol = body and l in body and not ca and not da and equal_at_models(facts, own_params, sigma, body[l])
                if body and l in body and not same_sol and not (low and (c, ps) != level_nf(bump(body[l]))):
                    if (c, ps) != level_nf(bump(body[l])):
                        raise Mismatch(f"{name}: source level {l} is proof-local, argument must be its solution {body[l]}")
                elif l in own_l and not (body and l in body) and not reading and not (low and (c, ps) != level_nf(bump({"k": "param", "n": level_param(l)}))):
                    if (c, ps) != level_nf(bump({"k": "param", "n": level_param(l)})):
                        raise Mismatch(f"{name}: source level {l} is shared, argument must be {level_param(l)}")
                else:
                    # (R3-down, rows of the lowered tier only: an argument for a shared level that is not its
                    # variable must not raise either, as for a level of another declaration)
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


def has_bvar(e, i):
    """Whether de Bruijn index i (relative to e's top) occurs in e."""
    if isinstance(e, list):
        return any(has_bvar(x, i) for x in e)
    if not isinstance(e, dict):
        return False
    k = e.get("k")
    if k == "bvar":
        return e["i"] == i
    if k in ("forall", "lam"):
        return has_bvar(e["t"], i) or has_bvar(e["b"], i + 1)
    if k == "let":
        return has_bvar(e["t"], i) or has_bvar(e["v"], i) or has_bvar(e["b"], i + 1)
    return any(has_bvar(v, i) for v in e.values() if isinstance(v, (dict, list)))


def app_occurrences(e, acc, types=None):
    """(name, universe arguments, number of applied arguments) of every constant occurrence, except
    inside a type argument that sibling arguments determine (`@Eq.{u} A a b`: A is the type of a, so
    kernel typing fixes it; given `types`: head name -> (type, ...))."""
    stack = [e]
    while stack:
        x = stack.pop()
        if isinstance(x, list):
            stack.extend(x)
            continue
        if not isinstance(x, dict):
            continue
        if x.get("k") == "app":
            h, args = x, []
            while h.get("k") == "app":
                args.append(h["a"])
                h = h["f"]
            args.reverse()
            skip = set()
            if h.get("k") == "const" and types and h["n"] in types:
                bs, t = [], types[h["n"]][0]
                while t is not None and t.get("k") == "forall" and len(bs) < len(args):
                    bs.append(t["t"])
                    t = t["b"]
                for j, bt in enumerate(bs):
                    if bt.get("k") == "sort" and any(has_bvar(bs[k], k - j - 1) for k in range(j + 1, len(bs))):
                        skip.add(j)
            stack.extend(a_ for j, a_ in enumerate(args) if j not in skip)
            if h.get("k") == "const":
                acc.append((h["n"], h["u"], len(args)))
            else:
                stack.append(h)
            continue
        if x.get("k") == "const":
            acc.append((x["n"], x["u"], 0))
            continue
        stack.extend(v for v in x.values() if isinstance(v, (dict, list)))
    return acc


def mentions_param(j, p):
    if isinstance(j, dict):
        return (j.get("k") == "param" and j.get("n") == p) or any(mentions_param(v, p) for v in j.values())
    return isinstance(j, list) and any(mentions_param(v, p) for v in j)


def binder_levels(t):
    """Levels in the binder domains of the ∀-telescope of a source statement."""
    out = set()
    while t.get("k") == "prod":
        out |= source_globals(t["ty"], set())
        t = t["b"]
    return out


def dominated(s1, s2):
    """s1 <= s2 for every value of the parameters (normal forms)."""
    c1, p1 = level_nf(s1)
    c2, p2 = level_nf(s2)
    if not all(any(q == p and k <= k2 for q, k2 in p2) for p, k in p1):
        return False
    return not c1 or (c2 is not None and c1 <= c2) or any(c1 <= k2 for _, k2 in p2)


def check_binder_independence(facts, d, params, sol, interp):
    """Statements, independently of the translator: the translated levels of the source binder levels
    (quantification ranges) keep the source's independence — a translated order between two binder
    levels (identification included) must be entailed by the native facts, and a binder level
    translated to a closed level must be forced <= Set. No self-reported default is consulted."""
    def sigma(b):
        if b in interp:
            return interp[b]
        if b in params:
            return {"k": "param", "n": level_param(b)}
        return sol.get(b)
    tr = [(b, sigma(b)) for b in sorted(binder_levels(d["body"]))]
    tr = [(b, x) for b, x in tr if x is not None]
    for b, x in tr:
        c, ps = level_nf(x)
        if not ps and not facts.entails(b, "Set", 0):
            raise Mismatch(f"statement specialized: binder level {b} translated to the closed level {x}")
    for b1, x1 in tr:
        for b2, x2 in tr:
            if b1 != b2 and dominated(x1, x2) and not facts.entails(b1, b2, 0):
                raise Mismatch(f"statement specialized: binder levels {b1} <= {b2} forced by the translation, not by the source")


def check_statement_generality(facts, own, gen, exprs, poly, types):
    """Task C, independently of the translator's own reports (no `universe_level_defaults`/residual
    record is consulted): a statement — or a definition's type — is never specialized at a universe
    level that its source leaves free. For every reference `c.{σ…} a₁ … aₙ` in a statement (the
    statement row's type and value, a definition row's type) and every source level l of c that is
    not a level of the statement (R3, the `else` case: neither a parameter nor an implicit level), the
    argument σ may differ from l's parameter only if
      * the source forces it: l ≤ Set in the native graph (σ closed), or
      * kernel typing determines it at this occurrence: c's Lean parameter for l occurs in the type of
        one of the n applied binders (a cumulativity site: `rel.{0} Nat`, `Equality.sort.{…} T`).
    Otherwise (an unapplied `Equality.type.{0,0}` under a binder, the pre-C translation of opt_eqP) the
    statement ranges over a smaller universe than the source's: rejected (R3G requires u_l). Type
    arguments fixed by sibling arguments (`@Eq A a b`) are not inspected (typing determines them)."""
    for e in exprs:
        for name, us, nargs in app_occurrences(e, [], types):
            if name not in gen or name not in types:
                continue
            k0 = (poly or {}).get(name, 0)
            ty, lps, nh = types[name]
            us_, lps_ = us[k0:], lps[k0:]
            if len(us_) != len(gen[name]) or len(lps_) != len(gen[name]):
                continue                          # (arity mismatch: reported by check_universe_args)
            # (a pending artifact's hypothesis binders do not count: their levels are the translator's
            # choice, not determined by the source)
            binders, t = [], ty
            while t is not None and t.get("k") == "forall" and len(binders) < nargs:
                binders.append(t["t"])
                t = t["b"]
            binders = binders[nh:]
            for l, sigma, p in zip(gen[name], us_, lps_):
                if l in own or l in TEMPLATE_LEVELS:
                    continue                      # (own levels: their parameter, checked by R3; R5)
                # R-CARRIER P2: a row owning a copy of l (one per independent class) owns l (its arguments are
                # checked by R3 / coherence, as for an own level)
                if any(SPLIT_COPIES.get(cp) == l and cp in P2_COPIES for cp in own):
                    continue
                c, ps = level_nf(sigma)
                # (an argument max of own parameters whose source levels are all equal to l in the source graph,
                # <= both ways, is l's reading, not a specialization)
                own_by_param = {level_param(g): g for g in own}
                if (c in (None, 0)) and ps and all(k == 0 and p_ in own_by_param and
                                                   facts.entails(SPLIT_COPIES.get(own_by_param[p_], own_by_param[p_]), l, 0) and
                                                   facts.entails(l, SPLIT_COPIES.get(own_by_param[p_], own_by_param[p_]), 0)
                                                   for p_, k in ps):
                    continue
                # (rule R, general form: an argument over own levels, copies excluded, equal to l at every model
                # of the source facts is l's reading, not a specialization)
                plain_own = {pp: g for pp, g in own_by_param.items() if g not in SPLIT_COPIES}
                if ps and level_param(l) not in plain_own and equal_at_models(
                        facts, {**plain_own, level_param(l): l}, sigma, {"k": "param", "n": level_param(l)}):
                    continue
                if not ps and facts.entails(l, "Set", 0):
                    continue
                if any(mentions_param(b, p) for b in binders):
                    continue
                raise Mismatch(f"{name}: source level {l} is free in the statement (not determined by the reference's "
                               f"arguments, not forced by the source graph) but its argument is {sigma}, not the "
                               f"parameter {level_param(l)}: the statement is specialized (R3G)")


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
    # (statement mode: a statement definition's type levels are the statement's own levels)
    tl = set(source_globals(d["type"], set())) | set(d.get("statement_levels") or [])
    own = tl | source_globals(d["body"], set())
    implicit = set(r.get("implicit_levels") or [])
    # (statement mode: an implicit level may be a body level shared with a referenced declaration; it
    # must not occur explicitly in the type, and must be the argument of a reference for it, checked
    # with the universe arguments)
    if implicit & (tl if STATEMENT_MODE[0] else own):
        raise Mismatch(f"implicit levels {sorted(implicit & (tl if STATEMENT_MODE[0] else own))} occur explicitly in the source")
    tl, own = tl | implicit, own | implicit
    sol = {x["level"]: x["sigma"] for x in r.get("solved_levels", [])}
    interp = {x["level"]: x["sigma"] for x in r.get("level_interp") or []}
    if interp:
        if FACTS is None:
            raise Mismatch("level interpretation without native facts")
        if not set(interp) <= tl or set(interp) & set(sol):
            raise Mismatch(f"interpreted levels {sorted(interp)} must be type or implicit levels {sorted(tl)}, not solved ones")
        want = own_level_interp(FACTS, sorted(interp), set(source_globals(d["type"], set())) | source_globals(d["body"], set()),
                                rs_deps(DECL_SRC.get(d["name"], d)))
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


def check_body_levels(facts, d, sol, params=None, admit=frozenset(), prop_offset=False, relaxed=None):
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
            # (only for the reported levels: R2B-P proof-local ones, R2B-S result-sort ones)
            off = prop_offset and a == "Set" and (relaxed is None or b in relaxed)
            if not leq(summ(a), summ(b), 1 if (r == "lt" and not off) else 0):
                raise Mismatch(f"proof-local level solution violates the native fact {a} {r} {b}")


def only_in_result_sort(ty, l):
    """R2B-S applicability (independent): l occurs in the source type forall xs, Sort s only in s."""
    while ty["k"] == "prod":
        if l in source_globals(ty["ty"], set()):
            return False
        ty = ty["b"]
    return ty["k"] == "sort" or l not in source_globals(ty, set())


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


def universe_and_instance_checks(lines, decls, rows, metadata_path, problem, aliases=(), statements=frozenset(), definitions=frozenset(),
                                 protected=frozenset()):
    """Universe interpretation (R3), body levels (R2S/R2B), residuals and typing-determined instance
    levels of every accepted row (`rows`: source name -> result row with status
    TRANSLATED_AND_CHECKED for the rows to check). Returns (universe arguments checked, recursors)."""
    # Universe interpretation (rule R3), checked independently of the translator.
    facts = Facts(lines[4]) if lines[4].get("kind") == "universe_facts" else None
    global FACTS
    FACTS = facts
    if facts is None:
        problem("universe", "source IR has no native universe facts")
    gen, poly, gen_admit = {}, {}, {}
    # R3G-F: closures in source order (a declaration's dependencies precede it in the merged IR)
    CARRIER_SET.clear()
    DECOUPLED.clear()
    for x in lines:
        cs_ = carrier_levels(x)
        CARRIER_SET.update(cs_)
        if cs_:
            g_ = set(ind_globals(x))
            DECOUPLED.update((l_, m_) for l_ in cs_ for m_ in g_ if m_ != l_)
    RS_CLOSURE.clear()
    DECL_SRC.clear()
    DECL_SRC.update({x["name"]: x for x in lines if x.get("kind") in ("constant", "inductive")})
    for x in lines:
        if x.get("kind") in ("constant", "inductive") and x["name"] in rows:
            cl = rs_deps(x) | set(rows[x["name"]].get("result_sort_implicit_levels") or [])
            if cl:
                RS_CLOSURE[x["name"]] = cl
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
    # R3G-F: the result-sort-only levels of each generated inductive type, from its source (and its own
    # R3G-F levels, themselves checked when that row is audited)
    t2s_ = {}
    for s_, r_ in rows.items():
        if r_.get("status") == "TRANSLATED_AND_CHECKED" and r_.get("target"):
            for t_ in [r_["target"]] + [c["name"] for c in r_.get("target_ctors") or []]:
                t2s_[t_] = s_
    ro_memo = {}

    def ro_of(nm):
        """Levels result-sort-only at references to target nm: an inductive's source result-sort-only levels
        and its own R3G-F levels, and (any declaration) the R3G-F levels of its dependency closure that are
        not levels of its own source."""
        if nm not in ro_memo:
            s_ = t2s_.get(nm)
            if not s_:
                ro_memo[nm] = set()
            else:
                d0 = DECL_SRC.get(s_, decls[s_])
                if d0["kind"] == "inductive":
                    expl = set(ind_globals(d0))
                    own_ro = result_only_levels(d0) | set(rows[s_].get("result_sort_implicit_levels") or [])
                else:
                    expl = set(source_globals(d0["type"], set())) | source_globals(d0.get("body"), set())
                    own_ro = set()
                ro_memo[nm] = own_ro | (rs_deps(d0) - expl)
        return ro_memo[nm]
    # R-SPLIT: at references, a copy stands for its source level (an argument `a <= l`: R3)
    # R-CARRIER P2: the positions of P2 copies (level_copies) are recorded: there the shared-level coherence
    # does not apply (an argument a <= l, R3 entailment)
    GEN_COPY_POS.clear()
    for n_ in gen:
        GEN_COPY_POS[n_] = {k for k, x in enumerate(gen[n_]) if x in P2_COPIES}
        gen[n_] = [SPLIT_COPIES.get(x, x) for x in gen[n_]]
    # assembly: a final theorem `Rocq.<leaf>` has the universe parameters of its accepted statement
    for t_, src_ in aliases:
        st_ = (rows.get(src_) or {}).get("target")
        if st_ in gen:
            gen[t_] = gen[st_]
            poly[t_] = poly.get(st_, 0)
            gen_admit[t_] = gen_admit.get(st_, set())
    univ_checked = 0
    # target types (for the statement-generality check: which universe parameters an applied argument
    # determines)
    types = {n_: (t_, ps_, 0) for n_, (t_, ps_) in BOOT_TYPES.items()}
    for r_ in rows.values():
        if r_.get("status") == "TRANSLATED_AND_CHECKED" and r_.get("target_type") is not None:
            nh = len(r_.get("pending_hypotheses") or [])
            types[r_["target"]] = (r_["target_type"], r_.get("level_params") or [], nh)
            for c in r_.get("target_ctors") or []:
                types[c["name"]] = (c["type"], r_.get("level_params") or [], nh)
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
                    # R2B-P / R2B-S: the relaxed levels must be reported, R2B-P ones proof-local (not in the
                    # source type; their source instance is checked at verify), R2B-S ones only in the
                    # type's result sort (a type definition at its value's level)
                    rp = {x["level"] for x in r_.get("r2bp_levels") or []}
                    rs = {x["level"] for x in r_.get("sort_lowered_levels") or []}
                    tyg = set(source_globals(d_["type"], set()))
                    # R2B-P levels of the statement must be reported as such (a specialization of the
                    # source statement; verify re-checks the instance and refuses it on requested roots)
                    marked = {x["level"] for x in r_.get("r2bp_levels") or [] if x.get("in_type")}
                    if (rp & tyg) != marked:
                        raise Mismatch(f"R2B-P levels of the source type {sorted(rp & tyg)} reported as {sorted(marked)}")
                    for l_ in rs:
                        if not only_in_result_sort(d_["type"], l_):
                            raise Mismatch(f"R2B-S level {l_} occurs in the source type outside its result sort")
                    # R2B-V (docs/UNIVERSE_FAMILY_C.md §4), independently: a result sort taken from the
                    # value is allowed on a type-valued definition only (never a statement), for levels
                    # of the source result sort only, each solved to a lowering (no raising)
                    if r_.get("result_sort_inherited"):
                        if not rs:
                            raise Mismatch("R2B-V without lowered result-sort levels")
                        if s_ in statements:
                            raise Mismatch("R2B-V on a statement")
                        t_ = d_["type"]
                        while t_["k"] == "prod":
                            t_ = t_["b"]
                        if t_["k"] != "sort":
                            raise Mismatch("R2B-V on a definition whose source type does not end in a sort")
                        # the target result sort is a Type (never Prop: Prop ≤ Type cumulativity is
                        # not a level lowering)
                        tt_ = r_.get("target_type")
                        while tt_ is not None and tt_.get("k") == "forall":
                            tt_ = tt_["b"]
                        if tt_ is None or tt_.get("k") != "sort":
                            raise Mismatch("R2B-V: the target type does not end in a sort")
                        c0_, ps0_ = level_nf(tt_["l"])
                        if not ((c0_ or 0) >= 1 or any(k >= 1 for _, k in ps0_)):
                            raise Mismatch("R2B-V: the target result sort may be Prop (not a level lowering)")
                        back_ = {level_param(g): g for g in params}
                        res_lv = source_globals(t_, set())
                        for x in r_.get("sort_lowered_levels") or []:
                            l_ = x["level"]
                            if l_ not in res_lv:
                                raise Mismatch(f"R2B-V: level {l_} does not occur in the source result sort")
                            c_, ps_ = level_nf(x["sigma"])
                            if not ((c_ is None or facts.entails("Set", l_, c_)) and
                                    all(p in back_ and facts.entails(back_[p], l_, k) for p, k in ps_)):
                                raise Mismatch(f"R2B-V: result-sort level {l_} solved to {x['sigma']}, not a lowering")
                    # (R2B-V: the replaced result-sort levels are checked as lowerings below, not as
                    # solutions: they have no counterpart in the target)
                    inh_ = {x["level"] for x in r_.get("sort_lowered_levels") or []} if r_.get("result_sort_inherited") else set()
                    check_body_levels(facts, d_, {k: v for k, v in sol_only.items() if k not in inh_}, params, own_admit,
                                      bool(r_.get("universe_cumulativity")), rp | rs)
                    bl = {**sol_only, **interp_}            # coherence: an own level's argument is its image
                    # R3G: an implicit level must be the source level of a parameter of a referenced
                    # declaration, and occur as that parameter's argument in the accepted terms
                    for l in r_.get("implicit_levels") or []:
                        want = level_nf(interp_[l] if l in interp_ else {"k": "param", "n": level_param(l)})
                        if not any(len(us) - (poly or {}).get(nm, 0) == len(gen[nm]) and any(
                                g == SPLIT_COPIES.get(l, l) and level_nf(u) == want
                                for g, u in zip(gen[nm], us[(poly or {}).get(nm, 0):]))
                                for e_ in exprs if e_ is not None for nm, us in const_occurrences(e_, []) if nm in gen):
                            raise Mismatch(f"implicit level {l} is not the argument of a reference for that level")
                else:
                    # an inductive block's own levels: its parameters, and (template blocks) its solved levels;
                    # for a non-template block, an argument for an own level must be its R2F interpretation
                    params_i, bl, tb_i = ind_params(d_, r_)
                    own = set(params_i)
                    if tb_i is None and not r_.get("plain_levels"):
                        bl = own_level_interp(facts, params_i, set(ind_globals(d_)),
                                              rs_deps(d_) | set(r_.get("result_sort_implicit_levels") or []))     # explicit and implicit levels (R2F)
                    self_n = {r_.get("target")} | {c["name"] for c in r_.get("target_ctors", [])}
                    RSI_CHECKED[0] += check_result_sort_implicit(facts, d_, r_, gen, ro_of)
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
                                                    gen_admit, own_admit, bool(r_.get("universe_cumulativity")),
                                                    bool(r_.get("universe_lowered")))
                if d_["kind"] == "inductive" and s_ in definitions:
                    # an inductive block: the binder domains of its arity and of its constructors
                    # (parameters and fields: quantification ranges); its own references are at its own
                    # parameters by construction
                    nh, ind_exprs = len(r_.get("pending_hypotheses") or []), []
                    for x in [r_.get("target_type")] + [c["type"] for c in r_.get("target_ctors") or []]:
                        for _ in range(nh):
                            if x is not None and x.get("k") == "forall":
                                x = x["b"]
                        while x is not None and x.get("k") == "forall":
                            ind_exprs.append(x["t"])
                            x = x["b"]
                    try:
                        check_statement_generality(facts, own, gen_, ind_exprs, poly, types)
                    except Mismatch as e:
                        if s_ in protected:
                            raise Mismatch(f"protected public declaration with a narrowed quantification range: {e}")
                        DEF_TYPE_CANDIDATES.append({"declaration": s_, "message": str(e)})
                if s_ in statements:
                    check_binder_independence(facts, d_, set(params), sol_only, interp_)
                if s_ in statements or (d_["kind"] == "constant" and s_ in definitions):
                    # a statement: all of it; a definition: the binder domains of its type (its
                    # quantification ranges). The hypothesis telescope (prerequisite statements at the
                    # levels the declaration uses them) is peeled.
                    nh, stmt_exprs = len(r_.get("pending_hypotheses") or []), []
                    for x in (r_.get("target_type"), r_.get("target_value") if s_ in statements else None):
                        for _ in range(nh):
                            if x is not None and x.get("k") in ("forall", "lam"):
                                x = x["b"]
                        if x is None:
                            continue
                        if s_ in statements:
                            stmt_exprs.append(x)
                        else:
                            while x.get("k") == "forall":
                                stmt_exprs.append(x["t"])
                                x = x["b"]
                    try:
                        check_statement_generality(facts, own, gen_, stmt_exprs, poly, types)
                    except Mismatch as e:
                        if s_ in statements:
                            raise
                        if s_ in protected:
                            raise Mismatch(f"protected public declaration with a narrowed quantification range: {e}")
                        # a non-protected definition: diagnostic (as R3-down / residual defaults, library
                        # definitions may be instantiated below the source; their effect on protected
                        # declarations is checked there)
                        DEF_TYPE_CANDIDATES.append({"declaration": s_, "message": str(e)})
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
    return univ_checked, recursors, inst


def main(src_path, contract_path, report_path, out_path, metadata_path=None, assembly=None, validated=None):
    from collections import Counter
    lines = [json.loads(l) for l in open(src_path)]
    if statement_mode(lines[0]):
        return main_statement(lines, src_path, contract_path, report_path, out_path, metadata_path, assembly, validated)
    if assembly:
        print("assembly audit requires a statement-mode export", file=sys.stderr)
        return 2
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
    # P0 interface protection, recomputed independently (not via tools/protection.py): the pinned
    # manifest's digest, the protected names present in the audited source, the contract's binding,
    # and every accepted protected row keeping its full statement (no R2B-S, no R2B-P statement level).
    # Whether those relaxations happened is itself checked independently by the universe checks below
    # (a row that hides a relaxation fails its strict level check).
    import hashlib
    root_dir = Path(__file__).resolve().parent.parent
    iface_checked = 0
    try:
        pin = json.load(open(root_dir / "tools" / "protected_interface.pin.json"))
        mbytes = (root_dir / pin["manifest"]).read_bytes()
        msha = hashlib.sha256(mbytes).hexdigest()
        if msha != pin["sha256"]:
            problem("interface", "protected-interface manifest differs from its pin")
        prot = set(json.loads(mbytes)["protected"]) & set(decls)
        cp = con.get("protection") or {}
        if cp.get("manifest_sha256") != msha or cp.get("protected") != sorted(prot):
            problem("interface", "contract protection binding differs from the pinned manifest for this source")
        rp = report.get("protection") or {}
        if rp.get("protected_in_export") != len(prot) or rp.get("manifest_sha256") != msha:
            problem("interface", "the translation was not run under this protection binding")
        for r_ in results:
            if bool(r_.get("protected")) != (r_.get("source") in prot):
                problem("interface", f"{r_.get('source')}: protection flag differs from the pinned manifest")
            if r_.get("source") in prot and r_.get("status") == "TRANSLATED_AND_CHECKED":
                iface_checked += 1
                if r_.get("sort_lowered_levels") or any(x.get("in_type") for x in r_.get("r2bp_levels") or []):
                    problem("interface", f"{r_.get('source')}: protected public declaration translated with a specialized statement")
    except (OSError, KeyError, ValueError) as e:
        problem("interface", f"protection data unreadable: {e}")
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
    univ_checked, recursors, inst = universe_and_instance_checks(lines, decls, rows, metadata_path, problem)
    aud = Auditor(decls, list(rows.values()), recursors)
    for s in sorted(decls):
        r, d = rows.get(s), decls[s]
        COERCE[0] = bool(r and r.get("prop_lift_coercions"))
        v = {"source": s, "status": r.get("status") if r else None,
             "role": "root" if s in canon else ("required" if s in closure else "extra_not_required")}
        try:
            if r is None:
                raise Mismatch("no unique result row")
            if r["status"] == "TRANSLATED_AND_CHECKED" and d["kind"] == "inductive":
                check_coinductive(d, r)
                if len(d["bodies"]) != 1:
                    raise Mismatch("UNAUDITABLE: mutual block")
                b = d["bodies"][0]
                t, cs = generated_names(d["name"], b["name"], [c["name"] for c in b["ctors"]])
                if r["target"] != t or [c["name"] for c in r["target_ctors"]] != cs:
                    raise Mismatch(f"target names {r['target']} / {r['target_ctors']} are not the images of the source")
                # M6: non-uniform parameters are Lean indices; the uniform count is the native
                # (round-trip-checked) nparams_rec
                nrec = (d.get("native") or {}).get("nparams_rec", d["npars"])
                if r.get("num_params") != nrec or nrec > d["npars"]:
                    raise Mismatch("parameter count differs from the source's uniform parameters")
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
                src_ar, tgt_ar = b["type"], r["target_type"]
                if r.get("sort_interp") and not (tb is None and r.get("plain_levels")):
                    raise Mismatch("sort_interp reported for a block without plain parameters")
                if tb is None and r.get("plain_levels"):
                    aud.body = None               # M6: plain parameters (u_l itself for every level)
                    if r.get("sort_interp"):
                        if FACTS is None:
                            raise Mismatch("sort_interp without native facts")
                        src_ar, tgt_ar = split_sort_interp(b["type"], r["target_type"], own_level_interp(
                            FACTS, params0, set(ind_globals(d)), rs_deps(d) | set(r.get("result_sort_implicit_levels") or [])))
                elif tb is None:
                    aud.body = own_level_interp(FACTS, params0, set(ind_globals(d)), rs_deps(d) | set(r.get("result_sort_implicit_levels") or [])) if FACTS is not None else None   # explicit and implicit levels
                else:
                    if FACTS is not None:
                        check_body_levels(FACTS, d, sol0, params0)
                    aud.body = sol0
                try:
                    aud.check(src_ar, tgt_ar, ["arity"])
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
                    body_s = d["body"]
                    m6 = [n_ for n_ in (r.get("delta_inlined") or []) if n_ not in ERASED.get(s, ())]
                    if m6:
                        # M6: Set-motive constants used at a Prop family, inlined (definitional)
                        for n_ in m6:
                            if n_ not in aud.ir_bodies or not has_set_motive(decls[n_]["type"]):
                                raise Mismatch(f"inlined {n_} is not a transparent constant with a Set-motive binder")
                        body_s = inline_consts(body_s, set(m6), aud.ir_bodies)
                    aud.check(body_s, strip_prop_lift(r, r["target_value"], d["type"], aud.body), ["body"])
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
           "interface_checked": iface_checked,
           "instance_levels": {"checked": inst.checked, "deferred_to_consumer": inst.deferred},
           "coverage": {"requested_roots": len(canon), "required_closure": len(closure), "accepted": len(accepted),
                        "extra_exported": sorted(set(decls) - closure)},
           "problems": problems, "verdicts": verdicts}
    json.dump(out, open(out_path, "w"), indent=2)
    print(out["status"], f"({len(problems)} problem(s))")
    return 0 if not problems else 1


# ---------- statement mode (docs/STATEMENT_ONLY_DESIGN.md) ----------

LEAF_STATES = ("statement_only", "obligation", "opaque_interface")
ACCEPTED_ST = ("TRANSLATED_AND_CHECKED", "BOOTSTRAP_RESOLVED", "STATEMENT_KERNEL_CHECKED")
PENDING_ST = ("PENDING_KERNEL_CHECKED", "STATEMENT_PENDING_KERNEL_CHECKED")
_PROP = {"k": "sort", "s": {"k": "prop"}}
_SET_SORT = {"k": "sort", "s": {"k": "type", "u": [{"l": {"k": "set"}, "n": 0}]}}


def statement_mode(header):
    m = header.get("mode")
    return isinstance(m, dict) and m.get("name") == "statement"


def is_leaf(d):
    """A proof task: a proof-valued constant, an extracted obligation or opaque data (from the source
    record alone: its body state, set by the exporter's statement preparation)."""
    return d["kind"] == "constant" and d.get("body_state") in LEAF_STATES


def statement_view(d):
    """The declaration the translator builds for a source declaration (independently restated): a
    leaf `c : T` becomes `def c.statement : Prop := T` (`c.type : s := T` for opaque data of native
    sort s); every other declaration is itself."""
    if not is_leaf(d):
        return d, ""
    lv = sorted(source_globals(d["type"], set()))     # a statement definition's levels: the statement's
    if d["body_state"] == "opaque_interface":
        if d.get("type_sort") is None:
            raise Mismatch("opaque data without its native sort")
        # declared at the sort Lean infers for the type (audited as a sort, contributes no levels)
        return dict(d, type=_SET_SORT, body=d["type"], body_state="transparent", statement_levels=lv), ".type"
    if d.get("body") is not None:
        raise Mismatch("a proof task exported with a body")
    return dict(d, type=_PROP, body=d["type"], body_state="transparent", statement_levels=lv), ".statement"


def check_hyp_telescope(rows, leaves, hs, hyp_t):
    """The hypothesis telescope of a pending artifact: one binder per prerequisite, in the reported
    order, each the prerequisite's statement (its own pending artifact applied to its own hypotheses,
    which must come earlier)."""
    seen_t = {}
    for i, (l, t) in enumerate(zip(hs, hyp_t)):
        lr = rows.get(l)
        if lr is None or l not in leaves or lr["status"] not in ("STATEMENT_KERNEL_CHECKED", "STATEMENT_PENDING_KERNEL_CHECKED"):
            raise Mismatch(f"hypothesis {l} is not a translated proof task")
        # P3: a prerequisite may have one hypothesis per universe instance, never two at the same type
        # (its own hypotheses are resolved to a hypothesis of the right leaf, below)
        key = json.dumps(canon_levels(t), sort_keys=True)
        if key in seen_t.setdefault(l, set()):
            raise Mismatch(f"prerequisite {l} has two hypotheses at the same type")
        seen_t[l].add(key)
        cur, earlier = t, hs[:i]
        for h in reversed(lr.get("pending_hypotheses") or []):
            ids = [j for j, x in enumerate(earlier) if x == h]
            if not ids or cur.get("k") != "app" or cur["a"] not in [{"k": "bvar", "i": i - 1 - j} for j in ids]:
                raise Mismatch(f"hypothesis {l}: its statement is not applied to the hypothesis of {h}")
            cur = cur["f"]
        if cur.get("k") != "const" or cur["n"] != lr["target"]:
            raise Mismatch(f"hypothesis {l}: type is not its statement {lr['target']}")


def check_termination_statement(r, used, rows=None, leaves=None):
    """B: `def <leaf>.statement : Prop := ∀ Γ, ∀ s : C, Acc C R s`; its parent's audited termination
    lowering applies it (as hypothesis or final theorem) to the locals Γ and the decreasing argument, so
    the kernel identifies its C and R with the lowering's carrier and call relation (whose shape the
    parent's audit checked against the source's recursive calls).
    B-P (docs/TERMINATION.md): when the call relation mentions prerequisite hypotheses of the parent (a
    pending function in a recursive call's argument), the statement is a pending proof task over them:
    `∀ hs, Prop := fun hs => ∀ Γ, ∀ s : C, Acc C R s`, its hypothesis telescope checked like every pending
    artifact's (each binder a prerequisite's statement applied to the hypotheses of its own prerequisites)."""
    if not used:
        raise Mismatch("not used by its constant's audited termination lowering")
    hs = r.get("pending_hypotheses") or []
    ty, e = r.get("target_type"), r.get("target_value")
    hyp_t = []
    for i, l in enumerate(hs):
        if ty.get("k") != "forall" or e.get("k") != "lam" or ty["t"] != e["t"]:
            raise Mismatch(f"termination statement: hypothesis {i} ({l}) missing or differing between type and value")
        hyp_t.append(ty["t"])
        ty, e = ty["b"], e["b"]
    if hs:
        if rows is None or leaves is None:
            raise Mismatch("a termination statement with hypotheses outside a pending telescope check")
        check_hyp_telescope(rows, leaves, hs, hyp_t)
    if ty != {"k": "sort", "l": {"k": "zero"}}:
        raise Mismatch("a termination statement is not a Prop")
    prev = None
    while e.get("k") == "forall":
        prev, e = e, e["b"]
    h, a = Auditor.unspine(e)
    if prev is None or h.get("k") != "const" or h.get("n") != "Acc" or len(a) != 3 or a[2] != {"k": "bvar", "i": 0} \
            or a[0] != lift(prev["t"], 1):
        raise Mismatch("a termination statement is not ∀ Γ, ∀ s : C, Acc C R s")


def check_unfolding_equation(aud, pd, prow, r, leaves, tele_rows):
    """B: the unfolding equation of `c := λ outer, fix f args := B`:
    ∀ outer args, self outer args = ⟦B⟧[f := self outer], with `self` the constant's target (applied to
    the hypotheses of its own telescope when pending), restated here from the source: the binder
    types and ⟦B⟧ are compared with the source term by term (the fixpoint body as `check_fix` reads it),
    the recursive function denoting `self outer`."""
    hs = r.get("pending_hypotheses") or []
    ty, val = r["target_type"], r["target_value"]
    hyp_t = []
    for i, l in enumerate(hs):
        if ty.get("k") != "forall" or val.get("k") != "lam" or ty["t"] != val["t"]:
            raise Mismatch(f"hypothesis {i} ({l}) missing or differing between type and value")
        hyp_t.append(ty["t"])
        ty, val = ty["b"], val["b"]
    check_hyp_telescope(tele_rows, leaves, hs, hyp_t)
    if ty != {"k": "sort", "l": {"k": "zero"}}:
        raise Mismatch("an unfolding equation is not a Prop")
    if prow is None:
        raise Mismatch("its constant has no row")
    ph = prow.get("pending_hypotheses") or []
    if any(h not in hs for h in ph):
        raise Mismatch("its constant's hypotheses are not among the equation's")
    olams, b = [], pd["body"]
    while b["k"] == "lam":
        olams.append(b)
        b = b["b"]
    if b["k"] != "fix" or len(b["defs"]) != 1 or b["idx"] != 0:
        raise Mismatch("its constant's body is not λ outer, fix f := …")
    d = b["defs"][0]
    fbody = zeta_fix_lets(inline_rec_args(d["body"], [d["rarg"] + 1], aud.ir_bodies), 1)
    flams, fb = [], fbody
    while fb["k"] == "lam":
        flams.append(fb)
        fb = fb["b"]
    o, a, nh = len(olams), len(flams), len(hs)
    env = [("hyp", l, nh - 1 - i) for i, l in enumerate(hs)][::-1]
    cur = val
    for i, lam in enumerate(olams):
        if cur.get("k") != "forall":
            raise Mismatch(f"missing binder for outer argument {i}")
        aud.check(lam["ty"], cur["t"], ["unfold", f"outer{i}"], env)
        env = aud.push(env)
        cur = cur["b"]
    selfo = {"k": "const", "n": prow["target"], "u": [{"k": "param", "n": l} for l in prow.get("level_params", [])]}
    for h in ph:
        selfo = {"k": "app", "f": selfo, "a": {"k": "bvar", "i": Auditor.hyp_index(env, h, ["unfold"])}}
    for i in range(o):
        selfo = {"k": "app", "f": selfo, "a": {"k": "bvar", "i": o - 1 - i}}
    fenv, tenv = [("tgt", selfo)] + list(env), list(env)
    for i, lam in enumerate(flams):
        if cur.get("k") != "forall":
            raise Mismatch(f"missing binder for argument {i}")
        aud.check(lam["ty"], cur["t"], ["unfold", f"arg{i}"], fenv)
        fenv, cur = aud.push(fenv), cur["b"]
    eh, ea = Auditor.unspine(cur)
    if eh.get("k") != "const" or eh.get("n") != "Eq" or len(ea) != 3:
        raise Mismatch("not an equation")
    fty = d["ty"]
    for i in range(a):
        if fty["k"] != "prod":
            raise Mismatch("the fixpoint's type has fewer binders than its body's lambdas")
        tenv, fty = aud.push(tenv), fty["b"]
    aud.check(fty, ea[0], ["unfold", "type"], tenv)
    lhs = lift(selfo, a)
    for i in range(a):
        lhs = {"k": "app", "f": lhs, "a": {"k": "bvar", "i": a - 1 - i}}
    if ea[1] != lhs:
        raise Mismatch("the left side is not the constant applied to its arguments")
    aud.check(fb, ea[2], ["unfold", "rhs"], fenv)


def pending_target_name(key):
    return "RocqPending." + target_name(key)[len("Rocq."):]


def main_statement(lines, src_path, contract_path, report_path, out_path, metadata_path=None, assembly=None, validated=None):
    """Statement-mode audit. Every row the translator claims (accepted: TRANSLATED_AND_CHECKED,
    BOOTSTRAP_RESOLVED, STATEMENT_KERNEL_CHECKED; pending: PENDING_KERNEL_CHECKED,
    STATEMENT_PENDING_KERNEL_CHECKED) is audited against the source: its statement view (above), its
    prerequisites (recomputed: the leaves it reaches directly or through pending definitions), its
    hypothesis telescope, and its type and value term by term with every leaf reference a hypothesis.
    Rows the translator did not claim are reported, not accepted. No original proof body exists in the
    source (the exporter dropped them); a body on a proof task is refused."""
    from collections import Counter
    import hashlib
    STATEMENT_MODE[0] = True
    decls = {d["name"]: d for d in lines if d["kind"] in ("constant", "inductive")}
    con = json.load(open(contract_path))
    report = json.load(open(report_path))
    results = report.get("results", [])
    problems, verdicts = [], []

    def problem(det, msg):
        problems.append({"detector": det, "message": msg})

    ir_sha = sha256_path(src_path)
    if con.get("ir_sha256") != ir_sha:
        problem("binding", "contract IR digest differs from the audited source")
    if report.get("input_sha256") != ir_sha:
        problem("binding", "report input digest differs from the audited source")
    if report.get("run_id") != con.get("run_id"):
        problem("binding", "report run id differs from the contract")
    if con.get("mode") != "statement":
        problem("binding", "the contract is not a statement-mode contract")
    # coverage: one row per exported declaration, roots and closure recomputed
    request = con.get("request") or []
    src_roots = lines[1]["roots"]
    if not request or [r["requested"] for r in src_roots] != request:
        problem("coverage", "source root records differ from the contract request")
    canon = [r["name"] for r in src_roots]
    if [c["canonical"] for c in con.get("roots", [])] != canon:
        problem("coverage", "contract roots differ from the source root records")
    try:
        closure = required_closure(decls, canon)
    except Mismatch as e:
        closure = set()
        problem("coverage", str(e))
    if sorted(closure) != con.get("required_closure"):
        problem("coverage", "contract closure differs from the closure recomputed from the source")
    if sorted(decls) != con.get("exported"):
        problem("coverage", "contract export list differs from the source")
    # B (docs/TERMINATION.md): rows the translator generated for an exported constant: the statement
    # of a termination obligation of its termination lowering, its unfolding equation
    SYN_SUFFIX = {"termination": "__rocq2lean_termination_", "unfolding_equation": "__rocq2lean_unfold_"}
    syn = {}
    for r_ in results:
        par = r_.get("synthesized_from")
        if not par:
            continue
        suf, sname = SYN_SUFFIX.get(r_.get("synthetic_kind")), r_.get("source", "")
        if suf and par in decls and decls[par]["kind"] == "constant" and sname.startswith(par + suf) \
                and sname[len(par + suf):].isdigit() and sname not in decls:
            syn[sname] = r_
        else:
            problem("coverage", f"{sname}: generated row not attached to an exported constant")
    counts = Counter(r.get("source") for r in results)
    for s_, n in counts.items():
        if n != 1 or (s_ not in decls and s_ not in syn):
            problem("coverage", f"{s_}: {n} result rows / not exported")
    for s_ in decls:
        if counts[s_] == 0:
            problem("coverage", f"{s_}: exported declaration has no result")
    rows = {r["source"]: r for r in results if counts[r.get("source")] == 1 and (r.get("source") in decls or r.get("source") in syn)}
    st = lambda x: rows.get(x, {}).get("status")
    # entry 14: a block translated with erasing polymorphic definitions δβ-inlined is audited against its
    # inlined source; the inlined names must be erasing definitions (recomputed here from the source), and
    # each must actually occur in the block
    ERASED.clear()
    # rule P, statements (docs/PROP_LIFT.md §3.3): a statement translated with a lifted codomain stated as
    # its proposition; the reported chain is recomputed here from the source (the head-δ chain of the
    # codomain, transparent monomorphic constants, ending at a definition translated with a lifted value),
    # never for a protected declaration, and the statement is audited against the source with the chain
    # δβ-inlined (Rocq conversion)
    prot_pin = PROTECTED_PIN()
    # rule Q-a (docs/PHANTOM_SORT.md): a row translated with phantom checks' sort arguments lowered is
    # audited against the source with those arguments marked; the reported levels must be exactly the
    # levels that occur only there (recomputed here), and the phantom definitions are recomputed too
    pdefs = {n_: ps for n_, d_ in decls.items() if (ps := phantom_def_pairs(d_))}
    for n, r in sorted(rows.items()):
        pl_ = r.get("phantom_lowered") or []
        if not pl_ or n not in decls:
            continue
        d = decls[n]
        stmt_ = d.get("body_state") in ("statement_only", "obligation", "opaque_interface")
        parts = [d.get("type")] if stmt_ or d["kind"] != "constant" else [d.get("type"), d.get("body")]
        er = erase_phantom_sorts(parts, pdefs)
        gone = source_globals(parts, set()) - source_globals(er, set())
        if not gone or sorted(gone) != sorted(pl_):
            problem("structure", f"{n}: phantom-lowered levels {pl_} are not the levels occurring only in phantom checks {sorted(gone)}")
            continue
        decls[n] = dict(d, type=er[0], **({} if len(er) == 1 else {"body": er[1]}))
    for n, r in sorted(rows.items()):
        ch = r.get("prop_lift_unfold") or []
        if not ch:
            continue
        try:
            d = decls.get(n)
            if d is None or d["kind"] != "constant" or d.get("body_state") not in ("statement_only", "obligation"):
                raise Mismatch("rule P unfolding reported for a row that is not a statement")
            if n in prot_pin:
                raise Mismatch("rule P unfolding reported for a protected declaration")
            t = d["type"]
            while t.get("k") == "prod":
                t = t["b"]
            want = []
            for _ in range(8):
                hd, args = (t["f"], t["args"]) if t.get("k") == "app" else (t, [])
                c_ = hd.get("c") if hd.get("k") == "const" else None
                if c_ is None:
                    break
                want.append(c_)
                if (rows.get(c_) or {}).get("prop_lift") is not None and st(c_) in ("TRANSLATED_AND_CHECKED", "PENDING_KERNEL_CHECKED"):
                    break
                dc = decls.get(c_)
                if not (dc and dc["kind"] == "constant" and dc.get("body_state") == "transparent" and dc.get("body")
                        and (dc.get("universes") or {}).get("k") == "monomorphic"):
                    break
                t = src_flatten_apps(beta_app(dc["body"], args))
            if want != ch or (rows.get(ch[-1]) or {}).get("prop_lift") is None:
                raise Mismatch(f"rule P unfolding {ch} is not the source codomain's head chain to a lifted definition {want}")
            bodies = {c_: decls[c_]["body"] for c_ in ch[:-1]}
            bodies[ch[-1]] = decls[ch[-1]]["body"]
            def pre(x, k, bodies=bodies):
                if x.get("k") == "app" and x["f"].get("k") == "const" and x["f"]["c"] in bodies:
                    return src_flatten_apps(beta_app(bodies[x["f"]["c"]], x["args"]))
                return None
            decls[n] = dict(d, type=src_rewrite(d["type"], pre))
        except Mismatch as e:
            problem("structure", f"{n}: {e}")
    for n, r in sorted(rows.items()):
        di = r.get("delta_inlined") or []
        if not di or n not in decls:
            continue
        if decls[n]["kind"] == "constant":
            # entry 15: a constant translated with erasing definitions δβ-inlined in its type and value (the
            # other reported names are M6 Set-motive constants, checked where the value is audited)
            bodies = {n_: erasing_poly_body(decls[n_]) for n_ in di if n_ in decls}
            bodies = {k: v for k, v in bodies.items() if v is not None}
            if not bodies:
                continue
            def pre(x, k, bodies=bodies):
                if x.get("k") == "app" and x["f"].get("k") == "const" and x["f"]["c"] in bodies:
                    return src_flatten_apps(beta_app(bodies[x["f"]["c"]], x["args"]))
                return None
            d2 = copy.deepcopy(decls[n])
            d2["type"] = src_rewrite(d2["type"], pre)
            if d2.get("body") is not None:
                d2["body"] = src_rewrite(d2["body"], pre)
            txt = json.dumps([d2["type"], d2.get("body")])
            if d2 == decls[n] or any(f'"c": "{n_}"' in txt for n_ in bodies):
                problem("structure", f"{n}: the reported inlining does not remove the definitions {sorted(bodies)}")
            decls[n] = d2
            ERASED[n] = set(bodies)
            continue
        if decls[n]["kind"] != "inductive":
            continue
        bodies = {}
        for n_ in di:
            b_ = erasing_poly_body(decls[n_]) if n_ in decls else None
            if b_ is None:
                problem("structure", f"{n}: inlined {n_} is not an erasing polymorphic definition")
            else:
                bodies[n_] = b_
        if len(bodies) == len(di):
            d2 = inline_erasing_block(decls[n], bodies)
            if any(json.dumps(d2).count(f'"c": "{n_}"') or json.dumps(d2).count(f'"c":"{n_}"') for n_ in di) or d2 == decls[n]:
                problem("structure", f"{n}: the reported inlining does not remove the definitions {di}")
            decls[n] = d2
    rep_roots = report.get("roots", [])
    if [(r.get("requested"), r.get("name")) for r in rep_roots] != [(r["requested"], r["name"]) for r in src_roots] \
            or any(r.get("status") != st(r.get("name")) for r in rep_roots):
        problem("coverage", "report root records disagree with the contract or with the result rows")
    # R-SPLIT (docs/LEVEL_SPLIT.md): a row translated through the split view is audited against the
    # split view derived here from the source: the reported split must be exactly that one, its copies
    # fresh levels, and the diagonal (every copy renamed back) must give back the source declaration
    SPLIT_COPIES.clear()
    split_checked = 0
    src_levels = set(lines[4].get("levels") or []) if lines[4].get("kind") == "universe_facts" else set()
    for n, r in sorted(rows.items()):
        ls = r.get("level_split") or []
        if not ls:
            continue
        if n not in decls:
            problem("level_split", f"{n}: split reported on a generated row")
            continue
        v, infos = level_split_view(decls[n])
        if v is None or ls != infos:
            problem("level_split", f"{n}: reported split {ls} is not the split derived from the source {infos}")
            continue
        cs = [c for x in infos for c in x["copies"]]
        # (fresh: no source level, not in the declaration; a copy name recurs in another split declaration
        # only for the same level and position, the same universe range)
        if len(set(cs)) != len(cs) or any(c in src_levels or SPLIT_COPIES.get(c, x["level"]) != x["level"] or _occ_paths(decls[n], c)
                                          for x in infos for c in x["copies"]):
            problem("level_split", f"{n}: split copies {cs} are not fresh levels")
            continue
        if level_unsplit(v, infos) != decls[n]:
            problem("level_split", f"{n}: the diagonal of the split view is not the source declaration")
            continue
        if any(level_param(c) not in (r.get("level_params") or []) for c in cs):
            problem("level_split", f"{n}: a split copy is not a universe parameter of the translation")
            continue
        decls[n] = v
        for x in infos:
            for c in x["copies"]:
                SPLIT_COPIES[c] = x["level"]
        split_checked += 1
    # R-CARRIER P2 (docs/CARRIER_LEVELS.md): implicit levels named per independent class. Each reported
    # copy must be a fresh level l__c<k> (k = 0, 1, ...) of an implicit level l of the row (not a level of its
    # source), reported among its implicit levels, and occur in its target type (it stands for an operand
    # class there). Copies then read as l at references (R3), lie below l and inherit l's upper bounds.
    copies_checked = 0
    for n, r in sorted(rows.items()):
        lc = r.get("level_copies") or []
        if not lc:
            continue
        try:
            if n not in decls or decls[n]["kind"] != "constant":
                raise Mismatch("level copies on a row that is not an exported constant")
            src_g = set(source_globals(decls[n]["type"], set())) | source_globals(decls[n].get("body"), set())
            imp = set(r.get("implicit_levels") or [])
            # (a statement row's statement is its value: its type is Prop)
            ty_params = _all_params(r.get("target_value") if str(r.get("status", "")).startswith("STATEMENT_")
                                    else r.get("target_type"), set())
            for x in lc:
                l, cs = x["level"], x["copies"]
                if l in src_g or l not in src_levels:
                    raise Mismatch(f"copied level {l} is not an implicit source level of the row")
                if cs != [f"{l}__c{k}" for k in range(len(cs))] or len(cs) < 2:
                    raise Mismatch(f"copies {cs} of {l} are not l__c0 .. l__c(k-1)")
                for c in cs:
                    if c in src_levels or SPLIT_COPIES.get(c, l) != l or c not in imp:
                        raise Mismatch(f"copy {c} is not a fresh implicit level standing for {l}")
                    if level_param(c) not in ty_params:
                        raise Mismatch(f"copy {c} does not occur in the target type (no operand class)")
            for x in lc:
                for c in x["copies"]:
                    SPLIT_COPIES[c] = x["level"]
                    P2_COPIES.add(c)
            copies_checked += 1
        except Mismatch as e:
            problem("level_copies", f"{n}: {e}")
    # interface protection (as in proof mode, for every claimed row)
    root_dir = Path(__file__).resolve().parent.parent
    iface_checked = 0
    prop_lift_protected = []
    phantom_protected = []
    try:
        pin = json.load(open(root_dir / "tools" / "protected_interface.pin.json"))
        mbytes = (root_dir / pin["manifest"]).read_bytes()
        msha = hashlib.sha256(mbytes).hexdigest()
        if msha != pin["sha256"]:
            problem("interface", "protected-interface manifest differs from its pin")
        prot = set(json.loads(mbytes)["protected"]) & set(decls)
        cp = con.get("protection") or {}
        if cp.get("manifest_sha256") != msha or cp.get("protected") != sorted(prot):
            problem("interface", "contract protection binding differs from the pinned manifest for this source")
        rp = report.get("protection") or {}
        if rp.get("protected_in_export") != len(prot) or rp.get("manifest_sha256") != msha:
            problem("interface", "the translation was not run under this protection binding")
        for r_ in results:
            if bool(r_.get("protected")) != (r_.get("source") in prot):
                problem("interface", f"{r_.get('source')}: protection flag differs from the pinned manifest")
            if r_.get("source") in prot and r_.get("status") in ACCEPTED_ST + PENDING_ST:
                iface_checked += 1
                # (R2B-V: an inherited result sort is the approved representation rule; its conditions are
                # checked independently with the universe checks)
                if (r_.get("sort_lowered_levels") and not r_.get("result_sort_inherited")) or \
                        any(x.get("in_type") for x in r_.get("r2bp_levels") or []):
                    problem("interface", f"{r_.get('source')}: protected public declaration translated with a specialized statement")
                # rule P (C5, docs/PROP_LIFT.md): every lifted position of a protected declaration is listed (an
                # equivalent range, C1, never a narrowed one); a lifted statement codomain is never protected
                if r_.get("prop_lift") is not None or r_.get("prop_lift_coercions"):
                    prop_lift_protected.append({"source": r_["source"], "status": r_["status"],
                                                "value_lift_depth": r_.get("prop_lift"),
                                                "coercions": r_.get("prop_lift_coercions") or 0})
                if r_.get("prop_lift_unfold"):
                    problem("interface", f"{r_.get('source')}: protected statement translated with a lifted codomain unfolded")
                # rule Q-a: a protected declaration's lowered phantom checks are listed (equivalent hypotheses:
                # every instance of a phantom check is inhabited)
                if r_.get("phantom_lowered"):
                    phantom_protected.append({"source": r_["source"], "status": r_["status"], "levels": r_["phantom_lowered"]})
    except (OSError, KeyError, ValueError) as e:
        problem("interface", f"protection data unreadable: {e}")
    # statement views and prerequisites, from the source alone
    views, suffix = {}, {}
    for n, d in decls.items():
        try:
            views[n], suffix[n] = statement_view(d)
        except Mismatch as e:
            problem("structure", f"{n}: {e}")
            views[n], suffix[n] = d, ""
    claimed = {n for n in list(decls) + list(syn) if st(n) in ACCEPTED_ST + PENDING_ST}
    leaves = {n for n in decls if is_leaf(decls[n])} | set(syn)
    # rule H: a proof task's statement, under either target naming (its hypotheses' types)
    HYP_STATEMENTS.update(f(n + ".statement") for n in leaves for f in (target_name, pending_target_name))
    pend_defs = {n for n in claimed if st(n) == "PENDING_KERNEL_CHECKED"}
    # assembly (docs/ASSEMBLY.md): the validated report the assembly started from, and the proof
    # tasks with final theorems; prerequisites are those of the validated library (a carried-over
    # pending artifact keeps them; an assembled row needs all of them proved)
    vrows, proved, manifest = {}, {}, {}
    if assembly:
        vrep = json.load(open(validated))
        vrows = {r["source"]: r for r in vrep.get("results", [])}
        if vrep.get("input_sha256") != ir_sha or vrep.get("run_id") != con.get("run_id"):
            problem("binding", "the validated report is not this run's translation")
        if report.get("validated_report_sha256") != sha256_path(validated):
            problem("binding", "the assembly report is not bound to this validated report")
        man = json.load(open(assembly))
        if report.get("proofs_sha256") != sha256_path(assembly):
            problem("binding", "the assembly report is not bound to this proof manifest")
        manifest = {e["leaf"]: e for e in man.get("proofs", [])}
        for n, r in rows.items():
            if r.get("proof_target") is not None:
                if n not in leaves or (n in decls and decls[n].get("body_state") == "opaque_interface"):
                    problem("proofs", f"{n}: final theorem for a declaration that is not a proof task")
                elif n not in manifest:
                    problem("proofs", f"{n}: final theorem without a manifest proof")
                elif r["status"] != "STATEMENT_KERNEL_CHECKED" or r.get("proof_state") != "PROOF_ASSEMBLED":
                    problem("proofs", f"{n}: final theorem on a statement that is not accepted")
                else:
                    proved[n] = r
        vst = lambda x: vrows.get(x, {}).get("status")
        pend_defs = {n for n in decls if vst(n) == "PENDING_KERNEL_CHECKED"}
    refs = {}
    for n, v in views.items():
        refs[n] = closure_refs([v["type"], v["body"]] if v["kind"] == "constant" else [v["params"], v["bodies"]], set()) - {n}
    # B: a termination-lowered constant needs its termination obligations (which its lowering must
    # use, audited below); a termination statement needs no source reference of its own (B-P: the
    # prerequisites of its constant that its relation mentions are checked below); an unfolding equation
    # needs what its constant needs
    for n, r_ in syn.items():
        par = r_["synthesized_from"]
        if r_["synthetic_kind"] == "termination":
            refs[n] = set()
            refs[par] = refs[par] | {n}
        else:
            refs[n] = refs[par] | {par}
    need_memo = {}

    def need(n, stack=()):
        if n in need_memo:
            return need_memo[n]
        if n in stack:
            raise Mismatch(f"cyclic prerequisites through {n}")
        out = set()
        for x in refs.get(n, ()):
            if x in leaves:
                out |= {x} | need(x, stack + (n,))
            elif x in pend_defs or (x in decls and decls[x]["kind"] == "inductive" and
                                    (vrows.get(x, {}).get("status") if assembly else st(x)) == "PENDING_KERNEL_CHECKED"):
                out |= need(x, stack + (n,))
        need_memo[n] = out
        return out

    for n in sorted(claimed):
        r = rows[n]
        try:
            for x in refs[n]:
                if x not in claimed:
                    raise Mismatch(f"claimed with a dependency that is not claimed: {x} ({st(x)})")
            nd = need(n)
            hs = r.get("pending_hypotheses") or []
            if assembly:
                a_ = r.get("assembly")
                v_ = vrows.get(n) or {}
                keys = ("status", "target", "target_kind", "target_type", "target_value", "target_ctors",
                        "level_params", "pending_hypotheses")
                if a_ == "VALIDATED" or r["status"] in PENDING_ST:
                    if any(r.get(k) != v_.get(k) for k in keys):
                        raise Mismatch(f"{a_} row differs from the validated row")
                if r["status"] in PENDING_ST:
                    if nd <= set(proved) and a_ not in ("ASSEMBLY_REJECTED", "ASSEMBLY_BLOCKED"):
                        raise Mismatch(f"every prerequisite is proved, yet the row stays {a_} (assembly not maximal)")
                elif a_ == "ASSEMBLED":
                    if v_.get("status") not in PENDING_ST or not nd <= set(proved):
                        raise Mismatch(f"assembled although its prerequisites {sorted(nd - set(proved))} have no final theorem")
                    nd = set()
                elif a_ != "VALIDATED":
                    raise Mismatch(f"accepted row with assembly state {a_}")
            # (P3: a prerequisite may occur once per universe instance; check_hyp_telescope checks that
            # its occurrences have different types)
            # B-P (docs/TERMINATION.md): a termination statement's hypotheses are prerequisites of its
            # constant that its call relation mentions (a subset of the constant's recomputed prerequisites,
            # never itself); the kernel checked the statement over exactly them, the telescope its order
            if n in syn and syn[n]["synthetic_kind"] == "termination" and hs:
                par_need = need(syn[n]["synthesized_from"]) - {n}
                if not set(hs) <= par_need:
                    raise Mismatch(f"termination statement hypotheses {sorted(set(hs) - par_need)} are not prerequisites of its constant")
                nd = set(hs)
            if set(hs) != nd:
                raise Mismatch(f"hypotheses {hs} differ from the recomputed prerequisites {sorted(nd)}")
            want = ("STATEMENT_" if n in leaves else "") + ("PENDING_KERNEL_CHECKED" if nd else
                                                            ("KERNEL_CHECKED" if n in leaves else "TRANSLATED_AND_CHECKED"))
            if r["status"] != want and not (r["status"] == "BOOTSTRAP_RESOLVED" and n in BOOTSTRAP and not nd):
                raise Mismatch(f"status {r['status']}, the source and the prerequisites give {want}")
        except Mismatch as e:
            problem("prerequisites", f"{n}: {e}")
    # normalized rows (statement views, hypotheses peeled) for the universe and instance checks
    norm_decls, norm_rows, peeled = dict(decls), {}, {}
    for n, r in rows.items():
        if n in syn:
            continue            # (generated statements: audited structurally below)
        if n not in claimed or r["status"] == "BOOTSTRAP_RESOLVED":
            norm_rows[n] = r
            continue
        norm_decls[n] = views[n]
        norm_rows[n] = dict(r, status="TRANSLATED_AND_CHECKED")
    univ_checked, recursors, inst = universe_and_instance_checks(
        lines, norm_decls, norm_rows, metadata_path, problem, aliases=[(target_name(n), n) for n in proved],
        statements=frozenset(n for n in leaves if n in claimed),
        definitions=frozenset(n for n in claimed if n not in leaves and n not in syn),
        protected=frozenset(claimed) & frozenset(PROTECTED_PIN()))
    # structural fidelity
    acc_rows = [r for n, r in rows.items() if r["status"] in ("TRANSLATED_AND_CHECKED", "BOOTSTRAP_RESOLVED")]
    aud = aud_main = Auditor(decls, acc_rows, recursors)
    aud.leaves = {n: rows[n] for n in leaves if n in claimed}
    aud.pending = {n: (rows[n]["target"], rows[n].get("pending_hypotheses") or []) for n in pend_defs
                   if decls[n]["kind"] == "constant"}
    aud.pending_inds = {n: rows[n] for n in pend_defs if decls[n]["kind"] == "inductive"}
    aud_carried = None
    if assembly:
        # accepted rows: a proved leaf is its final theorem; a carried-over pending artifact is audited
        # against the validated library it comes from (its prerequisites are hypotheses, as validated)
        aud.leaves = {n: rows[n] for n in leaves if n in claimed and n not in proved}
        aud.proved = proved
        aud.pending = {n: (rows[n]["target"], rows[n].get("pending_hypotheses") or []) for n in claimed
                       if st(n) == "PENDING_KERNEL_CHECKED" and decls[n]["kind"] == "constant"}
        aud.pending_inds = {n: rows[n] for n in claimed if st(n) == "PENDING_KERNEL_CHECKED" and decls[n]["kind"] == "inductive"}
        v_acc = [r for n, r in vrows.items() if r["status"] in ("TRANSLATED_AND_CHECKED", "BOOTSTRAP_RESOLVED")]
        aud_carried = Auditor(decls, v_acc, recursors)
        aud_carried.leaves = {n: vrows[n] for n in leaves if vrows.get(n, {}).get("status") in
                              ("STATEMENT_KERNEL_CHECKED", "STATEMENT_PENDING_KERNEL_CHECKED")}
        aud_carried.pending = {n: (vrows[n]["target"], vrows[n].get("pending_hypotheses") or []) for n in pend_defs
                               if decls[n]["kind"] == "constant"}
        aud_carried.pending_inds = {n: vrows[n] for n in pend_defs if decls[n]["kind"] == "inductive"}
        # final theorems: type exactly the accepted statement, value the manifest's template applied to
        # the prerequisites' final theorems (prerequisites: the validated statement's hypotheses)
        for n, r in proved.items():
            try:
                e = manifest[n]
                if r["proof_target"] != target_name(n):
                    raise Mismatch(f"final theorem {r['proof_target']} is not {target_name(n)}")
                want = {"k": "const", "n": r["target"], "u": [{"k": "param", "n": l} for l in r.get("level_params", [])]}
                if r.get("proof_type") != want:
                    raise Mismatch("final theorem's type is not its accepted statement")
                hs_v = (vrows.get(n) or {}).get("pending_hypotheses") or []
                if e.get("prerequisites") != hs_v:
                    raise Mismatch(f"manifest prerequisites {e.get('prerequisites')} differ from the validated {hs_v}")
                spine, cur = [], r.get("proof_value")
                while cur.get("k") == "app":
                    spine.append(cur["a"])
                    cur = cur["f"]
                spine.reverse()
                if cur.get("k") != "const" or cur["n"] != e["template"]:
                    raise Mismatch(f"final theorem's value is not headed by its template {e['template']}")
                if [x.get("n") if x.get("k") == "const" else None for x in spine] != [target_name(h) for h in hs_v] \
                        or any(h not in proved for h in hs_v):
                    raise Mismatch("template not applied to its prerequisites' final theorems")
            except (Mismatch, KeyError, AttributeError) as ex:
                problem("proofs", f"{n}: {ex}")
    wf_users = {}
    for s_ in sorted(decls):
        r, d = rows.get(s_), views[s_]
        COERCE[0] = bool(r and r.get("prop_lift_coercions"))
        v = {"source": s_, "status": r.get("status") if r else None, "leaf": s_ in leaves,
             "role": "root" if s_ in canon else ("required" if s_ in closure else "extra_not_required")}
        try:
            if r is None:
                raise Mismatch("no unique result row")
            if s_ not in claimed:
                v["verdict"] = "NOT_ACCEPTED"
                verdicts.append(v)
                continue
            if r["status"] == "BOOTSTRAP_RESOLVED":
                b = BOOTSTRAP.get(s_)
                if b is None or r["target"] != b["types"][0]:
                    raise Mismatch("bootstrap resolution not in the audited table")
                v["verdict"] = "MATCH"
                verdicts.append(v)
                continue
            hs = r.get("pending_hypotheses") or []
            pending = r["status"] in PENDING_ST
            aud = aud_carried if (aud_carried is not None and pending) else aud_main
            aud.wf_used = []
            tele_rows = vrows if (assembly and pending) else rows
            if d["kind"] == "inductive":
                check_coinductive(d, r)
                b = d["bodies"][0]
                if len(d["bodies"]) != 1:
                    raise Mismatch("UNAUDITABLE: mutual block")
                t, cs = generated_names(d["name"], b["name"], [c["name"] for c in b["ctors"]])
                if pending:
                    t, cs = pending_target_name(t[len("Rocq."):]), [pending_target_name(c[len("Rocq."):]) for c in cs]
                if r["target"] != t or [c["name"] for c in r["target_ctors"]] != cs:
                    raise Mismatch(f"target names {r['target']} are not the images of the source")
                nrec = (d.get("native") or {}).get("nparams_rec", d["npars"])
                if r.get("num_params") != nrec + len(hs) or nrec > d["npars"]:
                    raise Mismatch("parameter count differs from the source's uniform parameters")
                params0, sol0, _ = ind_params(d, r)
                want_lp = [level_param(g) for g in params0]
                if r.get("level_params", []) != want_lp:
                    raise Mismatch(f"universe parameters {r.get('level_params')} are not the generalized globals {want_lp}")
                tb = template_binding(d)
                if bool(r.get("template")) != (tb is not None):
                    raise Mismatch("template status differs from the source kernel record")
                if r.get("sort_interp") and not (tb is None and r.get("plain_levels")):
                    raise Mismatch("sort_interp reported for a block without plain parameters")
                if tb is None and r.get("plain_levels"):
                    aud.body = None
                elif tb is None:
                    aud.body = own_level_interp(FACTS, params0, set(ind_globals(d)), rs_deps(d) | set(r.get("result_sort_implicit_levels") or [])) if FACTS is not None else None
                else:
                    aud.body = sol0
                try:
                    # hypotheses: the leading parameters of the type and of every constructor
                    hyp_t = []
                    ty_t = r["target_type"]
                    for i in range(len(hs)):
                        if ty_t.get("k") != "forall":
                            raise Mismatch(f"missing hypothesis parameter {i}")
                        hyp_t.append(ty_t["t"])
                        ty_t = ty_t["b"]
                    check_hyp_telescope(tele_rows, leaves, hs, hyp_t)
                    henv = [("hyp", l, len(hs) - 1 - i) for i, l in enumerate(hs)][::-1]
                    src_ar = b["type"]
                    if r.get("sort_interp"):
                        if FACTS is None:
                            raise Mismatch("sort_interp without native facts")
                        src_ar, ty_t = split_sort_interp(b["type"], ty_t, own_level_interp(
                            FACTS, params0, set(ind_globals(d)), rs_deps(d) | set(r.get("result_sort_implicit_levels") or [])))
                    aud.check(src_ar, ty_t, ["arity"], henv)
                    self_ref = ("selfp", t, [{"k": "param", "n": l} for l in want_lp], hs) if hs else \
                        ("const", t, [{"k": "param", "n": l} for l in want_lp])
                    for c, tc in zip(b["ctors"], r["target_ctors"]):
                        ct = tc["type"]
                        for i in range(len(hs)):
                            if ct.get("k") != "forall" or ct["t"] != hyp_t[i]:
                                raise Mismatch(f"constructor {c['name']}: hypothesis parameter {i} differs")
                            ct = ct["b"]
                        aud.check(c["type"], ct, ["ctor " + c["name"]], [self_ref] + aud.shift(henv, 0))
                finally:
                    aud.body = None
                v["verdict"] = "MATCH"
                verdicts.append(v)
                continue
            # C: a statement is never specialized; that is checked from the source (binder-level
            # independence, reference generality — universe checks), not from the translator's report of
            # defaulted levels, whose record is checked for consistency (check_residuals)
            want_t = (pending_target_name if pending else target_name)(s_ + suffix[s_])
            if r["target"] != want_t:
                raise Mismatch(f"target name {r['target']} is not {want_t}")
            # A′: opaque data with its prepared body is an opaque constant (Rocq never unfolds Qed;
            # Lean's kernel never unfolds `opaque`); every other definition is a `def`
            want_k = ("statement",) if s_ in leaves else (("opaque",) if d.get("body_state") == "opaque_data" else ("def",))
            if r["target_kind"] not in want_k:
                raise Mismatch(f"{'proof task' if s_ in leaves else 'definition'} emitted as {r['target_kind']}")
            if d.get("body_state") not in ("transparent", "sealed_implementation", "opaque_data"):
                raise Mismatch(f"body state {d.get('body_state')} is not a definition in statement mode")
            if d.get("body_state") == "opaque_data" and (d.get("native") or {}).get("body_kind") != "opaque":
                raise Mismatch("opaque_data whose native body is not opaque")
            ty, val = r.get("target_type"), r.get("target_value")
            if ty is None or val is None:
                raise Mismatch("success claimed without target type/value")
            # the hypothesis telescope: one binder per prerequisite, in the reported order, each the
            # prerequisite's statement (its own pending artifact applied to its own hypotheses)
            hyp_t = []
            for i, l in enumerate(hs):
                if ty.get("k") != "forall" or val.get("k") != "lam" or ty["t"] != val["t"]:
                    raise Mismatch(f"hypothesis {i} ({l}) missing or differing between type and value")
                hyp_t.append(ty["t"])
                ty, val = ty["b"], val["b"]
            check_hyp_telescope(tele_rows, leaves, hs, hyp_t)
            env = [("hyp", l, len(hs) - 1 - i) for i, l in enumerate(hs)][::-1]
            params, sol = own_partition(d, r)
            aud.body = sol
            REDUCE[0] = bool(r.get("sort_fact_reduced"))
            ADMIT[0] = set(r.get("admitting_levels") or [])
            try:
                if decls[s_].get("body_state") == "opaque_interface":
                    # declared at the sort Lean infers for the translated type (the native sort is an
                    # upper bound cumulativity absorbs); the interface itself is the value, audited below
                    if ty.get("k") != "sort":
                        raise Mismatch("opaque-data interface not declared at a sort")
                else:
                    aud.check(d["type"], ty, ["type"], env)
                body_s = d["body"]
                m6 = [n_ for n_ in (r.get("delta_inlined") or []) if n_ not in ERASED.get(s_, ())]
                if m6:
                    for n_ in m6:
                        if n_ not in aud.ir_bodies or not has_set_motive(decls[n_]["type"]):
                            raise Mismatch(f"inlined {n_} is not a transparent constant with a Set-motive binder")
                    body_s = inline_consts(body_s, set(m6), aud.ir_bodies)
                aud.check(body_s, strip_prop_lift(r, val, decls[s_]["type"], aud.body), ["body"], env)
                # B: its termination lowerings use exactly its own termination obligations
                want_wf = sorted(x for x, rx in syn.items() if rx["synthesized_from"] == s_ and rx["synthetic_kind"] == "termination")
                if sorted(aud.wf_used) != want_wf:
                    raise Mismatch(f"termination obligations used by its lowering {sorted(aud.wf_used)} differ from its generated ones {want_wf}")
                wf_users[s_] = list(aud.wf_used)
            finally:
                aud.body = None
                REDUCE[0] = False
                ADMIT[0] = set()
            v["verdict"] = "MATCH"
        except Mismatch as e:
            v["verdict"] = "MISMATCH"
            v["reason"] = str(e)
            problem("structure", f"{s_}: {e}")
        verdicts.append(v)
    # B: generated statements
    for s_ in sorted(syn):
        r = rows.get(s_)
        v = {"source": s_, "status": r.get("status") if r else None, "leaf": True, "role": "generated",
             "synthesized_from": syn[s_]["synthesized_from"], "synthetic_kind": syn[s_]["synthetic_kind"]}
        try:
            if r is None:
                raise Mismatch("no unique result row")
            if s_ not in claimed:
                v["verdict"] = "NOT_ACCEPTED"
                verdicts.append(v)
                continue
            par = r["synthesized_from"]
            if par not in claimed:
                raise Mismatch(f"generated for {par}, which is not claimed")
            pending = r["status"] in PENDING_ST
            aud = aud_carried if (aud_carried is not None and pending) else aud_main
            tele_rows = vrows if (assembly and pending) else rows
            want_t = (pending_target_name if pending else target_name)(s_ + ".statement")
            if r["target"] != want_t or r["target_kind"] != "statement":
                raise Mismatch(f"target {r['target']} ({r['target_kind']}) is not the statement {want_t}")
            if r["synthetic_kind"] == "termination":
                check_termination_statement(r, s_ in wf_users.get(par, []), tele_rows, leaves)
            else:
                check_unfolding_equation(aud, decls[par], rows.get(par), r, leaves, tele_rows)
            v["verdict"] = "MATCH"
        except Mismatch as e:
            v["verdict"] = "MISMATCH"
            v["reason"] = str(e)
            problem("structure", f"{s_}: {e}")
        verdicts.append(v)
    by = Counter((v["status"], v["verdict"]) for v in verdicts)
    if assembly:
        by_asm = Counter(r.get("assembly") for r in rows.values())
    out = {"schema": "rocq2lean-audit-statement/1", "mode": "statement",
           "assembly": ({"proofs_assembled": len(proved), "by_assembly_state": dict(sorted(by_asm.items(), key=str))}
                        if assembly else None),
           "status": "OK" if not problems else "AUDIT_REJECTED",
           "universe_arguments_checked": univ_checked, "interface_checked": iface_checked,
           "prop_lift_protected": sorted(prop_lift_protected, key=lambda x: x["source"]),
           "phantom_lowered_protected": sorted(phantom_protected, key=lambda x: x["source"]), "level_split_checked": split_checked, "result_sort_implicit_checked": RSI_CHECKED[0], "level_copies_checked": copies_checked,
           "instance_levels": {"checked": inst.checked, "deferred_to_consumer": inst.deferred},
           "definition_type_specialization_candidates": {
               "note": "non-protected definitions only (protected ones are rejected): a binder-domain level of the "
                       "type that no applied argument determines and that is not its parameter (it may be fixed by "
                       "the definition's value); diagnostic, not a rejection",
               "count": len(DEF_TYPE_CANDIDATES), "rows": DEF_TYPE_CANDIDATES},
           "coverage": {"requested_roots": len(canon), "required_closure": len(closure), "claimed": len(claimed),
                        "accepted": sum(1 for n in claimed if st(n) in ACCEPTED_ST),
                        "pending": sum(1 for n in claimed if st(n) in PENDING_ST),
                        "not_accepted": len(decls) - len(claimed),
                        "by_status_and_verdict": {f"{a}/{b}": c for (a, b), c in sorted(by.items(), key=str)}},
           "problems": problems, "verdicts": verdicts}
    json.dump(out, open(out_path, "w"), indent=2)
    print(out["status"], f"({len(problems)} problem(s))")
    return 0 if not problems else 1


if __name__ == "__main__":
    args = sys.argv[1:]
    opts = {}
    for flag in ("--assembly", "--validated"):
        if flag in args:
            i = args.index(flag)
            opts[flag[2:]] = args[i + 1]
            del args[i:i + 2]
    if len(args) not in (4, 5) or (("assembly" in opts) != ("validated" in opts)):
        print("usage: audit.py SOURCE.ndjson CONTRACT.json TRANSLATION_REPORT.json AUDIT_OUT.json [TARGET_METADATA.json] "
              "[--assembly PROOFS.json --validated VALIDATED_REPORT.json]", file=sys.stderr)
        sys.exit(2)
    sys.exit(main(*args, **opts))

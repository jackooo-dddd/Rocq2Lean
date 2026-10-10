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


def source_sort_nf(s):
    if s["k"] == "prop":
        return canon(0, {})
    if s["k"] == "type":
        c, ps = None, {}
        for e in s["u"]:
            if e["l"]["k"] == "set":
                c = max(c or 0, e["n"] + 1)
            elif e["l"]["k"] == "global":
                p = level_param(e["l"]["n"])
                ps[p] = max(ps.get(p, 0), e["n"] + 1)
            else:
                raise Mismatch(f"source universe outside the audited fragment: {e}")
        return canon(c, ps)
    raise Mismatch(f"source sort outside the audited fragment: {s}")


def source_globals(t, acc):
    if isinstance(t, dict):
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


class Auditor:
    def __init__(self, decls, results, recursors=None):
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
            return t, cs, "mono"
        raise Mismatch(f"inductive {mind} has no audited realisation")

    def head(self, t):
        """(expected const name, universe rule) for a global head."""
        k = t["k"]
        if k == "const":
            if t["c"] not in self.ok or self.ok[t["c"]]["status"] != "TRANSLATED_AND_CHECKED":
                raise Mismatch(f"reference to non-accepted constant {t['c']}")
            if t["u"]:
                raise Mismatch("universe instance on constant")
            n = len(self.ok[t["c"]].get("level_params", []))
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
        return [("bvar", x[1] + n, *x[2:]) if x[0] == "bvar" else x for x in env]

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
            if want[0] not in ("bvar", "const"):
                raise Mismatch(f"{path}: source rel {s['i']} refers to {want[0]} binder outside a supported call")
            ok = (e == {"k": "bvar", "i": want[1]}) if want[0] == "bvar" else (e == {"k": "const", "n": want[1], "u": []})
            if not ok:
                raise Mismatch(f"{path}: source rel {s['i']} should be {want}, found {e}")
            return
        if k == "sort":
            if e["k"] != "sort" or level_nf(e["l"]) != source_sort_nf(s["s"]):
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
        if isinstance(univ, tuple) and len(e["u"]) != univ[1]:
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
        head, spine = self.unspine(cur)
        tname, _, _ = self.ind_target(ref)
        if head["k"] != "const" or head["n"] != tname + ".rec":
            raise Mismatch(f"{path}: fixpoint must lower to {tname}.rec")
        nmin, nq, nidx = len(b["brs"]), nl - r - 1, len(b["p"]["ctx"]) - 1
        if len(spine) != npar + 1 + nmin + nidx + 1 + nq:
            raise Mismatch(f"{path}: {tname}.rec applied to {len(spine)} arguments")
        # Major premise and trailing arguments are the decreasing argument and Q, in order.
        self.check({"k": "rel", "i": nl - 1 - r}, spine[npar + 1 + nmin + nidx], path + ["major"], senv)
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
        menv = [("bvar", 0)]
        for i in reversed(range(r)):
            menv.append(("bvar", nidx - idx_of[i]) if i in idx_of else ("bvar", (nl - 1 - i) + nidx + 1))
        menv += self.shift(list(env), nl + nidx + 1)
        fty = d["ty"]
        for _ in range(r + 1):
            if fty["k"] != "prod":
                raise Mismatch(f"{path}: fixpoint type has fewer than {r + 1} binders")
            fty = fty["b"]
        mbody = self.strip_lams(spine[npar], nidx + 1, path + ["motive"])
        self.check(fty, mbody, path + ["motive body"], menv)
        self.check_rec_binders(head, spine, npar, nmin, nidx, path,
                               [len(self.recursive_positions(ref, k)) for k in range(nmin)],
                               [len(br["ctx"]) for br in b["brs"]], nq)
        for k, br in enumerate(b["brs"]):
            nf = len(br["ctx"])
            rpos = self.recursive_positions(ref, k)
            nih = len(rpos)
            body = self.strip_lams(spine[npar + 1 + k], nf + nih + nq, path + [f"minor{k}"])
            depth = nf + nih + nq
            benv = [("bvar", q + nih + nq, "field", k, q) for q in range(nf)]   # q: innermost-first
            for t in range(nl):                                               # a_{nl-1} .. a_0
                i = nl - 1 - t
                if i > r:
                    benv.append(("bvar", nq - 1 - (i - r - 1)))
                else:
                    benv.append(("bvar", senv[t][1] + depth, "param", i))
            info = {"minor": k, "r": r, "nf": nf, "nq": nq, "rec_q": [nf - 1 - p for p in rpos], "idx_pos": idx_pos}
            benv.append(("rec", info))
            benv += self.shift(senv[nl + 1:], depth)
            self.check(br["body"], body, path + [f"minor{k}"], benv)

    def check_rec_call(self, s, e, path, env, info):
        args, r = s["args"], info["r"]
        if len(args) < r + 1:
            raise Mismatch(f"{path}: recursive call without its decreasing argument")
        for i in range(r):
            if i in info["idx_pos"]:
                continue        # index arguments are fixed by the field's type
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
        rest = args[r + 1:]
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


def check_universe_args(facts, own, gen, exprs):
    """Rule R3 (docs/UNIVERSE_TRANSLATION.md) for every reference in `exprs`.
    own: source global levels of the referring declaration; gen: target name -> source levels."""
    n = 0
    own_params = {level_param(g): g for g in own}
    for e in exprs:
        for name, us in const_occurrences(e, []):
            if name not in gen:
                continue
            ls = gen[name]
            if len(us) != len(ls):
                raise Mismatch(f"{name}: {len(us)} universe arguments for {len(ls)} parameters")
            for l, sigma in zip(ls, us):
                c, ps = level_nf(sigma)
                if l in own:
                    if (c, ps) != canon(None, {level_param(l): 0}):
                        raise Mismatch(f"{name}: source level {l} is shared, argument must be {level_param(l)}")
                else:
                    if c is not None and not facts.entails("Set", l, c):
                        raise Mismatch(f"{name}: Set + {c} <= {l} not entailed by the source universe graph")
                    for p, k in ps:
                        if p not in own_params:
                            raise Mismatch(f"{name}: argument mentions {p}, not a parameter of the referring declaration")
                        if not facts.entails(own_params[p], l, k):
                            raise Mismatch(f"{name}: {own_params[p]} + {k} <= {l} not entailed by the source universe graph")
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
    zero = {p: _ZERO for p in ps}
    if inst_levels(res.get("generic_type"), zero) != r.get("target_type") or \
            inst_levels(res.get("generic_value"), zero) != r.get("target_value"):
        raise Mismatch("generic declaration with residual levels at 0 differs from the reported declaration")


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
    if facts is None:
        problem("universe", "source IR has no native universe facts")
    gen = {}
    for s_, r_ in rows.items():
        if r_.get("status") == "TRANSLATED_AND_CHECKED" and r_.get("level_params"):
            d_ = decls[s_]
            gen[r_["target"]] = sorted(source_globals([d_["type"], d_["body"]], set()))
    univ_checked = 0
    if facts is not None:
        for s_, r_ in rows.items():
            if r_.get("status") != "TRANSLATED_AND_CHECKED":
                continue
            d_ = decls[s_]
            own = set(source_globals([d_["type"], d_["body"]], set())) if d_["kind"] == "constant" else set()
            exprs = [r_.get("target_type"), r_.get("target_value")] + [c["type"] for c in r_.get("target_ctors", [])]
            try:
                univ_checked += check_universe_args(facts, own, gen, [x for x in exprs if x is not None])
            except Mismatch as e:
                problem("universe", f"{s_}: {e}")
    # Structural fidelity of every accepted translation.
    recursors = None
    if metadata_path and Path(metadata_path).exists():
        recursors = {r["name"]: r for r in json.load(open(metadata_path)).get("recursors", [])}
    # Defaulted universe levels (justification records) and typing-determined instance levels.
    inst = InstanceLevels(list(rows.values()), recursors)
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
                aud.check(b["type"], r["target_type"], ["arity"])
                for c, tc in zip(b["ctors"], r["target_ctors"]):
                    aud.check(c["type"], tc["type"], ["ctor " + c["name"]], [("const", t)])
                v["verdict"] = "MATCH"
            elif r["status"] == "TRANSLATED_AND_CHECKED":
                if d["kind"] != "constant":
                    raise Mismatch("UNAUDITABLE: declaration kind")
                if r["target"] != target_name(d["name"]):
                    raise Mismatch(f"target name {r['target']} is not the image of {d['name']}")
                want_kinds = {"transparent": {"def"}, "opaque_present": {"theorem", "opaque"}}.get(d["body_state"], set())
                if r["target_kind"] not in want_kinds:
                    raise Mismatch(f"{d['body_state']} source emitted as {r['target_kind']}")
                if r.get("target_type") is None or r.get("target_value") is None:
                    raise Mismatch("success claimed without target type/value")
                want_lp = sorted(level_param(n) for n in source_globals([d["type"], d["body"]], set()))
                if r.get("level_params", []) != want_lp:
                    raise Mismatch(f"universe parameters {r.get('level_params')} are not the generalized globals {want_lp}")
                aud.check(d["type"], r["target_type"], ["type"])
                aud.check(d["body"], r["target_value"], ["body"])
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

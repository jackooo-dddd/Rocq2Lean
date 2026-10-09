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
    def __init__(self, decls, results):
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
        for k, br in enumerate(brs):
            nf, nih = len(br["ctx"]), self.recursive_fields(ref, k)
            body = self.strip_lams(spine[npar + 1 + k], nf + nih, path + [f"minor{k}"])
            self.check(br["body"], body, path + [f"minor{k}"], self.shift(self.push(env, nf), nih))
        # Indices of the major premise are forced by the recursor's (kernel-checked) type.
        self.check(s["c"], spine[-1], path + ["major"], env)

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
        # Motive: shape only (forced by the declared type, which is audited).
        self.strip_lams(spine[npar], nidx + 1, path + ["motive"])
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


def main(src_path, contract_path, report_path, out_path):
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
    if [r.get("name") for r in rep_roots] != canon or any(r.get("status") != ok_status(r.get("name")) for r in rep_roots):
        problem("coverage", "report root records disagree with the contract or with the result rows")
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
    # Structural fidelity of every accepted translation.
    aud = Auditor(decls, list(rows.values()))
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
           "coverage": {"requested_roots": len(canon), "required_closure": len(closure), "accepted": len(accepted),
                        "extra_exported": sorted(set(decls) - closure)},
           "problems": problems, "verdicts": verdicts}
    json.dump(out, open(out_path, "w"), indent=2)
    print(out["status"], f"({len(problems)} problem(s))")
    return 0 if not problems else 1


if __name__ == "__main__":
    if len(sys.argv) != 5:
        print("usage: audit.py SOURCE.ndjson CONTRACT.json TRANSLATION_REPORT.json AUDIT_OUT.json", file=sys.stderr)
        sys.exit(2)
    sys.exit(main(*sys.argv[1:5]))

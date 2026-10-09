#!/usr/bin/env python3
"""Independent structural audit: source IR  vs  accepted Lean terms.

    audit.py SOURCE.ndjson TRANSLATION_REPORT.json AUDIT_OUT.json

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

Documented equivalences: binder names and binder info are not compared; the universe argument
of a template-rule constant (Eq) is not compared, because the kernel forces it to be the sort
level of the first argument; closed universe levels are compared by their numeric value.
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


def level_value(l):
    """Value of a closed Lean level JSON, or None if it mentions parameters."""
    k = l["k"]
    if k == "zero":
        return 0
    if k == "succ":
        v = level_value(l["l"])
        return None if v is None else v + 1
    if k == "max":
        a, b = level_value(l["a"]), level_value(l["b"])
        return None if a is None or b is None else max(a, b)
    if k == "imax":
        a, b = level_value(l["a"]), level_value(l["b"])
        return None if a is None or b is None else (0 if b == 0 else max(a, b))
    return None


def source_sort_value(s):
    if s["k"] == "prop":
        return 0
    if s["k"] == "type":
        vals = []
        for e in s["u"]:
            if e["l"]["k"] != "set":
                raise Mismatch(f"source universe outside the audited fragment: {e}")
            vals.append(e["n"] + 1)
        return max(vals)
    raise Mismatch(f"source sort outside the audited fragment: {s}")


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
            return target_name(t["c"]), "mono"
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
    def push(env, n=1):
        for _ in range(n):
            env = [("bvar", 0)] + [("bvar", x[1] + 1) if x[0] == "bvar" else x for x in env]
        return env

    @staticmethod
    def shift(env, n):
        """The target has `n` extra binders that the source does not (recursive results)."""
        return [("bvar", x[1] + n) if x[0] == "bvar" else x for x in env]

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
            ok = (e == {"k": "bvar", "i": want[1]}) if want[0] == "bvar" else (e == {"k": "const", "n": want[1], "u": []})
            if not ok:
                raise Mismatch(f"{path}: source rel {s['i']} should be {want}, found {e}")
            return
        if k == "sort":
            if e["k"] != "sort" or level_value(e["l"]) != source_sort_value(s["s"]):
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

    def recursive_fields(self, ref, ctor):
        """Number of recursive constructor arguments (Lean adds one recursive result for each)."""
        mib = self.decls[ref["mind"]]
        if len(mib["bodies"]) != 1:
            raise Mismatch("UNAUDITABLE: case on a mutual block")
        args = list(reversed(mib["bodies"][ref["i"]]["ctors"][ctor]["args"]))  # outermost first
        n = 0
        for p, a in enumerate(args):
            t, depth = a["ty"], 0
            while t["k"] == "prod":
                t, depth = t["b"], depth + 1
            while t["k"] == "app":
                t = t["f"]
            if t == {"k": "rel", "i": p + mib["npars"] + depth}:
                n += 1
        return n

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


def main(src_path, report_path, out_path):
    lines = [json.loads(l) for l in open(src_path)]
    decls = {d["name"]: d for d in lines if d["kind"] in ("constant", "inductive")}
    report = json.load(open(report_path))
    results = report["results"]
    verdicts, failures = [], 0
    names = [r["source"] for r in results]
    if sorted(names) != sorted(decls):
        failures += 1
        verdicts.append({"source": "*", "verdict": "MISMATCH",
                         "reason": "report results do not cover the exported declarations one-to-one"})
    aud = Auditor(decls, results)
    for r in results:
        d = decls.get(r["source"])
        v = {"source": r["source"], "status": r["status"]}
        try:
            if r["status"] == "TRANSLATED_AND_CHECKED" and d["kind"] == "inductive":
                if len(d["bodies"]) != 1:
                    raise Mismatch("UNAUDITABLE: mutual block")
                b = d["bodies"][0]
                t, cs = generated_names(d["name"], b["name"], [c["name"] for c in b["ctors"]])
                if r["target"] != t or [c["name"] for c in r["target_ctors"]] != cs:
                    raise Mismatch(f"target names {r['target']} / {r['target_ctors']} are not the images of the source")
                aud.check(b["type"], r["target_type"], ["arity"])
                for c, tc in zip(b["ctors"], r["target_ctors"]):
                    aud.check(c["type"], tc["type"], ["ctor " + c["name"]], [("const", t)])
                v["verdict"] = "MATCH"
            elif r["status"] == "TRANSLATED_AND_CHECKED":
                if d["kind"] != "constant":
                    raise Mismatch("UNAUDITABLE: declaration kind")
                if r["target"] != target_name(d["name"]):
                    raise Mismatch(f"target name {r['target']} is not the image of {d['name']}")
                want_kinds = {"transparent": {"def"}, "opaque_present": {"theorem", "opaque"}}[d["body_state"]]
                if r["target_kind"] not in want_kinds:
                    raise Mismatch(f"{d['body_state']} source emitted as {r['target_kind']}")
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
            failures += 1
        verdicts.append(v)
    for root in report["roots"]:
        if root["status"] != "TRANSLATED_AND_CHECKED":
            failures += 1
            verdicts.append({"source": root["name"], "verdict": "ROOT_NOT_ACCEPTED"})
    out = {"schema": "rocq2lean-audit/1", "status": "OK" if failures == 0 else "AUDIT_REJECTED",
           "failures": failures, "verdicts": verdicts}
    json.dump(out, open(out_path, "w"), indent=2)
    print(out["status"], f"({failures} failure(s))")
    return 0 if failures == 0 else 1


if __name__ == "__main__":
    sys.exit(main(*sys.argv[1:4]))

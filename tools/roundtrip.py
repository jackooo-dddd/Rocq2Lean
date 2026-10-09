#!/usr/bin/env python3
"""Independent decoder + structural round trip for an export.

    roundtrip.py SOURCE.ndjson OUT_DIR  -- load-path flags... -- Require.Module ...

1. Decodes every declaration of the IR (independently of the OCaml exporter) back into MetaRocq
   Gallina syntax (`constant_body` / `mutual_inductive_body`).
2. Writes OUT_DIR/RoundTrip.v which, in a fresh Rocq process with the original libraries
   loaded, re-quotes each declaration (`tmQuoteConstant kn true`, `tmQuoteInductive kn`) and
   compares it with the decoded value using `cb_eqb` / `mib_eqb` from rocq/roundtrip/RtEq.v
   (full structural equality, including binder names, relevance and universes; MetaRocq's own
   eqb_*_body do not compute because of an opaque EqDec obligation).
3. Checks opacity natively: `tmQuoteConstant kn false` must hide the body exactly when the IR
   says `opaque_present` or `assumption`.
4. Recomputes dependency edges from the IR terms and compares them with the exported edges.

Writes OUT_DIR/roundtrip.json; exits non-zero on any mismatch.
"""

import json
import os
import subprocess
import sys
from pathlib import Path


class Unsupported(Exception):
    pass


def bs(s):
    return '"' + s.replace('"', '""') + '"%bs'


def gl_list(xs):
    return "[" + "; ".join(xs) + "]"


def kername(key, mps):
    """Rebuild a MetaRocq kername from the structured mp recorded on the declaration."""
    mp, ident = mps[key]
    return f"({modpath(mp)}, {bs(ident)})"


def modpath(mp):
    if "file" in mp:
        return "(MPfile " + gl_list([bs(c) for c in reversed(mp["file"])]) + ")"
    if "dot" in mp:
        inner, ident = mp["dot"]
        return f"(MPdot {modpath(inner)} {bs(ident)})"
    raise Unsupported("functor-bound module path")


def level(l):
    k = l["k"]
    if k == "set":
        return "Level.lzero"
    if k == "global":
        return f"(Level.level {bs(l['n'])})"
    if k == "var":
        return f"(Level.lvar {l['i']})"
    raise Unsupported(k)


def sort(s):
    if s["k"] == "prop":
        return "sProp"
    if s["k"] == "sprop":
        return "sSProp"
    es = [f"({level(e['l'])}, {e['n']})" for e in s["u"]]
    return f"(sType (Universe.from_kernel_repr {es[0]} {gl_list(es[1:])}))"


def rel(r):
    return {"R": "Relevant", "I": "Irrelevant"}[r]


def aname(n):
    nm = "nAnon" if n["n"] is None else f"(nNamed {bs(n['n'])})"
    return f"{{| binder_name := {nm}; binder_relevance := {rel(n['r'])} |}}"


def inst(u):
    return gl_list([level(l) for l in u])


class Dec:
    def __init__(self, mps):
        self.mps = mps

    def kn(self, key):
        return kername(key, self.mps)

    def ind(self, i):
        return f"{{| inductive_mind := {self.kn(i['mind'])}; inductive_ind := {i['i']} |}}"

    def term(self, t):
        k = t["k"]
        T = self.term
        if k == "rel":
            return f"(tRel {t['i']})"
        if k == "var":
            return f"(tVar {bs(t['id'])})"
        if k == "evar":
            return f"(tEvar {t['ev']} {gl_list([T(a) for a in t['args']])})"
        if k == "sort":
            return f"(tSort {sort(t['s'])})"
        if k == "cast":
            ck = {"vm": "VmCast", "native": "NativeCast", "default": "Cast"}[t["kind"]]
            return f"(tCast {T(t['t'])} {ck} {T(t['ty'])})"
        if k == "prod":
            return f"(tProd {aname(t['n'])} {T(t['ty'])} {T(t['b'])})"
        if k == "lam":
            return f"(tLambda {aname(t['n'])} {T(t['ty'])} {T(t['b'])})"
        if k == "let":
            return f"(tLetIn {aname(t['n'])} {T(t['v'])} {T(t['ty'])} {T(t['b'])})"
        if k == "app":
            return f"(tApp {T(t['f'])} {gl_list([T(a) for a in t['args']])})"
        if k == "const":
            return f"(tConst {self.kn(t['c'])} {inst(t['u'])})"
        if k == "ind":
            return f"(tInd {self.ind(t['ind'])} {inst(t['u'])})"
        if k == "construct":
            return f"(tConstruct {self.ind(t['ind'])} {t['c']} {inst(t['u'])})"
        if k == "case":
            ci, p = t["ci"], t["p"]
            ci_s = f"{{| ci_ind := {self.ind(ci['ind'])}; ci_npar := {ci['npar']}; ci_relevance := {rel(ci['r'])} |}}"
            p_s = (f"{{| puinst := {inst(p['u'])}; pparams := {gl_list([T(a) for a in p['params']])}; "
                   f"pcontext := {gl_list([aname(n) for n in p['ctx']])}; preturn := {T(p['ret'])} |}}")
            brs = [f"{{| bcontext := {gl_list([aname(n) for n in b['ctx']])}; bbody := {T(b['body'])} |}}"
                   for b in t["brs"]]
            return f"(tCase {ci_s} {p_s} {T(t['c'])} {gl_list(brs)})"
        if k == "proj":
            p = t["p"]
            return (f"(tProj {{| proj_ind := {self.ind(p['ind'])}; proj_npars := {p['npars']}; "
                    f"proj_arg := {p['arg']} |}} {T(t['t'])})")
        if k in ("fix", "cofix"):
            ds = [f"{{| dname := {aname(d['n'])}; dtype := {T(d['ty'])}; dbody := {T(d['body'])}; rarg := {d['rarg']} |}}"
                  for d in t["defs"]]
            return f"({'tFix' if k == 'fix' else 'tCoFix'} {gl_list(ds)} {t['idx']})"
        raise Unsupported(f"primitive {k}")

    def ctx(self, c):
        return gl_list([f"{{| decl_name := {aname(d['n'])}; "
                        f"decl_body := {'None' if d['body'] is None else 'Some ' + self.term(d['body'])}; "
                        f"decl_type := {self.term(d['ty'])} |}}" for d in c])

    def udecl(self, u):
        if u["k"] == "monomorphic":
            return "Monomorphic_ctx"
        names = gl_list(["nAnon" if n is None else f"(nNamed {bs(n)})" for n in u["names"]])
        cs = []
        for c in u["constraints"]:
            rel = c["rel"]
            ct = f"(ConstraintType.Le ({rel['offset']})%Z)" if rel["k"] == "le" else "ConstraintType.Eq"
            cs.append(f"(({level(c['l'])}, {ct}), {level(c['r'])})")
        cset = "(List.fold_right ConstraintSet.add ConstraintSet.empty " + gl_list(cs) + ")"
        return f"(Polymorphic_ctx ({names}, {cset}))"

    def constant(self, d):
        body = "None" if d["body"] is None else f"(Some {self.term(d['body'])})"
        return (f"{{| cst_type := {self.term(d['type'])}; cst_body := {body}; "
                f"cst_universes := {self.udecl(d['universes'])}; cst_relevance := {rel(d['relevance'])} |}}")

    def inductive(self, d):
        bodies = []
        for b in d["bodies"]:
            ctors = [f"{{| cstr_name := {bs(c['name'])}; cstr_args := {self.ctx(c['args'])}; "
                     f"cstr_indices := {gl_list([self.term(i) for i in c['indices']])}; "
                     f"cstr_type := {self.term(c['type'])}; cstr_arity := {c['arity']} |}}" for c in b["ctors"]]
            projs = [f"{{| proj_name := {bs(p['name'])}; proj_relevance := {rel(p['r'])}; proj_type := {self.term(p['type'])} |}}"
                     for p in b["projs"]]
            bodies.append(
                f"{{| ind_name := {bs(b['name'])}; ind_indices := {self.ctx(b['indices'])}; ind_sort := {sort(b['sort'])}; "
                f"ind_type := {self.term(b['type'])}; ind_kelim := {b['kelim']}; ind_ctors := {gl_list(ctors)}; "
                f"ind_projs := {gl_list(projs)}; ind_relevance := {rel(b['r'])} |}}")
        var = "None" if d["variance"] is None else "(Some " + gl_list(
            ["Variance." + {"irrelevant": "Irrelevant", "covariant": "Covariant", "invariant": "Invariant"}[v]
             for v in d["variance"]]) + ")"
        return (f"{{| ind_finite := {d['finite']}; ind_npars := {d['npars']}; ind_params := {self.ctx(d['params'])}; "
                f"ind_bodies := {gl_list(bodies)}; ind_universes := {self.udecl(d['universes'])}; ind_variance := {var} |}}")


def term_deps(t, acc):
    if isinstance(t, dict):
        k = t.get("k")
        if k == "const":
            acc.add(t["c"])
        elif k in ("ind", "construct"):
            acc.add(t["ind"]["mind"])
        elif k == "case":
            acc.add(t["ci"]["ind"]["mind"])
        elif k == "proj":
            acc.add(t["p"]["ind"]["mind"])
        for v in t.values():
            term_deps(v, acc)
    elif isinstance(t, list):
        for v in t:
            term_deps(v, acc)
    return acc


def main(argv):
    src, out = Path(argv[0]), Path(argv[1])
    rest = argv[2:]
    sep = rest.index("--")
    loadpaths, requires = rest[:sep], rest[sep + 1:]
    lines = [json.loads(l) for l in open(src)]
    decls = [d for d in lines if d["kind"] in ("constant", "inductive")]
    mps = {d["name"]: (d["mp"], d["id"]) for d in decls}
    dec = Dec(mps)
    results, problems = {}, []

    # Dependency edges, recomputed independently.
    for d in decls:
        if d["kind"] == "constant":
            want_t = term_deps(d["type"], set()) - {d["name"]}
            want_b = (term_deps(d["body"], set()) if d["body"] else set()) - {d["name"]}
            if sorted(want_t) != d["deps"]["type"] or sorted(want_b) != d["deps"]["body"]:
                problems.append(f"{d['name']}: exported dependency edges differ from recomputed ones")
        missing = [x for x in d["deps"]["type"] + d["deps"].get("body", []) if x not in mps]
        if missing:
            problems.append(f"{d['name']}: dependencies absent from the export: {missing}")

    v = ["From MetaRocq.Utils Require Import utils.",
         "From MetaRocq.Template Require Import All.",
         "From Rocq2LeanRoundTrip Require Import RtEq.",
         *[f"Require {r}." for r in requires],
         "Import MonadNotation.", "Open Scope bs_scope.", ""]
    for i, d in enumerate(decls):
        try:
            if d["kind"] == "constant":
                val = dec.constant(d)
                v.append(f"Definition rt_{i} : constant_body := {val}.")
                hidden = "true" if d["body_state"] in ("opaque_present", "assumption") else "false"
                kn = dec.kn(d['name'])
                v.append(
                    f"MetaRocq Run (tmBind (tmQuoteConstant {kn} true) (fun cb : constant_body => "
                    f"tmBind (tmEval all (cb_eqb cb rt_{i})) (fun b : bool => "
                    f"tmBind (tmQuoteConstant {kn} false) (fun cb' : constant_body => "
                    f"tmBind (tmEval all (match cst_body cb' with None => true | Some _ => false end)) (fun h : bool => "
                    f"if b then (if Bool.eqb h {hidden} then tmMsg \"RT_OK {i}\" else tmMsg \"RT_OPACITY_MISMATCH {i}\") "
                    f"else tmMsg \"RT_MISMATCH {i}\"))))).")
            else:
                val = dec.inductive(d)
                v.append(f"Definition rt_{i} : mutual_inductive_body := {val}.")
                v.append(
                    f"MetaRocq Run (tmBind (tmQuoteInductive {dec.kn(d['name'])}) (fun mib : mutual_inductive_body => "
                    f"tmBind (tmEval all (mib_eqb mib rt_{i})) (fun b : bool => "
                    f"if b then tmMsg \"RT_OK {i}\" else tmMsg \"RT_MISMATCH {i}\"))).")
        except Unsupported as e:
            results[d["name"]] = f"UNSUPPORTED_BY_DECODER: {e}"
    out.mkdir(parents=True, exist_ok=True)
    vfile = out / "RoundTrip.v"
    vfile.write_text("\n".join(v) + "\n")
    rt_dir = Path(__file__).resolve().parent.parent / "rocq" / "roundtrip"
    rt_lp = ["-Q", str(rt_dir), "Rocq2LeanRoundTrip"]
    subprocess.run(["rocq", "compile", *rt_lp, str(rt_dir / "RtEq.v")], check=True, capture_output=True)
    p = subprocess.run(["rocq", "compile", *rt_lp, *loadpaths, str(vfile)], capture_output=True, text=True)
    (out / "logs").mkdir(exist_ok=True)
    (out / "logs" / "roundtrip.log").write_text(p.stdout + p.stderr)
    for line in (p.stdout + p.stderr).splitlines():
        parts = line.split()
        if len(parts) == 2 and parts[0].startswith("RT_") and parts[1].isdigit():
            results[decls[int(parts[1])]["name"]] = parts[0]
    for d in decls:
        st = results.get(d["name"], "NOT_CHECKED")
        if st != "RT_OK":
            problems.append(f"{d['name']}: {st}")
    if p.returncode != 0:
        problems.append(f"round-trip Rocq process exited with {p.returncode}")
    report = {"schema": "rocq2lean-roundtrip/1", "status": "OK" if not problems else "EXPORT_VALIDATION_FAILED",
              "checked": len(decls), "results": results, "problems": problems,
              "method": "independent Python decoder -> MetaRocq Gallina; transparent structural equality "
                        "(rocq/roundtrip/RtEq.v: cb_eqb / mib_eqb) against a fresh quotation; native opacity check; "
                        "recomputed dependency edges"}
    (out / "roundtrip.json").write_text(json.dumps(report, indent=2) + "\n")
    print(report["status"], f"{len(decls)} declarations", *problems[:10], sep="\n  ")
    return 0 if not problems else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))

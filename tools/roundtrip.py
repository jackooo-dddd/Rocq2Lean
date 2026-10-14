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

import hashlib
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


def term_levels(t, acc):
    if isinstance(t, dict):
        if t.get("k") == "global" and "n" in t:
            acc.add(t["n"])
        for v in t.values():
            term_levels(v, acc)
    elif isinstance(t, list):
        for v in t:
            term_levels(v, acc)
    return acc


def check_native_meta(decls, out, loadpaths, requires):
    """Fresh-process native recomputation of each declaration's metadata (body kind, typing flags,
    polymorphism, template/private status, private universes), compared field by field."""
    plugin = Path(__file__).resolve().parent.parent / "rocq" / "exporter"
    v = ["From Rocq2LeanExport Require Import Loader.", *[f"Require {r}." for r in requires]]
    v += [f'Rocq2Lean NativeMeta "{d["name"]}" "{d["kind"]}".' for d in decls]
    vfile = out / "RoundTripNative.v"
    vfile.write_text("\n".join(v) + "\n")
    p = subprocess.run(["rocq", "compile", "-I", str(plugin / "src"), "-Q", str(plugin / "theories"), "Rocq2LeanExport",
                        *loadpaths, str(vfile)], capture_output=True, text=True)
    (out / "logs" / "roundtrip_native.log").write_text(p.stdout + p.stderr)
    got = {}
    for line in (p.stdout + p.stderr).splitlines():
        if line.startswith("NATIVE_META "):
            _, key, js = line.split(" ", 2)
            got[key] = json.loads(js)
    problems = []
    for d in decls:
        if d["name"] not in got:
            problems.append(f"{d['name']}: native metadata not recomputed")
        elif got[d["name"]] != d["native"]:
            diff = sorted(k for k in set(got[d["name"]]) | set(d["native"]) if got[d["name"]].get(k) != d["native"].get(k))
            problems.append(f"{d['name']}: native metadata differs in {diff}")
    if p.returncode != 0:
        problems.append(f"native metadata process exited with {p.returncode}")
    return {"status": "OK" if not problems else "MISMATCH", "problems": problems}


def check_prepared(decls, out, loadpaths, requires):
    """Prepared constants (sealed-module implementation and/or lowered ssr_have_upoly, see
    rocq/exporter): a fresh Rocq process re-prepares each one natively (`Rocq2Lean CheckPrepared`),
    re-checks the prepared body with Rocq's kernel against the declared type, quotes type and body,
    and they must equal the IR's field by field."""
    if not decls:
        return {"results": {}, "problems": []}
    plugin = Path(__file__).resolve().parent.parent / "rocq" / "exporter"
    v = ["From Rocq2LeanExport Require Import Loader.", *[f"Require {r}." for r in requires]]
    v += [f'Rocq2Lean CheckPrepared "{d["name"]}".' for d in decls]
    vfile = out / "RoundTripPrepared.v"
    vfile.write_text("\n".join(v) + "\n")
    p = subprocess.run(["rocq", "compile", "-I", str(plugin / "src"), "-Q", str(plugin / "theories"), "Rocq2LeanExport",
                        *loadpaths, str(vfile)], capture_output=True, text=True)
    (out / "logs").mkdir(exist_ok=True)
    (out / "logs" / "roundtrip_prepared.log").write_text(p.stdout + p.stderr)
    got = {}
    for line in (p.stdout + p.stderr).splitlines():
        if line.startswith("PREPARED "):
            _, key, js = line.split(" ", 2)
            got[key] = json.loads(js)
    results, problems = {}, []
    for d in decls:
        g = got.get(d["name"])
        if g is None:
            results[d["name"]] = "RT_PREPARED_NOT_RECOMPUTED"
        elif g["type"] != d["type"] or g["body"] != d["body"]:
            results[d["name"]] = "RT_PREPARED_MISMATCH"
        else:
            results[d["name"]] = "RT_OK"
    if p.returncode != 0:
        problems.append(f"prepared-constant process exited with {p.returncode}")
    return {"results": results, "problems": problems}


STATEMENT_SAMPLE = 8         # constants re-derived alone, per export (request independence)
STATEMENT_STATES = ("statement_only", "obligation", "obligation_extraction_failed", "opaque_interface", "opaque_data")


def check_statement(decls, out, loadpaths, requires):
    """Statement mode: a fresh Rocq process re-runs the statement preparation of each rewritten
    constant alone (`Rocq2Lean CheckStatementPrepared`) and prints its rewritten type and body, its
    state and its obligations; they must equal the IR. Obligation constants (they exist only in the
    prepared environment) are checked through their parent definition."""
    if not decls:
        return {"results": {}, "problems": []}
    plugin = Path(__file__).resolve().parent.parent / "rocq" / "exporter"
    parents = [d for d in decls if d["body_state"] != "obligation"]
    # every constant re-derived in one fresh process, the environment prepared once for all of them
    # (as the export does: `CheckStatementsPrepared`); and, for request independence, a deterministic
    # sample re-derived each alone in its own prepared environment (`CheckStatementPrepared`)
    (out / "logs").mkdir(exist_ok=True)
    keys = out / "RoundTripStatement.keys"
    keys.write_text("".join(d["name"] + "\n" for d in parents))
    sample = sorted(parents, key=lambda d: hashlib.sha256(d["name"].encode()).hexdigest())[:STATEMENT_SAMPLE]

    def run(name, cmds):
        v = ["From Rocq2LeanExport Require Import Loader.", *[f"Require {r}." for r in requires], *cmds]
        vfile = out / f"{name}.v"
        vfile.write_text("\n".join(v) + "\n")
        p = subprocess.run(["rocq", "compile", "-I", str(plugin / "src"), "-Q", str(plugin / "theories"), "Rocq2LeanExport",
                            *loadpaths, str(vfile)], capture_output=True, text=True)
        (out / "logs" / f"{name}.log").write_text(p.stdout + p.stderr)
        got = {}
        for line in (p.stdout + p.stderr).splitlines():
            if line.startswith("STATEMENT "):
                _, key, js = line.split(" ", 2)
                got[key] = json.loads(js)
        return p, got

    p, got = run("RoundTripStatement", [f'Rocq2Lean CheckStatementsPrepared "{keys}".'])
    p1, alone = run("RoundTripStatementAlone", [f'Rocq2Lean CheckStatementPrepared "{d["name"]}".' for d in sample])
    by_name = {d["name"]: d for d in decls}
    results, problems, confirmed = {}, [], set()
    want_state = {"statement_only": "statement_only", "obligation_extraction_failed": "obligation_extraction_failed",
                  "opaque_interface": "opaque_interface", "opaque_data": "opaque_data"}
    for d in parents:
        g = got.get(d["name"])
        if g is None:
            results[d["name"]] = "RT_STATEMENT_NOT_RECOMPUTED"
            continue
        ok = g["type"] == d["type"] and g["body"] == d["body"] and g["state"] == want_state.get(d["body_state"], "kept") \
            and [o["name"] for o in g["obligations"]] == (d.get("obligations") or []) \
            and g.get("termination") == (d.get("termination") or {}).get("state") \
            and (d["body_state"] != "opaque_data" or ((d.get("native") or {}).get("body_kind") == "opaque" and d["body"] is not None))
        for o in g["obligations"]:
            od = by_name.get(o["name"])
            if od is None or od["body_state"] != "obligation" or od["type"] != o["type"] or od["body"] is not None:
                ok = False
            else:
                confirmed.add(o["name"])
        results[d["name"]] = "RT_OK" if ok else "RT_STATEMENT_MISMATCH"
    for d in decls:
        if d["body_state"] == "obligation":
            results[d["name"]] = "RT_OK" if d["name"] in confirmed else "RT_OBLIGATION_UNCONFIRMED"
    for d in sample:
        if alone.get(d["name"]) != got.get(d["name"]):
            results[d["name"]] = "RT_STATEMENT_REQUEST_DEPENDENT"
    if p.returncode != 0:
        problems.append(f"statement-preparation process exited with {p.returncode}")
    if p1.returncode != 0:
        problems.append(f"per-constant statement-preparation process exited with {p1.returncode}")
    return {"results": results, "problems": problems, "request_independence_sample": [d["name"] for d in sample]}


def check_universes(lines, out, loadpaths, requires):
    """Native re-check of the universe facts, and consistency of MetaRocq's universe record."""
    facts = lines[4]
    problems = []
    if facts.get("kind") != "universe_facts":
        return {"status": "MISSING", "problems": ["universe facts record missing"]}
    names = ["Set"] + facts["levels"]
    rel = {(x["l"], x["r"]): x["rel"] for x in facts["relations"]}
    # Every level named in the exported terms is covered by the facts.
    used = term_levels([d for d in lines if d.get("kind") in ("constant", "inductive")], set())
    for n in sorted(used - set(names)):
        problems.append(f"universe level {n} occurs in the export but has no native facts")
    # MetaRocq's constraints are entailed by the native facts.
    for c in lines[3]["constraints"]:
        a = "Set" if c["l"]["k"] == "set" else c["l"].get("n")
        b = "Set" if c["r"]["k"] == "set" else c["r"].get("n")
        r = rel.get((a, b), "none")
        k = c["rel"]
        ok = ((k["k"] == "le" and ((k["offset"] <= 0 and r in ("le", "lt")) or (k["offset"] == 1 and r == "lt")))
              or (k["k"] == "eq" and r == "le" and rel.get((b, a)) == "le"))
        if not ok:
            problems.append(f"MetaRocq constraint {a} {k} {b} is not entailed by the native facts")
    # Fresh-process native re-check of every ordered pair.
    plugin = Path(__file__).resolve().parent.parent / "rocq" / "exporter"
    v = ["From Rocq2LeanExport Require Import Loader.", *[f"Require {r}." for r in requires]]
    # every ordered pair, in one pass of `Rocq2Lean CheckRelations` (the same check as CheckRelation)
    pairs = [(a, b) for a in names for b in names if a != b]
    tsv, res = (out / "RoundTripUniverses.tsv").resolve(), (out / "RoundTripUniverses.out").resolve()
    tsv.write_text("".join(f"{a}\t{b}\t{rel.get((a, b), 'none')}\n" for a, b in pairs))
    if res.exists():
        res.unlink()
    v.append(f'Rocq2Lean CheckRelations "{tsv}" "{res}".')
    vfile = out / "RoundTripUniverses.v"
    vfile.write_text("\n".join(v) + "\n")
    p = subprocess.run(["rocq", "compile", "-I", str(plugin / "src"), "-Q", str(plugin / "theories"), "Rocq2LeanExport",
                        *loadpaths, str(vfile)], capture_output=True, text=True)
    (out / "logs" / "roundtrip_universes.log").write_text(p.stdout + p.stderr)
    lines = res.read_text().splitlines() if res.exists() else []
    oks = [l for l in lines if l.startswith("UREL_OK")]
    bad = [l for l in lines if l.startswith(("UREL_MISMATCH", "UREL_UNKNOWN"))]
    problems += bad
    if p.returncode != 0:
        problems.append(f"universe re-check process exited with {p.returncode}")
    if len(oks) != len(pairs):
        problems.append(f"universe re-check confirmed {len(oks)} of {len(pairs)} pairs")
    return {"status": "OK" if not problems else "MISMATCH", "problems": problems, "pairs": len(pairs)}


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
    # statement mode: declarations rewritten by the statement preparation (proof bodies omitted, proof
    # subterms extracted as obligations) are re-derived natively by check_statement below
    statement = [d for d in decls if d["kind"] == "constant" and
                 (d["body_state"] in STATEMENT_STATES or d.get("obligations"))]
    prepared = [d for d in decls if d["kind"] == "constant" and d not in statement
                and any(((d.get("native") or {}).get("prepared") or {}).values())]
    for i, d in enumerate(decls):
        if d in prepared or d in statement:
            continue       # sealed implementation / lowered body: checked by check_prepared below
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
    pr = check_prepared(prepared, out, loadpaths, requires)
    results.update(pr["results"])
    problems += pr["problems"]
    sr = check_statement(statement, out, loadpaths, requires)
    results.update(sr["results"])
    problems += sr["problems"]
    for d in decls:
        st = results.get(d["name"], "NOT_CHECKED")
        if st != "RT_OK":
            problems.append(f"{d['name']}: {st}")
    if p.returncode != 0:
        problems.append(f"round-trip Rocq process exited with {p.returncode}")
    meta = check_native_meta([d for d in decls if d.get("body_state") != "obligation"], out, loadpaths, requires)
    problems += meta["problems"]
    results["__native_metadata__"] = meta["status"]
    universe = check_universes(lines, out, loadpaths, requires)
    problems += universe["problems"]
    results["__universe_facts__"] = universe["status"]
    report = {"schema": "rocq2lean-roundtrip/1", "status": "OK" if not problems else "EXPORT_VALIDATION_FAILED",
              "checked": len(decls), "results": results, "problems": problems,
              "statement_request_independence_sample": sr.get("request_independence_sample", []),
              "method": "independent Python decoder -> MetaRocq Gallina; transparent structural equality "
                        "(rocq/roundtrip/RtEq.v: cb_eqb / mib_eqb) against a fresh quotation; native opacity check; "
                        "recomputed dependency edges; native universe facts re-checked pairwise in a fresh process "
                        "(Rocq2Lean CheckRelation) and MetaRocq's constraints checked to be entailed by them; statement "
                        "preparation re-derived for every rewritten constant in one prepared environment "
                        "(CheckStatementsPrepared), and alone for a deterministic sample (CheckStatementPrepared)"}
    (out / "roundtrip.json").write_text(json.dumps(report, indent=2) + "\n")
    print(report["status"], f"{len(decls)} declarations", *problems[:10], sep="\n  ")
    return 0 if not problems else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))

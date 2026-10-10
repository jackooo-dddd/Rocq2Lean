"""Source vs target computation on generated inputs, compared as constructor-index trees.

Generates M3C/Cases.v (deterministic small inputs), runs the real pipeline on it, then
  * Rocq: evaluates each case (cbv), quotes the value with MetaRocq and encodes it as
    constructor indices (tests/m3/Enc.v);
  * Lean: fully normalizes each translated case (`#rocq2lean_eval`);
and compares the two after mapping Lean constructors back to source (inductive, index) through
the translation report. Printed names are never compared. Exit status 0 iff all cases agree.
"""
import itertools
import json
import os
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tests"))
from lib import cli, SWITCH  # noqa: E402

RUN = ROOT / "runs" / "m3-compute"
M3 = ROOT / "fixtures" / "m3"


def rnat(n):
    return "RZ" if n == 0 else f"(RS {rnat(n - 1)})"


def rlist(xs):
    return "(@RNil RNat)" if not xs else f"(RCons {rnat(xs[0])} {rlist(xs[1:])})"


def trees(depth):
    if depth == 0:
        return ["(@Leaf RNat)"]
    smaller = trees(depth - 1)
    out = list(smaller)
    for l, r in itertools.product(smaller, repeat=2):
        out.append(f"(Node {l} {rnat(len(out) % 3)} {r})")
    return out


def vec(xs):
    return "(@VNil RNat)" if not xs else f"(VCons {rnat(xs[0])} {vec(xs[1:])})"


def nat(n):
    return "O" if n == 0 else f"(S {nat(n - 1)})"


def cases():
    cs = []
    for a, b in itertools.product(range(4), repeat=2):
        cs.append(f"addR {rnat(a)} {rnat(b)}")
        cs.append(f"addAcc {rnat(a)} {rnat(b)}")
    for xs in ([], [0], [2, 1], [1, 0, 3]):
        cs.append(f"lengthR {rlist(xs)}")
        cs.append(f"mapR RS {rlist(xs)}")
        cs.append(f"head_or RZ {rlist(xs)}")
    for t in trees(2)[:8]:
        cs.append(f"mirrorR {t}")
        cs.append(f"tree_root_or RZ {t}")
    for xs in ([], [1], [0, 2]):
        cs.append(f"vmap RS {vec(xs)}")
        cs.append(f"vid {vec(xs)}")
    cs.append(f"vtail {vec([1, 2])}")
    for n in range(5):
        cs.append(f"double_nat {nat(n)}")
        cs.append(f"pred_nat {nat(n)}")
        cs.append(f"pred_r {rnat(n)}")
    return cs


def parse_sexp(s):
    toks = s.replace("(", " ( ").replace(")", " ) ").split()
    pos = 0

    def go():
        nonlocal pos
        t = toks[pos]
        pos += 1
        if t != "(":
            return t
        out = []
        while toks[pos] != ")":
            out.append(go())
        pos += 1
        return out
    return go()


def norm_rocq(x):
    """Rocq encoding -> canonical tree ("c", mind, idx, args) / ("i", mind, args)."""
    if x[0] == "c":
        return ("c", x[1], int(x[2]), ())
    if x[0] == "i":
        return ("i", x[1], ())
    if x[0] == "a":
        h = norm_rocq(x[1])
        return h[:-1] + (tuple(norm_rocq(a) for a in x[2:]),)
    raise ValueError(f"unexpected Rocq encoding {x}")


def lean_maps(report):
    ctor, ind = {"Nat.zero": ("Corelib.Init.Datatypes.nat", 0), "Nat.succ": ("Corelib.Init.Datatypes.nat", 1),
                 "Eq.refl": ("Corelib.Init.Logic.eq", 0)}, {"Nat": "Corelib.Init.Datatypes.nat",
                                                            "Eq": "Corelib.Init.Logic.eq"}
    for r in report["results"]:
        if r["status"] == "TRANSLATED_AND_CHECKED" and r["kind"] == "inductive":
            ind[r["target"]] = r["source"]
            for k, c in enumerate(r["target_ctors"]):
                ctor[c["name"]] = (r["source"], k)
    return ctor, ind


def norm_lean(v, ctor, ind):
    if "nat" in v:   # Lean Nat literal = bootstrap nat constructor chain
        t = ("c", "Corelib.Init.Datatypes.nat", 0, ())
        for _ in range(v["nat"]):
            t = ("c", "Corelib.Init.Datatypes.nat", 1, (t,))
        return t
    if "c" in v:
        m, k = ctor[v["c"]]
        return ("c", m, k, tuple(norm_lean(a, ctor, ind) for a in v["args"]))
    if "i" in v:
        return ("i", ind[v["i"]], tuple(norm_lean(a, ctor, ind) for a in v["args"]))
    raise ValueError(f"target value is not a constructor tree: {v}")


def main():
    shutil.rmtree(RUN, ignore_errors=True)
    RUN.mkdir(parents=True)
    cs = cases()
    lines = ["From M3 Require Import M3Types M3Case M3Fix."]
    lines += [f"Definition case{i} := {c}." for i, c in enumerate(cs)]
    (RUN / "Cases.v").write_text("\n".join(lines) + "\n")
    man = {"name": "m3-compute", "load_paths": [["-Q", str(M3), "M3"], ["-Q", ".", "M3C"]],
           "files": [str(M3 / f) for f in ("M3Types.v", "M3Case.v", "M3Fix.v")] + ["Cases.v"],
           "requires": ["M3C.Cases"]}
    (RUN / "manifest.json").write_text(json.dumps(man))
    roots = [f"M3C.Cases.case{i}" for i in range(len(cs))]
    for args in (("export", "--manifest", RUN / "manifest.json", "--roots", ",".join(roots), "--out", RUN),
                 ("translate", "--input", RUN / "source.ndjson", "--out", RUN),
                 ("verify", "--run", RUN)):
        rc, out = cli(*args)
        if rc != 0:
            print(f"{args[0]} failed:\n{out[-2000:]}")
            return 1
    report = json.loads((RUN / "translation_report.json").read_text())
    # Rocq side.
    env = dict(os.environ, PATH=f"{Path.home()}/.local/bin:" + os.environ["PATH"])
    enc_dir = ROOT / "tests" / "m3"
    subprocess.run(["opam", "exec", "--switch=" + SWITCH, "--", "rocq", "compile", "-Q", str(enc_dir), "R2LEnc",
                    str(enc_dir / "Enc.v")], check=True, env=env, capture_output=True)
    ev = ["From MetaRocq.Utils Require Import utils.", "From MetaRocq.Template Require Import All.",
          "From R2LEnc Require Import Enc.", "Require M3C.Cases.", "Open Scope bs_scope.", ""]
    for i in range(len(cs)):
        ev.append(f"MetaRocq Run (tmBind (tmEval all M3C.Cases.case{i}) (fun v => tmBind (tmQuote v) "
                  f"(fun q => tmBind (tmEval all (enc q)) (fun s => tmMsg (\"EVAL {i} \" ^ s))))).")
    (RUN / "RocqEval.v").write_text("\n".join(ev) + "\n")
    p = subprocess.run(["opam", "exec", "--switch=" + SWITCH, "--", "rocq", "compile", "-Q", str(enc_dir), "R2LEnc",
                        "-Q", str(M3), "M3", "-Q", str(RUN), "M3C", str(RUN / "RocqEval.v")],
                       env=env, capture_output=True, text=True)
    rocq = {}
    for line in (p.stdout + p.stderr).splitlines():
        if line.startswith("EVAL "):
            _, i, rest = line.split(" ", 2)
            rocq[int(i)] = norm_rocq(parse_sexp(rest))
    # Lean side.
    names = [next(r["target"] for r in report["results"] if r["source"] == f"M3C.Cases.case{i}")
             for i in range(len(cs))]
    (RUN / "lean" / "names.json").write_text(json.dumps(names))
    mod = RUN / "lean" / "Rocq2LeanEval.lean"
    mod.write_text(f'import Rocq2LeanOut\nimport Rocq2Lean.Eval\n#rocq2lean_eval "{RUN / "lean" / "names.json"}" '
                   f'"{RUN / "lean" / "values.json"}"\n')
    lenv = dict(os.environ, PATH=f"{Path.home()}/.elan/bin:" + os.environ["PATH"])
    lp = subprocess.run(["lake", "-d", str(ROOT), "env", "printenv", "LEAN_PATH"], capture_output=True, text=True,
                        env=lenv).stdout.strip()
    subprocess.run(["lean", str(mod)], cwd=RUN / "lean", env=dict(lenv, LEAN_PATH=f"{lp}:{RUN / 'lean'}"), check=True)
    ctor, ind = lean_maps(report)
    vals = json.loads((RUN / "lean" / "values.json").read_text())
    results, bad = [], 0
    for i, c in enumerate(cs):
        try:
            lv = norm_lean(vals[i]["value"], ctor, ind)
        except (KeyError, ValueError) as e:
            lv = f"UNMAPPED: {e}"
        ok = i in rocq and rocq[i] == lv
        bad += not ok
        results.append({"case": c, "agree": ok})
        if not ok:
            print("DISAGREE", c, rocq.get(i), lv)
    (RUN / "computation.json").write_text(json.dumps({"cases": len(cs), "disagreements": bad, "results": results},
                                                     indent=2))
    print(f"computation: {len(cs) - bad}/{len(cs)} cases agree")
    return 0 if bad == 0 else 1


if __name__ == "__main__":
    sys.exit(main())

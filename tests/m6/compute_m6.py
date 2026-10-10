"""M6 computation validation of the accessibility lowering (fixtures/accfix `search`, structural
recursion on an accb proof) and of the ι-generalized fix lowering (fixtures/iotafix: eqb,
compare_cont, nth, dep, size_if, whose decreasing match is not outermost) and of mutual fixpoints
(fixtures/mutfix: add/add_carry, sub_mask/sub_mask_carry, evens_s/odds_s, alt_eq/alt_neq), evaluated on
concrete inputs independently in Rocq (cbv, quoted with MetaRocq) and in Lean (normalization of the
translated constants), compared as constructor trees (harness of tests/m3/compute.py).
Exit 0 iff all cases agree.
"""
import json
import os
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tests"))
sys.path.insert(0, str(ROOT / "tests" / "m3"))
from lib import cli, SWITCH  # noqa: E402
import compute as C  # noqa: E402

RUN = ROOT / "runs" / "m6-compute"
AF = ROOT / "fixtures" / "accfix"
IF = ROOT / "fixtures" / "iotafix"
I = "IF.IotaFix."
MFX = ROOT / "fixtures" / "mutfix"
M = "MF.MutFix."
CASES = [
    "AF.AccFix.search AF.AccFix.P2 0 AF.AccFix.h0",
    "AF.AccFix.search AF.AccFix.P2 1 (AF.AccFix.AccBS AF.AccFix.P2 1 (AF.AccFix.AccB0 AF.AccFix.P2 2 eq_refl))",
    "AF.AccFix.search AF.AccFix.P2 2 (AF.AccFix.AccB0 AF.AccFix.P2 2 eq_refl)",
    "AF.AccFix.search (fun n => Nat.leb 3 n) 0 (AF.AccFix.AccBS _ 0 (AF.AccFix.AccBS _ 1 (AF.AccFix.AccBS _ 2 "
    "(AF.AccFix.AccB0 (fun n => Nat.leb 3 n) 3 eq_refl))))",
    f"{I}eqb (Nat.iter 9 {I}xO {I}xH) (Nat.iter 9 {I}xO {I}xH)",
    f"{I}eqb ({I}xI (Nat.iter 5 {I}xO {I}xH)) ({I}xI (Nat.iter 5 {I}xI {I}xH))",
    f"{I}compare_cont {I}Eq (Nat.iter 4 {I}xO ({I}xI {I}xH)) (Nat.iter 4 {I}xI ({I}xO {I}xH))",
    f"{I}compare_cont {I}Eq (Nat.iter 6 {I}xI {I}xH) (Nat.iter 3 {I}xO {I}xH)",
    f"{I}compare_cont {I}Gt {I}xH {I}xH",
    f"{I}nth 3 (List.seq 10 7) 0",
    f"{I}nth 9 (List.seq 10 7) 42",
    f"{I}nth 0 (@nil bool) true",
    f"{I}dep true (Nat.iter 3 {I}xO {I}xH)",
    f"{I}dep false {I}xH",
    f"{I}size_if true (Nat.iter 7 {I}xI {I}xH)",
    f"{I}size_if false ({I}xO {I}xH)",
    f"{M}p2n ({M}add (Nat.iter 6 {M}xI {M}xH) (Nat.iter 5 {M}xO ({M}xI {M}xH)))",
    f"{M}p2n ({M}add_carry ({M}xO ({M}xI {M}xH)) (Nat.iter 4 {M}xI {M}xH))",
    f"{M}add ({M}xI ({M}xO {M}xH)) ({M}xI {M}xH)",
    f"{M}m2n ({M}sub_mask (Nat.iter 6 {M}xI {M}xH) ({M}xO ({M}xI ({M}xO {M}xH))))",
    f"{M}sub_mask ({M}xO {M}xH) (Nat.iter 3 {M}xI {M}xH)",
    f"{M}m2n ({M}sub_mask_carry (Nat.iter 5 {M}xO {M}xH) ({M}xI {M}xH))",
    f"{M}evens_s (List.seq 3 6) (0 :: nil)",
    f"{M}odds_s (List.seq 3 6) nil",
    f"{M}alt_eq (Nat.iter 3 {M}xI {M}xH) (Nat.iter 3 {M}xI {M}xH)",
    f"{M}alt_neq ({M}xO {M}xH) ({M}xO {M}xH)",
    f"{I}sumto 2 5",
    f"{I}walk 3 {I}t3",
    f"{I}psize ({I}padd ({I}px ({I}pinj 2 ({I}pc 7)) ({I}pc 1)) ({I}pinj 4 ({I}px ({I}pc 3) ({I}pinj 1 ({I}pc 9)))))",
    f"{I}padd ({I}pinj 1 ({I}pc 2)) ({I}pinj 3 ({I}px ({I}pc 4) ({I}pc 5)))",
    f"{I}count 3 false ({I}nd ({I}nd {I}lf ({I}nd {I}lf {I}lf)) {I}lf)",
    f"{I}norm ({I}eadd ({I}econst 20) ({I}eadd ({I}eopp ({I}econst 6)) ({I}eadd ({I}econst 2) ({I}eopp ({I}econst 1)))))",
    f"{I}norm ({I}eadd ({I}eadd ({I}econst 3) ({I}eopp ({I}econst 1))) ({I}eopp ({I}econst 1)))",
    "Pos.add 1234%positive 987%positive",
    "Pos.add_carry 255%positive 1%positive",
    "Pos.sub_mask 1000%positive 999%positive",
    "Pos.sub_mask 5%positive 77%positive",
    "Pos.compare 4096%positive 4095%positive",
    "Pos.eqb 77%positive 77%positive",
    "Z.pos_sub 100%positive 250%positive",
    "Pos.peano_rect (fun _ => nat) 0 (fun _ n => S n) 37%positive",
    "List.nth 4 (List.seq 0 9) 42",
]
# MathComp's ex_minn is not compared: Rocq's own evaluation (cbv) is stuck on it, because the
# accessibility proof that find_ex_minn recurses on is built with opaque (Qed) lemmas such as
# addn0 (checked: the Rocq-side value does not reduce to a constructor). There is no source value
# to compare a target value with.


def canon(v):
    """Module-qualified names: the report writes M.N/Mod.x, Rocq's quotation M.N.Mod.x."""
    if isinstance(v, tuple):
        return tuple(canon(x) for x in v)
    if isinstance(v, list):
        return [canon(x) for x in v]
    return v.replace("/", ".") if isinstance(v, str) else v


def main():
    shutil.rmtree(RUN, ignore_errors=True)
    RUN.mkdir(parents=True)
    # the fixtures the cases load are compiled here (not left to an earlier run: no order dependence)
    env0 = dict(os.environ, PATH=f"{Path.home()}/.local/bin:" + os.environ["PATH"])
    for d, prefix, f in ((AF, "AF", "AccFix.v"), (IF, "IF", "IotaFix.v"), (MFX, "MF", "MutFix.v")):
        subprocess.run(["opam", "exec", "--switch=" + SWITCH, "--", "rocq", "compile", "-Q", ".", prefix, f], cwd=d,
                       check=True, env=env0, capture_output=True)
    lines = ["Require AF.AccFix.", "Require IF.IotaFix.", "Require MF.MutFix.", "Require Stdlib.Lists.List.", "From Stdlib Require Import PArith.BinPos ZArith.BinInt.",
             "Import Stdlib.Lists.List.ListNotations.", "Open Scope list_scope."]
    lines += [f"Definition case{i} := {c}." for i, c in enumerate(CASES)]
    (RUN / "Cases.v").write_text("\n".join(lines) + "\n")
    man = {"name": "m6-compute", "load_paths": [["-Q", str(AF), "AF"], ["-Q", str(IF), "IF"], ["-Q", str(MFX), "MF"], ["-Q", ".", "M6C"]], "files": ["Cases.v"],
           "requires": ["M6C.Cases"]}
    (RUN / "manifest.json").write_text(json.dumps(man))
    roots = [f"M6C.Cases.case{i}" for i in range(len(CASES))]
    for args in (("export", "--manifest", RUN / "manifest.json", "--roots", ",".join(roots), "--out", RUN),
                 ("translate", "--input", RUN / "source.ndjson", "--out", RUN), ("verify", "--run", RUN)):
        rc, out = cli(*args)
        if rc != 0:
            print(f"{args[0]} failed:\n{out[-2000:]}")
            return 1
    report = json.loads((RUN / "translation_report.json").read_text())
    env = dict(os.environ, PATH=f"{Path.home()}/.local/bin:" + os.environ["PATH"])
    enc_dir = ROOT / "tests" / "m3"
    subprocess.run(["opam", "exec", "--switch=" + SWITCH, "--", "rocq", "compile", "-Q", str(enc_dir), "R2LEnc",
                    str(enc_dir / "Enc.v")], check=True, env=env, capture_output=True)
    ev = ["From MetaRocq.Utils Require Import utils.", "From MetaRocq.Template Require Import All.",
          "From R2LEnc Require Import Enc.", "Require M6C.Cases.", "Open Scope bs_scope.", ""]
    for i in range(len(CASES)):
        ev.append(f"MetaRocq Run (tmBind (tmEval all M6C.Cases.case{i}) (fun v => tmBind (tmQuote v) "
                  f"(fun q => tmBind (tmEval all (enc q)) (fun s => tmMsg (\"EVAL {i} \" ^ s))))).")
    (RUN / "RocqEval.v").write_text("\n".join(ev) + "\n")
    p = subprocess.run(["opam", "exec", "--switch=" + SWITCH, "--", "rocq", "compile", "-Q", str(enc_dir), "R2LEnc",
                        "-Q", str(AF), "AF", "-Q", str(IF), "IF", "-Q", str(MFX), "MF", "-Q", str(RUN), "M6C", str(RUN / "RocqEval.v")], env=env, capture_output=True, text=True)
    rocq = {}
    for line in (p.stdout + p.stderr).splitlines():
        if line.startswith("EVAL "):
            _, i, rest = line.split(" ", 2)
            rocq[int(i)] = C.norm_rocq(C.parse_sexp(rest))
    names = [next(r["target"] for r in report["results"] if r["source"] == f"M6C.Cases.case{i}") for i in range(len(CASES))]
    (RUN / "lean" / "names.json").write_text(json.dumps(names))
    mod = RUN / "lean" / "Rocq2LeanEval.lean"
    mod.write_text(f'import Rocq2LeanOut\nimport Rocq2Lean.Eval\n#rocq2lean_eval "{RUN / "lean" / "names.json"}" '
                   f'"{RUN / "lean" / "values.json"}"\n')
    lenv = dict(os.environ, PATH=f"{Path.home()}/.elan/bin:" + os.environ["PATH"])
    lp = subprocess.run(["lake", "-d", str(ROOT), "env", "printenv", "LEAN_PATH"], capture_output=True, text=True,
                        env=lenv).stdout.strip()
    subprocess.run(["lean", str(mod)], cwd=RUN / "lean", env=dict(lenv, LEAN_PATH=f"{lp}:{RUN / 'lean'}"), check=True)
    ctor, ind = C.lean_maps(report)
    vals = json.loads((RUN / "lean" / "values.json").read_text())
    results, bad = [], 0
    for i, c in enumerate(CASES):
        try:
            lv = C.norm_lean(vals[i]["value"], ctor, ind)
        except (KeyError, ValueError) as e:
            lv = f"UNMAPPED: {e}"
        ok = i in rocq and canon(rocq[i]) == canon(lv)
        bad += not ok
        results.append({"case": c, "agree": ok, "rocq": str(rocq.get(i))[:80], "lean": str(lv)[:80]})
        if not ok:
            print("DISAGREE", c, rocq.get(i), str(lv)[:300])
    (RUN / "computation.json").write_text(json.dumps({"cases": len(CASES), "disagreements": bad, "results": results}, indent=2))
    print(f"computation: {len(CASES) - bad}/{len(CASES)} cases agree")
    return 0 if bad == 0 else 1


if __name__ == "__main__":
    sys.exit(main())

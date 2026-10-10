"""M4 computation validation: genuine Stdlib/Corelib functions and the generated recursors of the
real datatypes (list, option, prod, bool), evaluated on concrete inputs in Rocq and in Lean, and
compared as constructor trees mapped back to source (inductive, index) through the translation
report (harness shared with tests/m3/compute.py). Exit 0 iff all cases agree.
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

RUN = ROOT / "runs" / "m4-compute"

CASES = [
    "[1;2] ++ [3]", "length [4;5;6]", "List.map S [0;2]", "rev [1;2;3]", "fold_left Nat.add [1;2;3] 0",
    "fold_right Nat.add 0 [1;2;3]", "combine [1;2] [true;false]", "split [(1,true);(2,false)]",
    "hd_error (@nil nat)", "hd_error [5;6]", "existsb (Nat.eqb 2) [1;2]", "forallb (Nat.eqb 2) [1;2]",
    "filter (fun x => Nat.ltb x 2) [0;3;1;2]", "firstn 2 [1;2;3]", "skipn 1 [1;2;3]", "concat [[1];[2;3];[]]",
    "repeat 7 3", "last [1;2;3] 0", "removelast [1;2;3]", "seq 2 3", "nth_error [4;5;6] 1", "nth_error [4] 3",
    "rev_append [1;2] [3]", "flat_map (fun x => [x;x]) [1;2]", "partition (Nat.eqb 1) [1;2;1]",
    "list_prod [1;2] [true]", "option_map S (Some 3)", "option_map S (@None nat)", "negb true", "andb true false",
    "orb false true", "xorb true true", "fst (3, false)", "snd (3, false)",
    # generated recursors (iota reduction of the kernel eliminators through the Rocq *_rect constants)
    "list_rect (fun _ => nat) 0 (fun _ _ r => S r) [7;8;9]", "option_rect (fun _ => nat) S 0 (Some 4)",
    "option_rect (fun _ => nat) S 0 None", "prod_rect (fun _ => nat) (fun a b => a + b) (2,3)",
    "bool_rect (fun _ => nat) 1 0 false",
]


def main():
    shutil.rmtree(RUN, ignore_errors=True)
    RUN.mkdir(parents=True)
    lines = ["From Stdlib Require Import List.", "Import ListNotations."]
    lines += [f"Definition case{i} := {c}." for i, c in enumerate(CASES)]
    (RUN / "Cases.v").write_text("\n".join(lines) + "\n")
    man = {"name": "m4-compute", "load_paths": [["-Q", ".", "M4C"]], "files": ["Cases.v"], "requires": ["M4C.Cases"]}
    (RUN / "manifest.json").write_text(json.dumps(man))
    roots = [f"M4C.Cases.case{i}" for i in range(len(CASES))]
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
          "From R2LEnc Require Import Enc.", "Require M4C.Cases.", "Open Scope bs_scope.", ""]
    for i in range(len(CASES)):
        ev.append(f"MetaRocq Run (tmBind (tmEval all M4C.Cases.case{i}) (fun v => tmBind (tmQuote v) "
                  f"(fun q => tmBind (tmEval all (enc q)) (fun s => tmMsg (\"EVAL {i} \" ^ s))))).")
    (RUN / "RocqEval.v").write_text("\n".join(ev) + "\n")
    p = subprocess.run(["opam", "exec", "--switch=" + SWITCH, "--", "rocq", "compile", "-Q", str(enc_dir), "R2LEnc",
                        "-Q", str(RUN), "M4C", str(RUN / "RocqEval.v")], env=env, capture_output=True, text=True)
    rocq = {}
    for line in (p.stdout + p.stderr).splitlines():
        if line.startswith("EVAL "):
            _, i, rest = line.split(" ", 2)
            rocq[int(i)] = C.norm_rocq(C.parse_sexp(rest))
    names = [next(r["target"] for r in report["results"] if r["source"] == f"M4C.Cases.case{i}") for i in range(len(CASES))]
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
        ok = i in rocq and rocq[i] == lv
        bad += not ok
        results.append({"case": c, "agree": ok})
        if not ok:
            print("DISAGREE", c, rocq.get(i), lv)
    (RUN / "computation.json").write_text(json.dumps({"cases": len(CASES), "disagreements": bad, "results": results},
                                                     indent=2))
    print(f"computation: {len(CASES) - bad}/{len(CASES)} cases agree")
    return 0 if bad == 0 else 1


if __name__ == "__main__":
    sys.exit(main())

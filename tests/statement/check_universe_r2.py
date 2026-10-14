#!/usr/bin/env python3
"""Rule round 2 (ITERATION_LOG entry 7): binder-level independence of statements (P1) and jointly
occurring level metavariables (P2), through the real CLI on fixtures/stmt/r2 (synthetic R2.v + the
MathComp obligation HB_unnamed_mixin_106__rocq2lean_obligation_1).

1. pairR_intro (CoqEAL list_R's shape: one level for two carriers) was refused with the source-derived
   binder-independence reason (its carriers would be identified); since R-SPLIT (entry 9) pairR is
   split and pairR_intro accepted with independent carriers; `two` keeps two independent levels;
   the P2 obligation is generic (its max-coupled class named after choice.959), nothing defaulted; no
   pending artifact claims an R2B-P level.
2. Negative controls, kernel-accepted, audit-rejected, every self-report hidden: two independent
   binder levels identified; a binder level fixed at 0; the P2 obligation narrowed at choice.959.
3. Positive control: `two` instantiated at two different nonzero universes and the P2 obligation's
   statement at nonzero universes, through the kernel.

Writes reports/statement_only/test_universe_r2.json.
"""
import copy
import json
import os
import shutil
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from lib import ROOT, audit_report, check, cli, finish, forge_run, results  # noqa: E402

OUT = {}
RUN = ROOT / "runs" / "st-r2"
OBL = "mathcomp.boot.choice.HB_unnamed_mixin_106__rocq2lean_obligation_1"
ROOTS = ["SF.R2.pairR_intro", "SF.R2.two", "mathcomp.boot.choice.HB_unnamed_mixin_106"]

shutil.rmtree(RUN, ignore_errors=True)
rcs = [cli("export", "--mode", "statement", "--manifest", ROOT / "fixtures/stmt/r2/manifest.json",
           "--roots", ",".join(ROOTS), "--out", RUN)[0]]
rcs.append(cli("translate", "--input", RUN / "source.ndjson", "--out", RUN)[0])
rcs.append(cli("validate", "--run", RUN)[0])
v = json.loads((RUN / "validate.json").read_text())
R, rep = results(RUN)
OUT["pipeline"] = {"exit_codes": rcs, "validation": v.get("status"), "reason": v.get("reason")}
check(rcs[0] == 0 and rcs[2] == 0 and v.get("status") == "STATEMENT_VALIDATED", "fixture: export/translate/validate")
pi = R["SF.R2.pairR_intro"]
OUT["pairR_intro"] = {"status": pi["status"], "message": pi.get("message", "")[:400]}
# (R-SPLIT, ITERATION_LOG entry 9: pairR's level `ul` is eligible — the sort of its three parameters and
# of its result only — so pairR is translated through the split view and pairR_intro keeps its independent
# carrier levels; the refusal of an ineligible coupled level is tested on qR_intro, check_level_split.py)
pr = R["SF.R2.pairR"]
OUT["pairR"] = {"status": pr["status"], "level_split": pr.get("level_split"), "level_params": pr.get("level_params")}
check(pi["status"] == "STATEMENT_KERNEL_CHECKED" and len(pi.get("level_params") or []) >= 3
      and pr["status"] == "TRANSLATED_AND_CHECKED" and (pr.get("level_split") or [{}])[0].get("params") == [0, 1, 2],
      "pairR_intro (list_R's shape) accepted through pairR's split view, carriers at independent levels (R-SPLIT)")
two = R["SF.R2.two"]
check(two["status"] == "STATEMENT_KERNEL_CHECKED" and len(two["level_params"]) == 2, "two: two independent binder levels")
o = R[OBL]
OUT["obligation"] = {k: o.get(k) for k in ("status", "level_params", "implicit_levels", "universe_level_defaults")}
check(o["status"] == "STATEMENT_KERNEL_CHECKED" and "u_mathcomp_boot_choice_959" in o["level_params"]
      and not o.get("universe_level_defaults"), "P2: the max-coupled class is named after choice.959; nothing defaulted")
pend_r2bp = [r["source"] for r in rep["results"] if r["status"].endswith("PENDING_KERNEL_CHECKED") and r.get("r2bp_levels")]
check(not pend_r2bp, "no pending artifact claims an R2B-P level (refused by the translator)")


def subst_levels(j, m):
    if isinstance(j, list):
        return [subst_levels(x, m) for x in j]
    if not isinstance(j, dict):
        return j
    if j.get("k") == "param" and j.get("n") in m:
        return m[j["n"]]
    return {k: subst_levels(v, m) for k, v in j.items()}


def narrow(src, m, label):
    rep2 = copy.deepcopy(rep)
    r = next(x for x in rep2["results"] if x["source"] == src)
    for k in ("target_type", "target_value"):
        r[k] = subst_levels(r[k], m)
    r["level_params"] = [p for p in r["level_params"] if p not in m]
    # (a consistent report: a narrowed implicit level disappears; a narrowed own level of the statement
    # is reported solved to its new value — so only the source-derived checks can tell)
    imp = r.get("implicit_levels") or []
    for p_, sg in m.items():
        l_ = p_[2:].replace("_", ".")
        own_l = next((l for l in json.loads((RUN / "source.ndjson").read_text().splitlines()[4])["levels"]
                      if "u_" + l.replace(".", "_") == p_), None)
        if own_l and own_l not in imp:
            r.setdefault("solved_levels", []).append({"level": own_l, "sigma": sg})
    r["implicit_levels"] = [l for l in imp if "u_" + l.replace(".", "_") not in m]
    r["universe_level_defaults"], r["universe_residuals"] = 0, None
    d_, kernel_all, rc, cons, aud = forge_run(RUN, label, rep2, check_cmd="validate")
    # (R-CARRIER, entry 11: the forged row's dependents may now be claimed and reference its original
    # universe parameters; the control requires the forged row itself to be kernel-accepted)
    rp_ = d_ / "lean" / "replay.json"
    kernel_ok = rp_.exists() and any(x["source"] == src and x["kernel"] == "ACCEPTED" for x in json.loads(rp_.read_text())["results"])
    # (validate stops at the consumer when dependents of the forged row fail to replay: the standalone
    # auditor is then run on the forged report)
    aprobs = aud.get("problems") if aud else audit_report(d_, rep2, "forged")[1]
    probs = [p["message"][:300] for p in aprobs if p["message"].startswith(src + ":")]
    OUT.setdefault("negative", {})[label] = {"kernel": kernel_ok, "validate_exit": rc, "audit_problems": probs[:3]}
    return kernel_ok, rc, probs


a_, b_ = two["level_params"]
k, rc, probs = narrow("SF.R2.two", {b_: {"k": "param", "n": a_}}, "two-identified")
check(k and rc == 2 and any("binder levels" in p for p in probs),
      "two binder levels identified (no self-report): kernel-accepted, audit-rejected (binder independence)")
k, rc, probs = narrow("SF.R2.two", {a_: {"k": "zero"}}, "two-closed")
check(k and rc == 2 and any("closed level" in p or "native fact" in p for p in probs),
      "a binder level fixed at 0 (no self-report): kernel-accepted, audit-rejected")
k, rc, probs = narrow(OBL, {"u_mathcomp_boot_choice_959": {"k": "zero"}}, "obligation-narrowed")
check(k and rc == 2 and any("free in the statement" in p or "not entailed" in p for p in probs),
      "the P2 obligation narrowed at choice.959 (no self-report): kernel-accepted, audit-rejected")

POS = f"""import Rocq2LeanOut
open Lean Meta Elab Command
def posInst (n : Name) (us : List Nat) (tag : String) : MetaM Unit := do
  let ci ← getConstInfo n
  let us := us.map Level.ofNat
  addDecl (.defnDecl {{ name := Name.mkSimple ("posctrl_" ++ tag), levelParams := [], type := ← instantiateTypeLevelParams ci.toConstantVal us,
                       value := mkConst n us, hints := .opaque, safety := .safe }})
run_meta posInst `{two["target"]} [3, 7] "two"
run_meta posInst `{o["target"]} {[2 + k for k in range(len(o["level_params"]))]} "obligation"
"""
lean = RUN / "lean"
(lean / "PositiveControl.lean").write_text(POS)
env = dict(os.environ, PATH=f"{Path.home()}/.elan/bin:" + os.environ["PATH"])
lp = subprocess.run(["lake", "-d", str(ROOT), "env", "printenv", "LEAN_PATH"], capture_output=True, text=True, env=env).stdout.strip()
env["LEAN_PATH"] = f"{lp}:{lean}"
p = subprocess.run(["lean", "PositiveControl.lean"], cwd=lean, capture_output=True, text=True, env=env)
OUT["positive"] = {"exit": p.returncode, "output": (p.stdout + p.stderr)[:500]}
check(p.returncode == 0, "positive control: `two` at universes 3 and 7, the P2 obligation at nonzero universes")

(ROOT / "reports" / "statement_only" / "test_universe_r2.json").write_text(json.dumps(OUT, indent=1) + "\n")
finish("test-universe-r2")

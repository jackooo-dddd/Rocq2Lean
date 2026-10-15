#!/usr/bin/env python3
"""Task C (docs/UNIVERSE_FAMILY_C.md): the Equality.type / JobType universe family, through the real CLI
on a small Prosa probe (fixtures/stmt/c: opt_eqP, ideal processor_state, JLFP_policy).

1. C-1 (R3G for statements): MathComp's opt_eqP (A′: an opaque constant, its body's proof subterms
   statements) keeps its reference levels as parameters (eqtype.51, eqtype.58), so option's canonical
   eqType is generic; no statement row has a
   defaulted level. The ideal processor_state is never claimed narrowed: before R-CARRIER its
   translation narrowed Job to level 0; from R-CARRIER (entry 11) to rules R and H (entry 12) it was
   refused; since stage 3 (entry 13) it is claimed with Job's carrier generic.
2. Negative controls, the target itself narrowed with every self-reported trace removed (no
   `universe_level_defaults`, no residual record, no implicit level): opt_eqP's first obligation
   statement at closed levels {0,0}, {0,1}, {2,2}
   and the protected ProcessorState at its Job binder are kernel-accepted and rejected by the audit's
   source-derived generality obligation (`check_statement_generality`).
3. Positive control at nonzero universes: the generic translations are kernel-checked at universes
   2..5 and the statement is used at an `Equality.type.{3,4}`; the same file fails against the narrowed
   module.
4. R2B-V (approved 2026-10-14): JLFP/FP/JLDP_policy are declared at the sort of their value, the job
   generic; downstream uses (hep_job, JLFP_to_JLDP, EDF, FIFO, two statements) translate and are
   audited; report-level forgeries of the rule (not a lowering, a binder level, on a statement, the
   protected lowering without the rule) are audit-rejected; the positive control instantiates the
   policies and EDF at nonzero universes.

Writes reports/statement_only/test_universe_c.json.
"""
import copy
import json
import shutil
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from lib import ROOT, check, cli, finish, forge_run, results  # noqa: E402

OUT = {}
RUN = ROOT / "runs" / "st-c-probe"
PRI = "prosa.model.priority."
DOWN = [PRI + "definitions.hep_job", PRI + "coercion.JLFP_to_JLDP", PRI + "edf.EDF", PRI + "fifo.FIFO",
        PRI + "coercion.reflexive_priorities_JLFP_implies_JLDP", "prosa.analysis.facts.priority.classes.hp_trans"]
ROOTS = ["mathcomp.boot.eqtype.opt_eqP", "prosa.model.processor.ideal.processor_state",
         PRI + "definitions.JLFP_policy", PRI + "definitions.FP_policy", PRI + "definitions.JLDP_policy",
         "prosa.behavior.job.job_cost", "SF.R2bv.Rprop"] + DOWN

shutil.rmtree(RUN, ignore_errors=True)
rcs = [cli("export", "--mode", "statement", "--manifest", ROOT / "fixtures/stmt/c/manifest.json",
           "--roots", ",".join(ROOTS), "--out", RUN)[0]]
rcs.append(cli("translate", "--input", RUN / "source.ndjson", "--out", RUN)[0])
rcs.append(cli("validate", "--run", RUN)[0])
v = json.loads((RUN / "validate.json").read_text())
R, rep = results(RUN)
OUT["pipeline"] = {"exit_codes": rcs, "validation": v.get("status"), "by_validation": v.get("by_validation")}
check(rcs[0] == 0 and rcs[2] == 0 and v.get("status") == "STATEMENT_VALIDATED",
      "probe: export/translate/validate (JLFP_policy not translated, everything claimed validated)")
o = R["mathcomp.boot.eqtype.opt_eqP"]
# (R3G-F, ITERATION_LOG entry 10: Equality.type also carries its nested result-sort levels; the eqType
# levels are read from its row instead of being listed: the condition stays "generic, none defaulted")
EQ_LPS = R["mathcomp.boot.eqtype/Equality.type"]["level_params"]
EQ_LV = sorted(l for l in json.loads((RUN / "source.ndjson").read_text().splitlines()[4])["levels"]
               if "u_" + l.replace(".", "_") in EQ_LPS)
OBLS = [f"mathcomp.boot.eqtype.opt_eqP__rocq2lean_obligation_{k}" for k in range(1, 6)]
OUT["opt_eqP"] = {k: o.get(k) for k in ("status", "target_kind", "level_params", "implicit_levels", "universe_level_defaults")}
# (A′: opt_eqP is opaque data translated with its body -- an opaque constant pending on the 5 proof
# subterms of its body, each a statement; C-1: all generic in eqtype.51/58)
check(o["status"] == "PENDING_KERNEL_CHECKED" and o["target_kind"] == "opaque" and set(OBLS) <= set(o["pending_hypotheses"])
      and o.get("implicit_levels") == EQ_LV and "u_mathcomp_boot_eqtype_51" in EQ_LPS and not o.get("universe_level_defaults")
      and all(R[n]["status"] == "STATEMENT_KERNEL_CHECKED" and R[n]["level_params"] == EQ_LPS
              and not R[n].get("universe_level_defaults") for n in OBLS),
      "C-1: opt_eqP (A′: an opaque constant) and its obligation statements keep the reference levels as parameters, none defaulted")
oe = R["mathcomp.boot.eqtype.Datatypes_option__canonical__eqtype_Equality"]
# (R-CARRIER P2, entry 11: the operand's and the result's structure levels are independent copies; the
# carrier 51 is one class; every parameter is an eqType level or a copy of one, none defaulted)
_eq_base = lambda p: p.split("__c")[0]
check(set(map(_eq_base, oe.get("level_params") or [])) == set(EQ_LPS) and "u_mathcomp_boot_eqtype_51" in oe["level_params"]
      and not oe.get("universe_level_defaults"),
      "option's canonical eqType is generic in the eqType levels (no longer Set-level only)")
ps = R["prosa.model.processor.ideal.processor_state"]
OUT["processor_state"] = {"status": ps["status"], "message": ps.get("message", "")[:400]}
# correction (2026-10-14): with opt_eqP generic, the ideal processor_state was still narrowed: `unit`'s
# finType (level 0) forced Job : JobType.{0, _} through one carrier level -- refused, never claimed.
# R-CARRIER (entry 11) separates the instance's carrier from Job's, but the definition is still refused,
# now at a reference whose shared level gets an R2F `max` argument (REFERENCE_COHERENCE; RULE_BACKLOG).
# (Corpus run 1's broad P1 claimed it; the narrowed P1 does not. The check states the actual result.)
# Stage 3 (entry 13, docs/COHERENCE_READINGS.md §6): with shared levels per occurrence, ProcessorState has
# plain parameters (its sort read through R2F), so `unit`'s carrier no longer reaches Job's: the definition
# is claimed, and Job's carrier argument equals eqtype.51 at every model of the source facts (not narrowed).
import importlib.util  # noqa: E402
_sp = importlib.util.spec_from_file_location("r2l_audit_c", ROOT / "tools" / "audit.py")
_A = importlib.util.module_from_spec(_sp)
_sp.loader.exec_module(_A)
_facts = json.loads((RUN / "source.ndjson").read_text().splitlines()[4])
_src = {"u_" + l.replace(".", "_"): l for l in _facts["levels"]}
_t = ps.get("target_type") or {}
while _t.get("k") == "forall" and _t["n"].startswith("h_"):
    _t = _t["b"]
_job = _t.get("t", {}) if _t.get("k") == "forall" else {}
_own = {q: _src[q] for q in ps.get("level_params") or [] if q in _src}
_U51 = "u_mathcomp_boot_eqtype_51"
_generic = (_job.get("n") == "Rocq.prosa.behavior.job.JobType" and len(_job.get("u", [])) == 4 and
            _A.equal_at_models(_A.Facts(_facts), {**_own, _U51: "mathcomp.boot.eqtype.51"}, _job["u"][1], {"k": "param", "n": _U51}))
OUT["processor_state"]["job_binder"] = _job
check(ps["status"] in ("PENDING_KERNEL_CHECKED", "TRANSLATED_AND_CHECKED") and _generic,
      "ideal processor_state (protected) is claimed with Job's carrier generic (equal to eqtype.51 at every model), "
      "never narrowed (since stage 3: shared levels per occurrence)")
claimed = [r for r in rep["results"] if r["status"] in ("STATEMENT_KERNEL_CHECKED", "STATEMENT_PENDING_KERNEL_CHECKED",
                                                         "TRANSLATED_AND_CHECKED", "PENDING_KERNEL_CHECKED")]
stmt_rows = [r for r in claimed if r["status"].startswith("STATEMENT_")]
check(all(not r.get("universe_level_defaults") for r in stmt_rows), f"no statement row has a defaulted level ({len(stmt_rows)} statements)")
a0 = json.loads((RUN / "audit.json").read_text())
check(a0.get("status") == "OK" and not [p for p in a0.get("problems", []) if "free in the statement" in p["message"]],
      "the audit's source-derived generality check accepts every claimed row")
# R2B-V (docs/UNIVERSE_FAMILY_C.md §4, approved 2026-10-14): the policy definitions are declared at the
# sort of their value (rel at the job's level); the job stays generic
OUT["policies"] = {}
for n in ("JLFP_policy", "FP_policy", "JLDP_policy"):
    jl = R[PRI + "definitions." + n]
    OUT["policies"][n] = {k: jl.get(k) for k in ("status", "level_params", "sort_lowered_levels", "result_sort_inherited", "message")}
    check(jl["status"] == "TRANSLATED_AND_CHECKED" and jl.get("result_sort_inherited") and jl.get("protected")
          and "u_mathcomp_boot_eqtype_51" in jl["level_params"]
          and {x["level"] for x in jl["sort_lowered_levels"]} >= {"Corelib.ssr.ssrbool.1105"},
          f"{n} (protected): translated under R2B-V, generic in the job's level, result sort lowered from rel's level")
rp_ = R["SF.R2bv.Rprop"]
OUT["Rprop"] = {k: rp_.get(k) for k in ("status", "result_sort_inherited", "message")}
check(not rp_.get("result_sort_inherited"), "R2B-V never declares a Prop-valued body (Prop ≤ Type cumulativity) as a proposition")
dn = {n: R[n]["status"] for n in DOWN}
OUT["downstream"] = {n: {"status": R[n]["status"], "message": (R[n].get("message") or "")[:300]} for n in DOWN}
check(all(st in ("TRANSLATED_AND_CHECKED", "PENDING_KERNEL_CHECKED", "STATEMENT_KERNEL_CHECKED", "STATEMENT_PENDING_KERNEL_CHECKED")
          for st in dn.values()), f"downstream uses of the policies translate and are audited: {dn}")


# 2. negative controls: the target itself is narrowed (not merely a flag). A declaration's universe
# parameters are replaced by closed levels in its type and value (always kernel-correct: a universe
# parameter can be instantiated at any level), it is re-emitted under its own name, every row that
# references it is reported blocked, and every self-reported trace of the specialization is removed
# (no `universe_level_defaults`, no residual record, no implicit level for the removed parameters)
def subst_levels(j, m):
    if isinstance(j, list):
        return [subst_levels(x, m) for x in j]
    if not isinstance(j, dict):
        return j
    if j.get("k") == "param" and j.get("n") in m:
        return m[j["n"]]
    return {k: subst_levels(v, m) for k, v in j.items()}


def closed(n):
    x = {"k": "zero"}
    for _ in range(n):
        x = {"k": "succ", "l": x}
    return x


def specialize(rep0, source, levels):
    rep_ = copy.deepcopy(rep0)
    rows = {r["source"]: r for r in rep_["results"]}
    r = rows[source]
    m = {p: closed(k) for p, k in levels.items()}
    params = set(levels)
    for k in ("target_type", "target_value"):
        r[k] = subst_levels(r[k], m)
    r["target_ctors"] = subst_levels(r.get("target_ctors") or [], m)
    r["level_interp"] = [x for x in subst_levels(r.get("level_interp") or [], m)
                         if "u_" + x["level"].replace(".", "_") not in params]
    r["level_params"] = [p for p in r["level_params"] if p not in params]
    r["implicit_levels"] = [l for l in r.get("implicit_levels") or [] if "u_" + l.replace(".", "_") not in params]
    r["universe_level_defaults"], r["universe_residuals"] = 0, None
    # every row referencing the narrowed declaration (transitively) is reported blocked
    names, blocked = {r["target"]} | {c["name"] for c in r["target_ctors"]}, []
    changed = True
    while changed:
        changed = False
        for x in rep_["results"]:
            if x is r or x["source"] in blocked or not x.get("target"):
                continue
            js = json.dumps([x.get("target_type"), x.get("target_value"), x.get("target_ctors")])
            if any(f'"n": "{n}"' in js for n in names):
                blocked.append(x["source"])
                names |= {x["target"]} | {c["name"] for c in x.get("target_ctors") or []}
                changed = True
    for x in rep_["results"]:
        if x["source"] in blocked:
            for k in ("target", "target_type", "target_value", "target_ctors", "target_kind", "pending_hypotheses"):
                x.pop(k, None)
            x.update(status="BLOCKED_DEPENDENCY", message=f"failed dependencies: #[{source}]", blocked_by=[source])
    # (the report's root records follow their rows)
    for rr in rep_.get("roots") or []:
        if rr.get("name") in blocked or rr.get("source") in blocked:
            rr["status"] = "BLOCKED_DEPENDENCY"
    return rep_, blocked


OPT = "mathcomp.boot.eqtype.opt_eqP__rocq2lean_obligation_1"      # a statement (an extracted proof subterm)
E51, E58 = "u_mathcomp_boot_eqtype_51", "u_mathcomp_boot_eqtype_58"
# (0,0): the pre-C translation; (0,1): a nonzero closed level that R3 (no raising) admits, so only the
# generality obligation can reject it; (2,2): raising, rejected by R3 itself
for l51, l58, want in ((0, 0, "free in the statement"), (0, 1, "free in the statement"),
                       (2, 2, "not entailed by the source universe graph")):
    tag = f"{l51}-{l58}"
    rep2, blocked = specialize(rep, OPT, {E51: l51, E58: l58})
    row = next(r for r in rep2["results"] if r["source"] == OPT)
    _, kernel_ok, rc, cons, aud = forge_run(RUN, f"narrowed-statement-{tag}", rep2, check_cmd="validate")
    probs = [p["message"] for p in aud.get("problems", []) if p["message"].startswith(OPT + ":")]
    OUT[f"negative_narrowed_statement_{tag}"] = {
        "kernel": kernel_ok, "validate_exit": rc, "blocked_dependents": len(blocked), "audit_problems": probs[:3],
        "row_self_reports": {k: row.get(k) for k in ("universe_level_defaults", "universe_residuals", "implicit_levels", "level_params")}}
    check(kernel_ok and rc == 2 and not row.get("universe_level_defaults") and row.get("universe_residuals") is None
          and not {"mathcomp.boot.eqtype.51", "mathcomp.boot.eqtype.58"} & set(row.get("implicit_levels") or [])
          and any(want in p for p in probs) and not any("defaulted" in p for p in probs),
          f"opt_eqP's obligation narrowed to Equality.type.{{{l51},{l58}}} (no self-reported trace): kernel-accepted, rejected by the "
          f"audit from the source ({want!r})")

# a protected definition narrowed at a quantification range: job_cost {Job : JobType.{0,_}}
SCH = "prosa.behavior.job.job_cost"
check(R[SCH]["status"] in ("TRANSLATED_AND_CHECKED", "PENDING_KERNEL_CHECKED") and E51 in R[SCH]["level_params"],
      "protected job_cost translates generically (Job : JobType.{u51,_})")
rep3, blocked3 = specialize(rep, SCH, {E51: 0, E58: 0})
_, kernel_ok, rc, cons, aud = forge_run(RUN, "narrowed-protected-definition", rep3, check_cmd="validate")
probs = [p["message"] for p in aud.get("problems", []) if p["message"].startswith(SCH + ":")]
OUT["negative_narrowed_protected_definition"] = {"kernel": kernel_ok, "validate_exit": rc,
                                                 "blocked_dependents": len(blocked3), "audit_problems": probs[:3]}
check(kernel_ok and rc == 2 and any("narrowed quantification range" in p for p in probs),
      "protected job_cost narrowed at its Job binder (no self-reported trace): kernel-accepted, audit-rejected")

# R2B-V negative controls (report-level: the declarations are unchanged, so the kernel replay accepts
# them; only the independent audit can reject)
JL = PRI + "definitions.JLFP_policy"


def forge_row(label, src, fn):
    rep2 = copy.deepcopy(rep)
    row = next(r for r in rep2["results"] if r["source"] == src)
    fn(row)
    _, kernel_ok, rc, cons, aud = forge_run(RUN, label, rep2, check_cmd="validate")
    probs = [p["message"][:300] for p in aud.get("problems", []) if p["message"].startswith(src + ":")]
    # (the consumer, also independent of the translator, may refuse first: its detectors are reported)
    probs += [f"consumer {d}" for d, v in (cons.get("detectors") or {}).items() if v != "OK"]
    OUT.setdefault("negative_r2bv", {})[label] = {"kernel": kernel_ok, "validate_exit": rc, "audit_problems": probs[:4]}
    return kernel_ok, rc, probs


def set_sigma(level, sigma):
    def f(row):
        for x in row["sort_lowered_levels"]:
            if x["level"] == level:
                x["sigma"] = sigma
        for x in row.get("solved_levels") or []:
            if x["level"] == level:
                x["sigma"] = sigma
    return f


k, rc, probs = forge_row("r2bv-not-a-lowering", JL, set_sigma("Corelib.ssr.ssrbool.1171", closed(5)))
check(k and rc == 2 and any("not a lowering" in p for p in probs),
      "R2B-V with a solution above the source level (Set+5 for a level the graph does not place there): audit-rejected")
k, rc, probs = forge_row("r2bv-binder-level", JL, lambda row: row["sort_lowered_levels"].append(
    {"level": "mathcomp.boot.eqtype.51", "sigma": {"k": "zero"}}))
check(k and rc == 2 and probs, "R2B-V claimed for a level of a binder (not only the result sort): audit-rejected")
k, rc, probs = forge_row("r2bv-without-rule", JL, lambda row: row.update(result_sort_inherited=False))
check(k and rc == 2 and any("specialized statement" in p or p == "consumer interface" for p in probs),
      "a protected result-sort lowering without the R2B-V rule is still refused by the interface protection")
STMT_ROW = next(r["source"] for r in rep["results"] if r["status"] == "STATEMENT_KERNEL_CHECKED" and r.get("level_params"))
k, rc, probs = forge_row("r2bv-on-statement", STMT_ROW, lambda row: row.update(
    result_sort_inherited=True, sort_lowered_levels=[{"level": "x", "sigma": {"k": "zero"}}]))
check(k and rc == 2 and probs, "R2B-V claimed on a statement: audit-rejected (statements never)")

# 3. positive control: the generic translations are usable at nonzero universes (kernel-checked
# instantiations and a use of the statement at a universe-3 eqType); the same file fails against the
# narrowed module (discrimination)
POS = """import Rocq2LeanOut
open Lean Meta Elab Command
def lv (n : Nat) : Level := Level.ofNat n
-- kernel-checked: each declaration instantiated at nonzero universes
def posInst (n : Name) (us : List Nat) (tag : String) : MetaM Unit := do
  let ci ← getConstInfo n
  let us := us.map lv
  addDecl (.defnDecl { name := Name.mkSimple ("posctrl_" ++ tag), levelParams := [], type := ← instantiateTypeLevelParams ci.toConstantVal us,
                       value := mkConst n us, hints := .opaque, safety := .safe })
run_meta posInst `RocqPending.mathcomp.boot.eqtype.opt_eqP EQUS "opt_eqP"
run_meta posInst `Rocq.mathcomp.boot.eqtype.opt_eqP__rocq2lean_obligation_1.statement EQUS "opt_eqP_obligation"
run_meta posInst `RocqPending.mathcomp.boot.eqtype.Datatypes_option__canonical__eqtype_Equality OEUS "option_eqType"
run_meta posInst `RocqPending.prosa.behavior.schedule.ProcessorState PSUS "ProcessorState"
SCHED_LINE
POLICY_LINES
-- a use: the statement applies to an eqType at universe 3 (δ-unfolds the statement in the kernel)
run_meta do
  let ci ← getConstInfo `Rocq.mathcomp.boot.eqtype.opt_eqP__rocq2lean_obligation_1.statement
  let us := EQLV
  let v ← instantiateValueLevelParams ci us
  let .forallE _ d _ _ := v | throwError "statement is not a quantification"
  -- the binder ranges over Equality.type at closed nonzero universes (its carrier level at least 3)
  unless d.isConstOf `Rocq.mathcomp.boot.eqtype.Equality.type && d.constLevels!.all (fun l => !l.isZero) do throwError "binder range {d}"
  let h := mkConst `Rocq.mathcomp.boot.eqtype.opt_eqP__rocq2lean_obligation_1.statement us
  addDecl (.defnDecl { name := `posctrl_use, levelParams := [], type := mkForall `h .default h v,
                       value := mkLambda `h .default h (.bvar 0), hints := .opaque, safety := .safe })
"""

# (universe argument counts come from the report rows: nonzero, carrier level at least 3)
EQUS = [3 + k for k in range(len(EQ_LPS))]
POS = POS.replace("EQUS", str(EQUS)).replace("EQLV", "[" + ", ".join(f"lv {x}" for x in EQUS) + "]")
POS = POS.replace("OEUS", str([3 + k for k in range(len(oe["level_params"]))]))
POS = POS.replace("PSUS", str([3 + k for k in range(len(R["prosa.behavior.schedule.ProcessorState"]["level_params"]))]))
# (schedule's target name and universe parameters come from its report row)
POS = POS.replace("POLICY_LINES", "\n".join(
    f'run_meta posInst `{R[n]["target"]} {[2 + k for k in range(len(R[n]["level_params"]))]} "{n.split(".")[-1]}"'
    for n in [JL, PRI + "edf.EDF", PRI + "definitions.hep_job"] if R[n].get("target")))
POS = POS.replace("SCHED_LINE", f'run_meta posInst `{R[SCH]["target"]} {[2 + k for k in range(len(R[SCH]["level_params"]))]} "job_cost"')


def run_pos(run_dir, name):
    import os
    import subprocess
    lean = Path(run_dir) / "lean"
    (lean / f"{name}.lean").write_text(POS)
    env = dict(os.environ, PATH=f"{Path.home()}/.elan/bin:" + os.environ["PATH"])
    lp = subprocess.run(["lake", "-d", str(ROOT), "env", "printenv", "LEAN_PATH"], capture_output=True, text=True, env=env).stdout.strip()
    env["LEAN_PATH"] = f"{lp}:{lean}"
    p = subprocess.run(["lean", f"{name}.lean"], cwd=lean, capture_output=True, text=True, env=env)
    return p.returncode, (p.stdout + p.stderr)[:600]


rc_pos, out_pos = run_pos(RUN, "PositiveControl")
rc_neg, out_neg = run_pos(RUN.parent / f"{RUN.name}-forged-narrowed-statement-0-0", "PositiveControl")
OUT["positive_nonzero_universes"] = {"generic_exit": rc_pos, "generic_output": out_pos, "narrowed_exit": rc_neg,
                                     "narrowed_output": out_neg}
check(rc_pos == 0, "positive control: opt_eqP, option's eqType, ProcessorState, job_cost, JLFP_policy, EDF, hep_job kernel-checked at universes 2..; "
                   "the statement applies to an Equality.type at nonzero universes")
check(rc_neg != 0, "the same positive control fails against the narrowed module (it discriminates)")

(ROOT / "reports" / "statement_only" / "test_universe_c.json").write_text(json.dumps(OUT, indent=1) + "\n")
finish("test-universe-c")

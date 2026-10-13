#!/usr/bin/env python3
"""Task C (docs/UNIVERSE_FAMILY_C.md): the Equality.type / JobType universe family, through the real CLI
on a small Prosa probe (fixtures/stmt/c: opt_eqP, ideal processor_state, JLFP_policy).

1. C-1 (R3G for statements): MathComp's opaque-data interface opt_eqP keeps its reference levels as
   parameters (eqtype.51, eqtype.58), so option's canonical eqType and Prosa's ideal processor_state
   (generic jobs) translate; no statement row has a defaulted level.
2. Negative control: a statement row claiming a defaulted level (the old behaviour) is
   kernel-accepted and rejected by the audit.
3. The policy family (JLFP_policy) stays refused: the only Lean representation lowers a protected
   declaration's result sort (no approved representation change); the refusal is reported.

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
ROOTS = ["mathcomp.boot.eqtype.opt_eqP", "prosa.model.processor.ideal.processor_state",
         "prosa.model.priority.definitions.JLFP_policy"]

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
OUT["opt_eqP"] = {k: o.get(k) for k in ("status", "level_params", "implicit_levels", "universe_level_defaults")}
check(o["status"] == "STATEMENT_KERNEL_CHECKED" and o.get("implicit_levels") == ["mathcomp.boot.eqtype.51", "mathcomp.boot.eqtype.58"]
      and not o.get("universe_level_defaults"), "C-1: opt_eqP's reference levels are parameters (R3G on the statement), none defaulted")
oe = R["mathcomp.boot.eqtype.Datatypes_option__canonical__eqtype_Equality"]
check(oe.get("level_params") == ["u_mathcomp_boot_eqtype_51", "u_mathcomp_boot_eqtype_58"],
      "option's canonical eqType is generic in the eqType levels (no longer Set-level only)")
ps = R["prosa.model.processor.ideal.processor_state"]
check(ps["status"] == "PENDING_KERNEL_CHECKED" and all(R[f"prosa.model.processor.ideal.processor_state__rocq2lean_obligation_{k}"]["status"]
                                                         == "STATEMENT_PENDING_KERNEL_CHECKED" for k in (1, 2)),
      "ideal processor_state and its obligations translate (pending on proof tasks only)")
stmt_rows = [r for r in rep["results"] if r["status"] in ("STATEMENT_KERNEL_CHECKED", "STATEMENT_PENDING_KERNEL_CHECKED")]
check(all(not r.get("universe_level_defaults") for r in stmt_rows), f"no statement row has a defaulted level ({len(stmt_rows)} statements)")
jl = R["prosa.model.priority.definitions.JLFP_policy"]
OUT["JLFP_policy"] = {"status": jl["status"], "message": jl.get("message", "")[:500]}
check(jl["status"] == "UNIVERSE_REJECTED", "JLFP_policy stays refused (policy blocker: no approved result-sort lowering)")

# 2. negative control: a statement row claiming a defaulted level (the pre-C behaviour), with a
# residual record the earlier audit accepted (generic declaration at its defaults = the reported one);
# the declaration itself is unchanged, so the kernel replay accepts everything
rep2 = copy.deepcopy(rep)
row = next(r for r in rep2["results"] if r["source"] == "mathcomp.boot.eqtype.opt_eqP")
row["universe_level_defaults"] = 1
row["universe_residuals"] = {"params": ["u_residual_0"], "defaults": [{"k": "zero"}],
                             "justification": "kernel accepted the declaration with these levels as fresh universe parameters",
                             "generic_type": row["target_type"], "generic_value": row["target_value"]}
_, kernel_ok, rc, cons, aud = forge_run(RUN, "defaulted-statement-level", rep2, check_cmd="validate")
probs = [p["message"] for p in aud.get("problems", []) if p["message"].startswith("mathcomp.boot.eqtype.opt_eqP:")]
OUT["negative_defaulted_statement_level"] = {"kernel": kernel_ok, "validate_exit": rc, "audit_problems": probs[:3],
                                             "consumer": cons.get("status")}
check(kernel_ok and rc == 2 and any("defaulted universe level" in p for p in probs),
      "a statement row with a defaulted level is kernel-accepted and audit-rejected (specialization)")

(ROOT / "reports" / "statement_only" / "test_universe_c.json").write_text(json.dumps(OUT, indent=1) + "\n")
finish("test-universe-c")

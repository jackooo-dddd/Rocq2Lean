#!/usr/bin/env python3
"""Pending-to-final assembly (docs/ASSEMBLY.md), through the real CLI, on the synthetic fixture
fixtures/stmt/asm (Asm.v). The proofs are tiny synthetic test proofs (tests/statement/proofs/), never
Prosa/Classic/MathComp proofs.

1. Pipeline: export --mode statement, translate, validate, tasks.
2. Task records: template names RocqProofTemplates.T<id>.proof, final names Rocq.<name>, generalization
   form (over proofs / over data), opaque-value tasks accept no submission.
3. check-proof: accepted submissions; refused ones (opaque value, a constant outside the template
   namespace).
4. Partial assembly without proofs: every pending row stays pending; --complete fails.
5. Assembly with proofs: a theorem without prerequisites, an extracted obligation (proof uses propext:
   reported in the axioms of the assembled definitions), assembled definitions, an assembled pending
   inductive, an assembled statement whose generalized proof is reused (kernel-checked instantiation),
   a statement about the re-emitted inductive whose generalized proof is about the pending inductive
   (ASSEMBLY_TRANSPORT_REQUIRED, never cast), dependents of opaque data kept as an interface (pick_wf)
   held (OPAQUE_BINDING_PENDING) even though a generalized proof over the data was verified; A′: opaque
   data translated with its body (pick) needs no binding.
6. Determinism and idempotence of assembly.
7. Invalid claimed submissions are refused: altered after its check, missing, stale after a new
   validation.
8. Computation, measured separately: definitional reduction (kernel `rfl`), compiled evaluation (#eval).

Writes reports/statement_only/test_assembly.json.
"""
import json
import shutil
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from lib import ROOT, check, cli, finish  # noqa: E402

OUT = {}
P = ROOT / "tests" / "statement" / "proofs"
RUN = ROOT / "runs" / "st-asm"
ROOTS = ["SF.Asm." + n for n in ("double_zero", "zero_of_le", "is_zero_of_intro", "pick_succ_pos", "pick_wf_succ_pos")]
OBL = "SF.Asm.half_sig__rocq2lean_obligation_1"


def tasks():
    return {t["source"]["kernel_name"]: t for t in map(json.loads, open(RUN / "PROOF_TASKS.jsonl"))}


def submit(task, proof_file):
    f = RUN / "submissions" / f"{task['task_id']}.lean"
    f.parent.mkdir(exist_ok=True)
    f.write_text((P / proof_file).read_text().replace("@TASK@", task["task_id"]))
    rc, out = cli("check-proof", "--run", RUN, "--task", task["task_id"], "--file", f)
    res = json.loads((RUN / "proofs" / task["task_id"] / "result.json").read_text())
    return rc, res


def latest_assembly():
    ds = sorted((RUN / "assembly").glob("*/assembly.json"), key=lambda p: p.stat().st_mtime_ns) if (RUN / "assembly").exists() else []
    return json.loads(ds[-1].read_text()) if ds else None


def rows(asm):
    rep = json.loads((Path(asm["assembly_dir"]) / "assembly_report.json").read_text())
    return {r["source"]: r for r in rep["results"]}, rep


# 1. pipeline
shutil.rmtree(RUN, ignore_errors=True)
rcs = [cli("export", "--mode", "statement", "--manifest", ROOT / "fixtures/stmt/asm/manifest.json",
           "--roots", ",".join(ROOTS), "--out", RUN)[0]]
rcs.append(cli("translate", "--input", RUN / "source.ndjson", "--out", RUN)[0])
rcs.append(cli("validate", "--run", RUN)[0])
rcs.append(cli("tasks", "--run", RUN)[0])
v = json.loads((RUN / "validate.json").read_text())
OUT["pipeline"] = {"exit_codes": rcs, "validation": v.get("status"), "by_validation": v.get("by_validation")}
check(rcs == [0, 0, 0, 0] and v.get("status") == "STATEMENT_VALIDATED", "fixture: export/translate/validate/tasks")

# 2. task records
T = tasks()
check(all(t["lean"]["reserved_name"] == f"RocqProofTemplates.T{t['task_id']}.proof" and
          t["lean"]["final_name"] == "Rocq." + t["source"]["kernel_name"] for t in T.values()),
      "tasks: template name RocqProofTemplates.T<id>.proof; Rocq.<name> reserved for the final declaration")
gen = {n: t["prerequisites"]["generalization"]["form"] for n, t in T.items()}
check(gen.get("SF.Asm.zero_of_le") == "over_proof_prerequisites" and gen.get("SF.Asm.pick_wf_succ_pos") == "over_data_prerequisites"
      and gen.get("SF.Asm.double_zero") == "none" and gen.get("SF.Asm.pick_succ_pos") == "none",
      "tasks: generalization form recorded (none / over proofs / over data)")
check(T["SF.Asm.pick_wf"]["kind"] == "opaque_value" and T["SF.Asm.pick_wf"]["accepts_submissions"] is False
      and "SF.Asm.pick" not in T, "tasks: no value task for pick (A′: translated body); the kept interface's "
      "value task (pick_wf) accepts no submission")
OUT["tasks"] = {n: {"kind": t["kind"], "generalization": gen[n], "accepts_submissions": t["accepts_submissions"]}
                for n, t in sorted(T.items())}

# 3. check-proof (refusals first)
rc, res = submit(T["SF.Asm.pick_wf"], "pick_value.lean")
check(rc == 2 and res["status"] == "PROOF_REJECTED" and res.get("stage") == "policy", "check-proof refuses an opaque-data value")
rc, res = submit(T["SF.Asm.double_zero"], "neg_outside_namespace.lean")
check(rc == 2 and any("outside" in p for p in res.get("problems") or []),
      "check-proof refuses a submission declaring a constant outside its template namespace")
OUT["check_proof_refusals"] = {"opaque_value": res.get("problems")}
shutil.rmtree(RUN / "proofs" / T["SF.Asm.pick_wf"]["task_id"])
shutil.rmtree(RUN / "proofs" / T["SF.Asm.double_zero"]["task_id"])

# 4. partial assembly without proofs
rc, out = cli("assemble", "--run", RUN)
asm0 = latest_assembly()
check(rc == 0 and asm0 and asm0["status"] == "ASSEMBLY_VALIDATED" and asm0["summary"]["assembled"] == 0
      and asm0["summary"]["proofs_assembled"] == 0, "assembly without proofs: validated, nothing assembled, all pending kept")
rc, out = cli("assemble", "--run", RUN, "--complete")
check(rc == 2 and "ASSEMBLY_INCOMPLETE" in out, "--complete fails while targets remain unresolved")
OUT["assembly_without_proofs"] = asm0["summary"] if asm0 else None

# 5. assembly with proofs
accepted = {}
for n, f in [("SF.Asm.double_zero", "double_zero.lean"), (OBL, "half_sig_obligation.lean"),
             ("SF.Asm.zero_of_le", "zero_of_le.lean"), ("SF.Asm.is_zero_of_intro", "is_zero_of_intro.lean"),
             ("SF.Asm.pick_succ_pos", "pick_succ_pos.lean"), ("SF.Asm.pick_wf_succ_pos", "pick_wf_succ_pos.lean")]:
    rc, res = submit(T[n], f)
    accepted[n] = res
    check(rc == 0 and res["status"] == "LEAN_PROOF_KERNEL_VERIFIED", f"check-proof accepts the synthetic proof of {n}")
check("propext" in (accepted[OBL].get("axioms") or []), "the obligation proof's axiom (propext) is recorded")
rc, out = cli("assemble", "--run", RUN)
asm = latest_assembly()
R, rep = rows(asm)
OUT["assembly"] = {"exit": rc, "summary": asm["summary"], "axioms_by_target": asm["axioms_by_target"],
                   "proof_dependent_computation": asm["proof_dependent_computation"],
                   "rows": {n: {k: r.get(k) for k in ("status", "target", "assembly", "proof_state", "proof_target", "assembly_note")}
                            for n, r in sorted(R.items())}}
check(rc == 0 and asm["status"] == "ASSEMBLY_VALIDATED", "assembly with proofs: ASSEMBLY_VALIDATED (consumer and audit)")
st = lambda n: (R[n]["assembly"], R[n].get("proof_state"))
check(st("SF.Asm.double_zero") == ("VALIDATED", "PROOF_ASSEMBLED") and R["SF.Asm.double_zero"]["proof_target"] == "Rocq.SF.Asm.double_zero",
      "a theorem without prerequisites: final theorem Rocq.<name>")
check(st(OBL)[1] == "PROOF_ASSEMBLED", "the extracted obligation: final theorem")
check(R["SF.Asm.half_sig"]["assembly"] == "ASSEMBLED" and R["SF.Asm.half_sig"]["target"] == "Rocq.SF.Asm.half_sig"
      and R["SF.Asm.zero_of"]["assembly"] == "ASSEMBLED", "pending definitions assembled as Rocq.* (no hypotheses)")
check(R["SF.Asm.is_zero_of"]["assembly"] == "ASSEMBLED" and R["SF.Asm.is_zero_of"]["target"] == "Rocq.SF.Asm.is_zero_of",
      "the pending inductive is re-emitted as a new type Rocq.SF.Asm.is_zero_of")
check(st("SF.Asm.zero_of_le") == ("ASSEMBLED", "PROOF_ASSEMBLED"),
      "a generalized proof over a proof prerequisite is reused: the kernel accepts its instantiation at the final statement")
check(st("SF.Asm.is_zero_of_intro") == ("ASSEMBLED", "ASSEMBLY_TRANSPORT_REQUIRED") and not R["SF.Asm.is_zero_of_intro"].get("proof_target"),
      "a generalized proof about the pending inductive does not prove the statement about the re-emitted one: "
      "ASSEMBLY_TRANSPORT_REQUIRED, no final theorem")
check(R["SF.Asm.pick_wf"].get("proof_state") == "OPAQUE_BINDING_PENDING" and R["SF.Asm.pick_wf_succ"]["assembly"] == "OPAQUE_BINDING_PENDING"
      and R["SF.Asm.pick_wf_succ_pos"]["assembly"] == "OPAQUE_BINDING_PENDING",
      "opaque data kept as an interface is not bound; its dependents stay pending even with a verified generalized proof over it")
check(R["SF.Asm.pick"]["assembly"] == "VALIDATED" and R["SF.Asm.pick"]["target"] == "Rocq.SF.Asm.pick"
      and R["SF.Asm.pick_succ"]["assembly"] == "VALIDATED" and st("SF.Asm.pick_succ_pos") == ("VALIDATED", "PROOF_ASSEMBLED"),
      "A′: the opaque constant pick (translated body) and its dependents need no binding; pick_succ_pos gets its final theorem")
axb = asm["axioms_by_target"]
check("propext" in axb.get("Rocq.SF.Asm.half_sig", []) and "propext" in axb.get("Rocq.SF.Asm.zero_of", []),
      "assembled definitions report the axioms of the proofs they contain (not labelled axiom-free)")
check(not axb.get("Rocq.SF.Asm.double_zero"), "a final theorem whose proof uses no axiom reports none")
check(asm["proof_dependent_computation"] == [], "no elimination of a Prop inductive into data on an assembled proof (fixture)")
rc2, out2 = cli("assemble", "--run", RUN, "--complete")
check(rc2 == 2 and "ASSEMBLY_INCOMPLETE" in out2, "--complete still fails (transport required, opaque data)")

# 6. determinism / idempotence
first = (Path(asm["assembly_dir"]) / "assembly_report.json").read_bytes()
rc, out = cli("assemble", "--run", RUN)
asm2 = latest_assembly()
check(rc == 0 and asm2["assembly_dir"] == asm["assembly_dir"] and
      (Path(asm2["assembly_dir"]) / "assembly_report.json").read_bytes() == first,
      "assembly is deterministic: same inputs, same directory, byte-identical report")

# 8. computation, measured separately (before the negative cases alter the run)
lean_dir = Path(asm["assembly_dir"]) / "lean"
lp = subprocess.run(["lake", "-d", str(ROOT), "env", "printenv", "LEAN_PATH"], capture_output=True, text=True).stdout.strip()
tdirs = [str(Path(asm["assembly_dir"]) / "templates")]
env = {"LEAN_PATH": ":".join([lp, str(RUN / "lean"), *tdirs, str(lean_dir)]), "PATH": "/usr/bin:/bin"}
probes = {
    "definitional_reduction": "theorem probe : Rocq.SF.Asm.zero_of 3 = 0 := rfl\n",
    "compiled_evaluation": "#eval Rocq.SF.Asm.zero_of 3\n",
}
OUT["computation"] = {}
for k, body in probes.items():
    f = lean_dir / f"Probe_{k}.lean"
    f.write_text("import Rocq2LeanAssembled\n" + body)
    p = subprocess.run([str(Path.home() / ".elan/bin/lean"), str(f)], capture_output=True, text=True, cwd=lean_dir, env=env)
    OUT["computation"][k] = {"exit": p.returncode, "output": (p.stdout + p.stderr).strip()[:600]}
check(OUT["computation"]["definitional_reduction"]["exit"] == 0,
      "definitional reduction: Rocq.SF.Asm.zero_of 3 = 0 by rfl (the assembled proof field is irrelevant)")
OUT["computation"]["propositional_equations"] = "not applicable: the fixture has no recursion through a proof"

# 7. invalid claimed submissions
tz = T["SF.Asm.zero_of_le"]["task_id"]
pf = RUN / "proofs" / tz / accepted["SF.Asm.zero_of_le"]["template_file"]
saved = pf.read_text()
pf.write_text(saved + "\n-- altered after its check\n")
rc, out = cli("assemble", "--run", RUN)
check(rc == 2 and "PROOF_REJECTED" in out and "altered" in out, "an altered verified submission rejects the assembly")
pf.unlink()
rc, out = cli("assemble", "--run", RUN)
check(rc == 2 and "missing" in out, "a missing verified submission rejects the assembly")
pf.write_text(saved)
# re-validating unchanged artifacts reproduces validate.json byte for byte (checks stay current); a new
# export (new run id, new validation) makes every earlier check stale
rc, out = cli("validate", "--run", RUN)
cli("tasks", "--run", RUN)
rc, out = cli("assemble", "--run", RUN)
check(rc == 0, "re-validating unchanged artifacts keeps the checks current (validate.json reproduced)")
cli("export", "--mode", "statement", "--manifest", ROOT / "fixtures/stmt/asm/manifest.json", "--roots", ",".join(ROOTS), "--out", RUN)
cli("translate", "--input", RUN / "source.ndjson", "--out", RUN)
cli("validate", "--run", RUN)
cli("tasks", "--run", RUN)
rc, out = cli("assemble", "--run", RUN)
check(rc == 2 and "stale" in out, "after a new export and validation, earlier checks are stale: the assembly is refused")
OUT["negatives_last_output"] = out[-400:]

(ROOT / "reports" / "statement_only").mkdir(parents=True, exist_ok=True)
(ROOT / "reports" / "statement_only" / "test_assembly.json").write_text(json.dumps(OUT, indent=1) + "\n")
finish("test-assembly")

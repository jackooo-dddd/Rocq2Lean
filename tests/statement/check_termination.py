#!/usr/bin/env python3
"""Task B: termination lowering with explicit termination obligations and unfolding equations
(docs/TERMINATION.md), through the real CLI, on the synthetic fixture fixtures/stmt/wf (Wf.v). The
proofs are tiny synthetic test proofs (tests/statement/proofs/wf_*.lean), never Prosa/Classic/MathComp.

1. Pipeline: export --mode statement, translate, validate, tasks. A recursion whose call is on a
   subterm Rocq's guard sees only through `sub` (edivr, modr) is translated pending on a generated
   termination obligation; its dependents are pending on it; its unfolding equation is a statement.
2. Conversion dependence: a definition whose type checks only by unfolding the lowered recursion (t3)
   is refused by the kernel and reported; the source declaration is identified (Rocq-side analysis in
   the corpus report).
3. Tasks: termination_obligation and unfolding_equation tasks, generalization recorded.
4. Negative controls: kernel-accepted mutations of the lowering and of the unfolding equation are
   rejected by the structural audit.
5. Assembly with the synthetic proofs: the termination obligation gets its final theorem, edivr and its
   dependents are assembled as Rocq.*, the unfolding equation's generalized proof is reused; modr (no
   proof supplied) stays pending.
6. Computation, measured separately on the assembled library: definitional reduction (kernel rfl /
   decide), the propositional unfolding equation (a fixture proof of divr 7 2 = 3 from it), compiled
   evaluation (#eval).

Writes reports/statement_only/test_termination.json.
"""
import copy
import json
import os
import shutil
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from lib import ROOT, check, cli, finish, forge_run, results  # noqa: E402

OUT = {}
P = ROOT / "tests" / "statement" / "proofs"
RUN = ROOT / "runs" / "st-wf"
ROOTS = ["SF.Wf.divr_le", "SF.Wf.t3", "SF.Wf.divr_7_2", "SF.Wf.modr"]
TE, UE = "SF.Wf.edivr__rocq2lean_termination_1", "SF.Wf.edivr__rocq2lean_unfold_1"
TM, UM = "SF.Wf.modr__rocq2lean_termination_1", "SF.Wf.modr__rocq2lean_unfold_1"


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


def find(e, pred, path=()):
    """Paths (key sequences) of the sub-expressions of a Lean expression JSON satisfying pred."""
    out = []
    if isinstance(e, dict):
        if pred(e):
            out.append(path)
        for k, v in e.items():
            out += find(v, pred, path + (k,))
    return out


def get(e, path):
    for k in path:
        e = e[k]
    return e


def head(e):
    while e.get("k") == "app":
        e = e["f"]
    return e


def drop_succ_arg(e, head_pred):
    """In the first application whose head satisfies head_pred and whose last argument is `Nat.succ x`,
    replace that argument by `x` (the recursive call's accumulator `q.succ` becomes `q`)."""
    succ = lambda x: x.get("k") == "app" and x["f"] == {"k": "const", "n": "Nat.succ", "u": []}
    ps = find(e, lambda x: x.get("k") == "app" and succ(x["a"]) and head_pred(head(x)))
    if not ps:
        return False
    node = get(e, ps[0])
    node["a"] = copy.deepcopy(node["a"]["a"])
    return True


def mutate(decl, label, fn):
    R, rep = results(RUN)
    rep = copy.deepcopy(rep)
    row = next(x for x in rep["results"] if x["source"] == decl)
    if not fn(row["target_value"]):
        OUT.setdefault("mutations", []).append({"mutation": label, "declaration": decl, "applicable": False})
        return None
    _, kernel_ok, rc, cons, aud = forge_run(RUN, label, rep, check_cmd="validate")
    struct = [p for p in aud.get("problems", []) if p["message"].startswith(f"{decl}:")]
    rec = {"mutation": label, "declaration": decl, "applicable": True, "kernel": "ACCEPTED" if kernel_ok else "REJECTED",
           "validate_exit": rc, "detectors": sorted({p["detector"] for p in struct}),
           "messages": [p["message"][:300] for p in struct][:3], "consumer": cons.get("status")}
    OUT.setdefault("mutations", []).append(rec)
    return rec


# 1. pipeline
shutil.rmtree(RUN, ignore_errors=True)
rcs = [cli("export", "--mode", "statement", "--manifest", ROOT / "fixtures/stmt/wf/manifest.json",
           "--roots", ",".join(ROOTS), "--out", RUN)[0]]
rcs.append(cli("translate", "--input", RUN / "source.ndjson", "--out", RUN)[0])
rcs.append(cli("validate", "--run", RUN)[0])
rcs.append(cli("tasks", "--run", RUN)[0])
v = json.loads((RUN / "validate.json").read_text())
R, rep = results(RUN)
OUT["pipeline"] = {"exit_codes": rcs, "validation": v.get("status"), "by_validation": v.get("by_validation"),
                   "rows": {n: {k: r.get(k) for k in ("status", "target", "pending_hypotheses", "synthesized_from", "synthetic_kind")}
                            for n, r in sorted(R.items())}}
# (translate exits 2: the root t3 is not translated, by design)
check(rcs[0] == 0 and rcs[1] == 2 and rcs[2] == 0 and rcs[3] == 0 and v.get("status") == "STATEMENT_VALIDATED",
      "fixture: export/translate/validate/tasks (t3 not translated, everything claimed validated)")
check(R["SF.Wf.edivr"]["status"] == "PENDING_KERNEL_CHECKED" and R["SF.Wf.edivr"]["pending_hypotheses"] == [TE]
      and R["SF.Wf.modr"]["pending_hypotheses"] == [TM],
      "a recursion on a subterm reached through a function (edivn_rec shape) is translated, pending on its termination obligation")
check(R[TE]["status"] == "STATEMENT_KERNEL_CHECKED" and R[TE]["synthesized_from"] == "SF.Wf.edivr"
      and R[TE]["target"] == f"Rocq.{TE}.statement", "the termination obligation is a generated, accepted statement")
check(R[UE]["status"] == "STATEMENT_PENDING_KERNEL_CHECKED" and R[UE]["pending_hypotheses"] == [TE],
      "the unfolding equation is a generated statement, pending on the termination obligation")
check(all(R[n]["status"] in ("PENDING_KERNEL_CHECKED", "STATEMENT_PENDING_KERNEL_CHECKED") and R[n]["pending_hypotheses"] == [TE]
          for n in ("SF.Wf.divr", "SF.Wf.T3", "SF.Wf.divr_le", "SF.Wf.divr_7_2")),
      "dependents (definitions, a type, statements) are pending on the termination obligation, not blocked")
check(R["SF.Wf.sub"]["status"] == "TRANSLATED_AND_CHECKED", "the structural helper is translated as before")

# 2. conversion dependence: t3 : T3 := 0 type-checks only by unfolding edivr
check(R["SF.Wf.t3"]["status"] == "KERNEL_REJECTED", "a definition needing definitional unfolding of the lowered recursion is refused (reported, not claimed)")
OUT["conversion_dependent"] = {"SF.Wf.t3": R["SF.Wf.t3"]["message"][:400]}

# 3. tasks
T = tasks()
check(T[TE]["kind"] == "termination_obligation" and T[UE]["kind"] == "unfolding_equation"
      and T[TE]["source"]["generated_for"] == "SF.Wf.edivr" and T[TE]["prerequisites"]["generalization"]["form"] == "none"
      and T[UE]["prerequisites"]["generalization"]["form"] == "over_proof_prerequisites",
      "tasks: termination obligation (no prerequisite) and unfolding equation (generalized over the obligation, a proof)")
OUT["tasks"] = {n: {"kind": t["kind"], "statement": t["lean"]["statement"][:600]} for n, t in sorted(T.items())}

# 4. negative controls (kernel-accepted, audit-rejected)
# (the lowering's recursive call is `ih n cert q.succ`, headed by the induction hypothesis, a bound
# variable; the equation's is `RocqPending.SF.Wf.edivr d n q.succ`)
for decl, label, fn in [("SF.Wf.edivr", "wf-lowering-changed-accumulator", lambda e: drop_succ_arg(e, lambda h: h.get("k") == "bvar")),
                        (UE, "unfolding-rhs-changed-accumulator",
                         lambda e: drop_succ_arg(e, lambda h: h == {"k": "const", "n": "RocqPending.SF.Wf.edivr", "u": []}))]:
    rec = mutate(decl, label, fn)
    check(rec is not None and rec["kernel"] == "ACCEPTED" and rec["validate_exit"] == 2 and "structure" in rec["detectors"],
          f"mutation {label}: kernel-accepted, rejected by the structural audit")

# 5. assembly with proofs (edivr's obligation and equation; modr's left unsupplied)
rc, res = submit(T[TE], "wf_edivr_termination.lean")
check(rc == 0 and res["status"] == "LEAN_PROOF_KERNEL_VERIFIED", "check-proof accepts the synthetic termination proof")
rc, res = submit(T[UE], "wf_edivr_unfold.lean")
check(rc == 0 and res["status"] == "LEAN_PROOF_KERNEL_VERIFIED", "check-proof accepts the synthetic unfolding-equation proof")
rc, out = cli("assemble", "--run", RUN)
asm = latest_assembly()
A = {r["source"]: r for r in json.loads((Path(asm["assembly_dir"]) / "assembly_report.json").read_text())["results"]} if asm else {}
OUT["assembly"] = {"exit": rc, "status": asm and asm["status"], "summary": asm and asm["summary"],
                   "axioms_by_target": asm and asm["axioms_by_target"],
                   "rows": {n: {k: r.get(k) for k in ("status", "target", "assembly", "proof_state", "proof_target", "assembly_note")}
                            for n, r in sorted(A.items())}}
check(rc == 0 and asm and asm["status"] == "ASSEMBLY_VALIDATED", "assembly: ASSEMBLY_VALIDATED (consumer and audit)")
st = lambda n: (A[n]["assembly"], A[n].get("proof_state"))
check(st(TE) == ("VALIDATED", "PROOF_ASSEMBLED") and A[TE]["proof_target"] == f"Rocq.{TE}",
      "the termination obligation gets its final theorem")
check(A["SF.Wf.edivr"]["assembly"] == "ASSEMBLED" and A["SF.Wf.edivr"]["target"] == "Rocq.SF.Wf.edivr"
      and all(A[n]["assembly"] == "ASSEMBLED" for n in ("SF.Wf.divr", "SF.Wf.T3", "SF.Wf.divr_le", "SF.Wf.divr_7_2")),
      "edivr and its dependents are assembled as Rocq.* (the lowering uses the final theorem)")
check(st(UE) == ("ASSEMBLED", "PROOF_ASSEMBLED"), "the unfolding equation: final statement, generalized proof reused")
check(A["SF.Wf.modr"]["assembly"] == "PENDING" and A[TM].get("proof_state") == "PROOF_NOT_SUPPLIED"
      and A[UM]["assembly"] == "PENDING", "modr (no termination proof supplied) and its equation stay pending")
check(A["SF.Wf.t3"]["assembly"] == "NOT_TRANSLATED", "t3 stays not translated")

# 6. computation, measured separately
lean_dir = Path(asm["assembly_dir"]) / "lean"
lp = subprocess.run(["lake", "-d", str(ROOT), "env", "printenv", "LEAN_PATH"], capture_output=True, text=True).stdout.strip()
env = {"LEAN_PATH": ":".join([lp, str(RUN / "lean"), str(Path(asm["assembly_dir"]) / "templates"), str(lean_dir)]),
       "PATH": "/usr/bin:/bin"}
probes = {
    # definitional reduction, by the elaborator (does not unfold theorem proofs) and by the kernel
    "definitional_reduction_elaborator_rfl": "theorem probe : Rocq.SF.Wf.divr 7 2 = 3 := rfl\n",
    "definitional_reduction_kernel_decide": "theorem probe : Rocq.SF.Wf.divr 7 2 = 3 := by decide +kernel\n",
    # the conversion-dependent definition t3 : T3 := 0, added directly through the kernel after assembly
    # (a measurement only: assembly does not re-attempt it; the result depends on the supplied
    # termination proof reducing, i.e. proof-dependent computation)
    "definitional_reduction_kernel_t3": (
        "open Lean Elab Command in\n#eval show CommandElabM Unit from do\n"
        "  let r ← liftCoreM <| try\n"
        "      addDecl (.defnDecl { name := `t3k, levelParams := [], type := mkConst ``Rocq.SF.Wf.T3, value := mkConst ``Nat.zero,\n"
        "                           hints := .abbrev, safety := .safe, all := [`t3k] })\n"
        "      pure \"KERNEL_ACCEPTED\"\n"
        "    catch e => do pure s!\"KERNEL_REJECTED {← e.toMessageData.toString}\"\n"
        "  if r != \"KERNEL_ACCEPTED\" then throwError r\n  logInfo r\n"),
    # the unfolding equation's final theorem, instantiated step by step (each step's right side is the
    # next call, by evaluating the structural `sub` on numerals); a fixture proof, tests only
    "propositional_equation": (
        "theorem probe : Rocq.SF.Wf.divr 7 2 = 3 := by\n"
        "  have h1 : Rocq.SF.Wf.edivr 1 7 0 = Rocq.SF.Wf.edivr 1 5 1 := Rocq.SF.Wf.edivr__rocq2lean_unfold_1 1 7 0\n"
        "  have h2 : Rocq.SF.Wf.edivr 1 5 1 = Rocq.SF.Wf.edivr 1 3 2 := Rocq.SF.Wf.edivr__rocq2lean_unfold_1 1 5 1\n"
        "  have h3 : Rocq.SF.Wf.edivr 1 3 2 = Rocq.SF.Wf.edivr 1 1 3 := Rocq.SF.Wf.edivr__rocq2lean_unfold_1 1 3 2\n"
        "  have h4 : Rocq.SF.Wf.edivr 1 1 3 = Rocq.Corelib.Init.Datatypes.prod.pair Nat Nat 3 1 := "
        "Rocq.SF.Wf.edivr__rocq2lean_unfold_1 1 1 3\n"
        "  show Rocq.Corelib.Init.Datatypes.fst Nat Nat (Rocq.SF.Wf.edivr (Rocq.Corelib.Init.Nat.pred 2) 7 0) = 3\n"
        "  rw [show Rocq.Corelib.Init.Nat.pred 2 = 1 from rfl, h1, h2, h3, h4]; rfl\n"),
    "compiled_evaluation": "#eval Rocq.SF.Wf.divr 7 2\n",
}
OUT["computation"] = {}
for k, body in probes.items():
    f = lean_dir / f"Probe_{k}.lean"
    f.write_text("import Rocq2LeanAssembled\n" + body)
    p = subprocess.run([str(Path.home() / ".elan/bin/lean"), str(f)], capture_output=True, text=True, cwd=lean_dir, env=env,
                       timeout=600)
    OUT["computation"][k] = {"exit": p.returncode, "output": (p.stdout + p.stderr).strip()[:800]}
C = {k: x["exit"] == 0 for k, x in OUT["computation"].items()}
check(C["propositional_equation"], "propositional unfolding equation: divr 7 2 = 3 follows from the assembled equation")
check(C["definitional_reduction_kernel_decide"] and not C["definitional_reduction_elaborator_rfl"],
      "definitional reduction: the kernel reduces divr 7 2 to 3 through the supplied (closed) termination proof; "
      "the elaborator's rfl does not (it does not unfold theorems)")
check(C["definitional_reduction_kernel_t3"], "after assembly the kernel accepts t3 : T3 := 0 (measured, not assembled)")
check(not C["compiled_evaluation"] and "LCNF" in OUT["computation"]["compiled_evaluation"]["output"],
      "compiled evaluation is unsupported (no code generated for kernel-added declarations): reported, not a kernel failure")
OUT["computation_summary"] = {k: ("OK" if x["exit"] == 0 else "FAILS") for k, x in OUT["computation"].items()}

(ROOT / "reports" / "statement_only").mkdir(parents=True, exist_ok=True)
(ROOT / "reports" / "statement_only" / "test_termination.json").write_text(json.dumps(OUT, indent=1) + "\n")
finish("test-termination")

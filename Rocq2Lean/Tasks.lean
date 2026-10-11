import Lean
import Rocq2Lean.Replay

/-!
# Proof-task interface (statement mode, docs/STATEMENT_ONLY_DESIGN.md §9)

Rocq2Lean never proves anything. These commands only *state* tasks and *check* proofs that a
separate proving agent submits.

* `#rocq2lean_render_tasks "in.json" "out.json"` — for each task (a proof-task statement constant of
  a validated statement library and the number of its prerequisite hypotheses) the Lean statement
  the agent must prove, as an expression and pretty-printed:
  - a task without prerequisites: `Rocq.c.statement` (or `Rocq.c.type` for opaque data);
  - a task with prerequisites `h₁ … hₖ`: `∀ h₁ … hₖ, RocqPending.c.statement h₁ … hₖ`. The proof is
    generic in the prerequisites: a proof hypothesis is irrelevant, and Rocq never unfolds opaque
    data, so the generalized statement is exactly what Rocq's proof establishes.

* `#rocq2lean_check_proof "task.json" "out.json"` — run in a fresh module that imports the statement
  library and the agent's proof module: the reserved constant exists, is not unsafe or an axiom, a
  proof task's constant is a `theorem`, its type is *syntactically* the task statement at the task's
  universe parameters, and its axioms (`collectAxioms`) are within the declared allowance; `sorryAx`
  is always refused.
-/

namespace Rocq2Lean

open Lean Elab Command Meta

/-- The statement a task asks for: the statement constant at its own universe parameters, generalized
over its first `nh` hypotheses (pending prerequisites). -/
def taskStatement (stmt : Name) (nh : Nat) : MetaM (List Name × Expr) := do
  let ci ← getConstInfo stmt
  let lps := ci.levelParams
  let c := mkConst stmt (lps.map Level.param)
  if nh == 0 then return (lps, c)
  let e ← forallBoundedTelescope ci.type (some nh) fun hs _ => do
    unless hs.size == nh do throwError "{stmt}: fewer than {nh} prerequisite binders"
    mkForallFVars hs (mkAppN c hs)
  return (lps, e)

syntax (name := rocqRenderTasks) "#rocq2lean_render_tasks " str str : command

@[command_elab rocqRenderTasks] def elabRenderTasks : CommandElab := fun stx => do
  let some inP := stx[1].isStrLit? | throwError "expected an input path"
  let some outP := stx[2].isStrLit? | throwError "expected an output path"
  let tasks ← IO.ofExcept ((← IO.ofExcept (Json.parse (← IO.FS.readFile inP))).getArr?)
  let out ← liftTermElabM do
    let mut out : Array Json := #[]
    for t in tasks do
      let stmt := ((t.getObjValAs? String "statement_constant").toOption.getD "").toName
      let nh := (t.getObjValAs? Nat "hypotheses").toOption.getD 0
      let (lps, e) ← taskStatement stmt nh
      let ci ← getConstInfo stmt
      let body ← match ci.value? with
        | some v => do
          let b ← lambdaBoundedTelescope v nh fun _ b => pure b
          pure (toString (← withOptions (fun o => o.setBool `pp.fullNames true) (ppExpr b)))
        | none => pure ""
      out := out.push (Json.mkObj [
        ("statement_constant", stmt.toString), ("level_params", Json.arr (lps.map (Json.str ·.toString)).toArray),
        ("task_type", exprJson e),
        ("task_type_pp", toString (← withOptions (fun o => o.setBool `pp.fullNames true) (ppExpr e))),
        ("statement_pp", body)])
    return out
  IO.FS.writeFile outP ((Json.arr out).compress ++ "\n")

syntax (name := rocqCheckProof) "#rocq2lean_check_proof " str str : command

@[command_elab rocqCheckProof] def elabCheckProof : CommandElab := fun stx => do
  let some taskP := stx[1].isStrLit? | throwError "expected a task path"
  let some outP := stx[2].isStrLit? | throwError "expected an output path"
  let task ← IO.ofExcept (Json.parse (← IO.FS.readFile taskP))
  let get (k : String) : String := (task.getObjValAs? String k).toOption.getD ""
  let thm := (get "reserved_name").toName
  let stmt := (get "statement_constant").toName
  let nh := (task.getObjValAs? Nat "hypotheses").toOption.getD 0
  let isProofTask := get "kind" != "opaque_value"
  let allowed := ((task.getObjValAs? (Array String) "allowed_axioms").toOption.getD #[]).map String.toName
  let mut problems : Array String := #[]
  let mut axs : Array Name := #[]
  match (← getEnv).find? thm with
  | none => problems := problems.push s!"{thm} is not declared by the submitted module"
  | some ci =>
    if ci.isUnsafe || ci.isPartial then problems := problems.push s!"{thm} is unsafe or partial"
    match ci with
    | .axiomInfo _ => problems := problems.push s!"{thm} is an axiom"
    | .thmInfo _ => pure ()
    | .defnInfo _ | .opaqueInfo _ =>
      if isProofTask then problems := problems.push s!"{thm} must be a theorem"
    | _ => problems := problems.push s!"{thm} is not a theorem or definition"
    let (lps, want) ← liftTermElabM (taskStatement stmt nh)
    if ci.levelParams != lps then
      problems := problems.push s!"{thm}: universe parameters {ci.levelParams} differ from the task's {lps}"
    else if ci.type != want then
      problems := problems.push s!"{thm}: its type is not syntactically the task statement"
    axs ← liftCoreM (collectAxioms thm)
    if axs.contains ``sorryAx then problems := problems.push s!"{thm} depends on sorryAx"
    for a in axs do
      unless a == ``sorryAx || allowed.contains a do
        problems := problems.push s!"{thm} depends on the axiom {a}, outside the allowance {allowed}"
  let res := Json.mkObj [
    ("schema", "rocq2lean-check-proof/1"), ("task_id", get "task_id"), ("reserved_name", thm.toString),
    ("status", if problems.isEmpty then "LEAN_PROOF_KERNEL_VERIFIED" else "PROOF_REJECTED"),
    ("axioms", Json.arr (axs.map (Json.str ·.toString))), ("problems", Json.arr (problems.map Json.str))]
  IO.FS.writeFile outP (res.pretty ++ "\n")
  unless problems.isEmpty do
    throwError "PROOF_REJECTED: {problems}"

end Rocq2Lean

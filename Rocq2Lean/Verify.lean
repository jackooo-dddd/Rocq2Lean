import Lean
import Rocq2Lean.Emit

/-!
# `#rocq2lean_verify`

Run in a *separate* module that imports the generated one. For every declaration the report
lists as `TRANSLATED_AND_CHECKED` it re-checks, against the imported environment:

* the target exists and has the recorded declaration kind;
* its type and value are exactly the ones recorded in the report;
* its transitive axiom set (`collectAxioms`) is empty — the pilot's success profile admits no
  axioms at all, so even standard Lean axioms are reported.

It also requires every requested root to be `TRANSLATED_AND_CHECKED`. Any failure fails the
consumer module.
-/

namespace Rocq2Lean

open Lean Elab Command Meta

syntax (name := rocqVerify) "#rocq2lean_verify " str : command

private def kindOf : ConstantInfo → String
  | .defnInfo _ => "def"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"
  | .axiomInfo _ => "axiom"
  | .quotInfo _ => "quot"

@[command_elab rocqVerify] def elabRocqVerify : CommandElab := fun stx => do
  let some repPath := stx[1].isStrLit? | throwError "expected a report path"
  let report ← IO.ofExcept (Json.parse (← IO.FS.readFile repPath))
  let results ← IO.ofExcept (report.getObjValAs? (Array Json) "results")
  let roots ← IO.ofExcept (report.getObjValAs? (Array Json) "roots")
  let mut problems : Array String := #[]
  for r in roots do
    let st := (r.getObjValAs? String "status").toOption.getD "?"
    if st != "TRANSLATED_AND_CHECKED" then
      problems := problems.push s!"root {(r.getObjValAs? String "name").toOption.getD "?"} has status {st}"
  let mut checked : Nat := 0
  for r in results do
    unless (r.getObjValAs? String "status").toOption == some "TRANSLATED_AND_CHECKED" do continue
    let some tgt := (r.getObjValAs? String "target").toOption | problems := problems.push "result without target"; continue
    let name := tgt.toName
    let some ci := (← getEnv).find? name
      | problems := problems.push s!"{tgt}: not present in the imported environment"; continue
    let kind := (r.getObjValAs? String "target_kind").toOption.getD ""
    if kindOf ci != kind then problems := problems.push s!"{tgt}: kind {kindOf ci}, report says {kind}"
    if (r.getObjValD "target_type") != exprJson ci.type then
      problems := problems.push s!"{tgt}: imported type differs from the reported type"
    match ci.value? (allowOpaque := true) with
    | some v =>
      if (r.getObjValD "target_value") != exprJson v then
        problems := problems.push s!"{tgt}: imported value differs from the reported value"
    | none => problems := problems.push s!"{tgt}: imported declaration has no value"
    let axs ← liftCoreM (collectAxioms name)
    unless axs.isEmpty do problems := problems.push s!"{tgt}: depends on axioms {axs}"
    checked := checked + 1
  unless problems.isEmpty do
    throwError "AUDIT_REJECTED (consumer):\n{String.intercalate "\n" problems.toList}"
  logInfo m!"rocq2lean verify: {checked} imported declaration(s) match the report; no axioms"

end Rocq2Lean

import Lean

/-!
# Checked kernel insertion

Every declaration the translator produces goes through `addChecked`, which calls the Lean
kernel's type checker synchronously (`Environment.addDeclCore` with `doCheck := true`, i.e.
`lean_add_decl`). It refuses to run when `debug.skipKernelTC` is set, and it never uses
`addDeclWithoutChecking`.
-/

open Lean

namespace Rocq2Lean

/-- Outcome of submitting one declaration to the Lean kernel. -/
inductive KernelResult where
  | accepted
  | rejected (msg : String)
  deriving Repr, Inhabited

/-- Submit `decl` to the Lean kernel and, if it is accepted, install the extended environment. -/
def addChecked (decl : Declaration) : CoreM KernelResult := do
  let opts ← getOptions
  if debug.skipKernelTC.get opts then
    throwError "rocq2lean: refusing to add declarations while debug.skipKernelTC is enabled"
  let env ← getEnv
  match env.addDeclCore (Core.getMaxHeartbeats opts).toUSize (maxRecDepth.get opts).toUSize decl
      none (doCheck := true) with
  | .ok env' =>
    setEnv env'
    return .accepted
  | .error ex =>
    return .rejected (← (ex.toMessageData opts).toString)

/-- Submit `decl` to the Lean kernel *without* installing it: used to validate a side condition
(e.g. that a declaration is well typed for every value of a defaulted universe level). -/
def checkOnly (decl : Declaration) : CoreM KernelResult := do
  let opts ← getOptions
  if debug.skipKernelTC.get opts then
    throwError "rocq2lean: refusing to check declarations while debug.skipKernelTC is enabled"
  match (← getEnv).addDeclCore (Core.getMaxHeartbeats opts).toUSize (maxRecDepth.get opts).toUSize decl
      none (doCheck := true) with
  | .ok _ => return .accepted
  | .error ex => return .rejected (← (ex.toMessageData opts).toString)

end Rocq2Lean

import Rocq2Lean.Kernel

/-! Phase 0: the production insertion path accepts a valid proof and rejects `Nat.zero : False`. -/

open Lean Elab Command Rocq2Lean

elab "#smoke_kernel_path" : command => liftCoreM do
  let thm (n : Name) (ty val : Expr) : Declaration :=
    .thmDecl { name := n, levelParams := [], type := ty, value := val, all := [n] }
  let good ← addChecked (thm `Smoke.trueIntro (mkConst ``True) (mkConst ``True.intro))
  let bad ← addChecked (thm `Smoke.zeroIsFalse (mkConst ``False) (mkConst ``Nat.zero))
  match good, bad with
  | .accepted, .rejected msg =>
    unless (← getEnv).contains `Smoke.trueIntro && !(← getEnv).contains `Smoke.zeroIsFalse do
      throwError "SMOKE_FAIL: environment contents do not match kernel results"
    logInfo m!"SMOKE_KERNEL_PATH_OK: valid accepted; invalid rejected with: {msg}"
  | g, b => throwError "SMOKE_FAIL: good={repr g} bad={repr b}"

#smoke_kernel_path

-- The accepted declaration is a real environment constant usable by later code.
example : True := Smoke.trueIntro

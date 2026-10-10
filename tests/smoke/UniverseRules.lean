import Rocq2Lean.Translate
import Rocq2Lean.Emit
open Lean Rocq2Lean

-- Unit checks of rule R3 (docs/UNIVERSE_TRANSLATION.md) on a small fact table: Set < a, Set < b, a ≤ b.
private def F : IR.UniverseFacts :=
  { levels := #["a", "b", "c"],
    relations := #[("Set", "lt", "a"), ("Set", "lt", "b"), ("Set", "lt", "c"), ("a", "le", "b"), ("b", "lt", "c"), ("a", "lt", "c")] }
private def ok (own : Array String) (l : String) (σ : Level) : Bool := (checkInstantiation F own l σ).toBool
private def u (s : String) : Level := .param (levelParamName s)

#guard ok #["a"] "b" (u "a")                         -- a ≤ b: lower level allowed
#guard !ok #["b"] "a" (u "b")                        -- b ≤ a not entailed
#guard ok #["b"] "b" (u "b")                         -- shared level: identity
#guard !ok #["a", "b"] "b" (u "a")                   -- shared level must be identity even if a ≤ b
#guard ok #[] "b" .zero                              -- Set ≤ b
#guard ok #[] "b" (.succ .zero)                      -- Set + 1 ≤ b (Set < b)
#guard !ok #[] "b" (.succ (.succ .zero))             -- Set + 2 ≤ b not entailed
#guard ok #["a"] "c" (.succ (u "a"))                 -- a + 1 ≤ c (a < c)
#guard !ok #["a"] "b" (.succ (u "a"))                -- a + 1 ≤ b not entailed (only a ≤ b)
#guard ok #["a"] "b" (.max (u "a") (u "a"))          -- normalization: max a a = a
#guard ok #["a"] "b" (.max .zero (u "a"))            -- normalization: max 0 a = a
#guard !ok #["a"] "b" (.param `u_unrelated)          -- foreign parameter

-- Justification of defaulted (residual) levels: accepted only if the declaration is kernel-valid
-- with the residual as a fresh universe parameter (here: `Prop : Sort (r+1)` holds only for r = 0).
open Meta in
run_meta do
  let r := Level.param `u_residual_0
  let bad ← justifyResiduals `rules_resid_bad "def" [] [`u_residual_0] (.sort (.succ r)) (.sort .zero)
  unless bad.isSome do throwError "an unjustified default was accepted"
  let good ← justifyResiduals `rules_resid_good "def" [] [`u_residual_0] (.sort (.succ r)) (.sort r)
  unless good.isNone do throwError "a level-irrelevant default was rejected: {good}"
  let none' ← justifyResiduals `rules_resid_none "def" [] [] (.sort (.succ .zero)) (.sort .zero)
  unless none'.isNone do throwError "no residual: nothing to justify"

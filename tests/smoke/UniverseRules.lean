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

-- Rule R (docs/COHERENCE_READINGS.md): for a shared level b, max(u_b, s…) with every other summand
-- passing R3 is b's R2F reading (equal to b at every model of the facts); nothing else is accepted.
#guard ok #["a", "b"] "b" (.max (u "b") (u "a"))     -- a ≤ b: the reading max(u_b, u_a)
#guard ok #["a", "b"] "b" (.max (u "a") (u "b"))     -- (summand order is irrelevant)
#guard ok #["b"] "b" (.max (u "b") (.succ .zero))    -- Set + 1 ≤ b (Set < b)
#guard !ok #["b", "c"] "b" (.max (u "b") (u "c"))    -- c ≤ b not entailed: raising, rejected
#guard !ok #["a", "b"] "b" (.max (u "b") (.succ (u "a")))  -- a + 1 ≤ b not entailed
#guard !ok #["b"] "b" (.max (u "b") (.succ (.succ .zero)))  -- Set + 2 ≤ b not entailed
#guard !ok #["a", "b"] "b" (.max (.succ (u "b")) (u "a"))   -- u_b + 1 is not a reading of b
#guard !ok #["a", "b", "c"] "c" (.max (u "a") (u "b"))      -- no u_c summand: a specialization of c
-- Rule R as equality at every model of the facts (`equalAtModels`, docs/COHERENCE_READINGS.md §6)
#guard equalAtModels F #["a", "b"] (.max (u "b") (u "a")) (u "b")        -- a ≤ b: max (b, a) = b
#guard !equalAtModels F #["a", "b"] (u "a") (u "b")                      -- a alone is below b
#guard !equalAtModels F #["b", "c"] (.max (u "b") (u "c")) (u "b")       -- c is above b
#guard equalAtModels F #["a", "c"] (.max (u "c") (.succ (u "a"))) (u "c") -- a + 1 ≤ c (a < c)
#guard !equalAtModels F #["a"] (.param `u_foreign) (u "a")               -- a foreign parameter
#guard !(checkInstantiation F #["a", "b"] "b" (.max (u "b") (u "a")) {} true).toBool
                                                     -- motive-level (R8) parameter: expects u_b + 1
#guard !(checkInstantiation F #["a", "b"] "b" (.max (u "b") (u "a")) (({} : Std.HashMap String Level).insert "b" (u "a"))).toBool
                                                     -- proof-local level: the argument is its solution

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

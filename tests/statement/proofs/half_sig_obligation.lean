import Rocq2LeanOut
-- the extracted obligation of half_sig (0 ≤ n, Rocq's `le`); `propext` is used on purpose, so that
-- assembly must report it in the axioms of the definitions whose proof fields contain this proof
theorem RocqProofTemplates.T@TASK@.proof : Rocq.SF.Asm.half_sig__rocq2lean_obligation_1.statement := by
  have _h : True = True := propext (Iff.refl True)
  intro n
  induction n with
  | zero => exact Rocq.Corelib.Init.Peano.le.le_n Nat.zero
  | succ m ih => exact Rocq.Corelib.Init.Peano.le.le_S Nat.zero m ih

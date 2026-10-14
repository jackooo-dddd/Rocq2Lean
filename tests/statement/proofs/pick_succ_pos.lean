import Rocq2LeanOut
-- A′: `pick` is an opaque constant (its body is not unfolded); the statement has no prerequisite
theorem RocqProofTemplates.T@TASK@.proof : Rocq.SF.Asm.pick_succ_pos.statement := by
  unfold Rocq.SF.Asm.pick_succ_pos.statement
  show Rocq.Corelib.Init.Peano.le (Nat.succ Nat.zero) (Nat.succ Rocq.SF.Asm.pick)
  generalize Rocq.SF.Asm.pick = p
  induction p with
  | zero => exact Rocq.Corelib.Init.Peano.le.le_n _
  | succ m ih => exact Rocq.Corelib.Init.Peano.le.le_S _ _ ih

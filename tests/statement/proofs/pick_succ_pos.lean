import Rocq2LeanOut
-- generalized over the opaque value `pick` (data): accepted by check-proof, never assembled until the
-- value is bound (A′)
theorem RocqProofTemplates.T@TASK@.proof :
    ∀ p, @RocqPending.SF.Asm.pick_succ_pos.statement p := by
  intro p
  unfold RocqPending.SF.Asm.pick_succ_pos.statement
  show Rocq.Corelib.Init.Peano.le (Nat.succ Nat.zero) (Nat.succ p)
  induction p with
  | zero => exact Rocq.Corelib.Init.Peano.le.le_n _
  | succ m ih => exact Rocq.Corelib.Init.Peano.le.le_S _ _ ih

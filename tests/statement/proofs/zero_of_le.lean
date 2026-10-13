import Rocq2LeanOut
-- generalized over the obligation (a proposition)
theorem RocqProofTemplates.T@TASK@.proof :
    ∀ h, @RocqPending.SF.Asm.zero_of_le.statement h := by
  intro h
  unfold RocqPending.SF.Asm.zero_of_le.statement
  intro n
  exact h n

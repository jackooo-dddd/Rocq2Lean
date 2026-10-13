import Rocq2LeanOut
-- generalized over the obligation; about the pending inductive RocqPending.SF.Asm.is_zero_of
theorem RocqProofTemplates.T@TASK@.proof :
    ∀ h, @RocqPending.SF.Asm.is_zero_of_intro.statement h :=
  fun h n => @RocqPending.SF.Asm.is_zero_of.izo h n

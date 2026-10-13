import Rocq2LeanOut
-- synthetic fixture (fixtures/stmt/wf): the termination obligation of SF.Wf.edivr's lowering
theorem RocqProofTemplates.T@TASK@.sub_le : ∀ s d, Rocq.SF.Wf.sub s d ≤ s := by
  intro s
  induction s with
  | zero => intro d; exact Nat.le_refl _
  | succ m ih =>
    intro d
    cases d with
    | zero => exact Nat.le_refl _
    | succ n => exact Nat.le_succ_of_le (ih n)

theorem RocqProofTemplates.T@TASK@.proof : Rocq.SF.Wf.edivr__rocq2lean_termination_1.statement := by
  unfold Rocq.SF.Wf.edivr__rocq2lean_termination_1.statement
  intro d s
  refine Subrelation.accessible (r := (· < ·)) ?_ (Nat.lt_wfRel.wf.apply s)
  intro y s' hR
  obtain ⟨q, n, h, rfl⟩ := hR
  have := RocqProofTemplates.T@TASK@.sub_le s' d
  rw [h] at this
  exact this

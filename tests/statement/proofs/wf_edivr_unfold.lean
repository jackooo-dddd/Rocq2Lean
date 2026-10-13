import Rocq2LeanOut
-- synthetic fixture (fixtures/stmt/wf): the unfolding equation of SF.Wf.edivr, generalized over its
-- termination obligation (a proposition: any two proofs are definitionally equal)
theorem RocqProofTemplates.T@TASK@.convoy {P : Type} (x : Nat) (b0 : P) (G : Nat → P) :
    Nat.rec (motive := fun t => x = t → P) (fun _ => b0) (fun n _ _ => G n) x rfl =
      Nat.rec (motive := fun _ => P) b0 (fun n _ => G n) x := by
  cases x <;> rfl

theorem RocqProofTemplates.T@TASK@.proof : ∀ h, @RocqPending.SF.Wf.edivr__rocq2lean_unfold_1.statement h := by
  intro h
  unfold RocqPending.SF.Wf.edivr__rocq2lean_unfold_1.statement
  intro d m q
  have e := RocqProofTemplates.T@TASK@.convoy (Rocq.SF.Wf.sub m d) (Rocq.Corelib.Init.Datatypes.prod.pair Nat Nat q m)
    (fun n => @RocqPending.SF.Wf.edivr h d n q.succ)
  unfold RocqPending.SF.Wf.edivr
  generalize h d m = a
  cases a with
  | intro x k => exact e

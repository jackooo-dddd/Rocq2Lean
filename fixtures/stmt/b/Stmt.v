(* Statement-only fixture, variant B: the statements and definitions of ../a/Stmt.v with different
   proofs (an irrelevant source proof change: closure, IR records and propositions must not change). *)
Definition double (n : nat) : nat := n + n.
Lemma double_succ : forall n, double (S n) = S (S (double n)).
Proof.
  intro n. unfold double. simpl. f_equal. symmetry. exact (plus_n_Sm n n).
Qed.
Inductive even : nat -> Prop :=
| even0 : even 0
| evenSS : forall n, even n -> even (S (S n)).
Lemma double_even : forall n, even (double n).
Proof.
  intro n. induction n as [|n IH]; [exact even0|].
  replace (double (S n)) with (S (S (double n))) by (symmetry; apply double_succ).
  apply evenSS; assumption.
Qed.
Definition half_sig (n : nat) : {m : nat | m <= n} :=
  exist (fun m => m <= n) 0 ltac:(apply le_0_n).
Definition zero_of (n : nat) : nat := proj1_sig (half_sig n).
Lemma zero_of_le : forall n, zero_of n <= n.
Proof. intro n. exact (proj2_sig (half_sig n)). Qed.
Lemma le_trans_alt : forall a b c, a <= b -> b <= c -> a <= c.
Proof. intros a b c H1 H2. revert H1. induction H2; intro H; [assumption | apply le_S; apply IHle; assumption]. Qed.

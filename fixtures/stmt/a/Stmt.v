(* Statement-only fixture, variant A: proofs written one way. Variant B (../b/Stmt.v) has the same
   statements and definitions with different proofs, including the inline proof in half_sig. *)
Definition double (n : nat) : nat := n + n.
Lemma double_succ : forall n, double (S n) = S (S (double n)).
Proof. intro n. unfold double. simpl. rewrite <- plus_n_Sm. reflexivity. Qed.
Inductive even : nat -> Prop :=
| even0 : even 0
| evenSS : forall n, even n -> even (S (S n)).
Lemma double_even : forall n, even (double n).
Proof. induction n as [|n IH]. - constructor. - rewrite double_succ. constructor. exact IH. Qed.
Definition half_sig (n : nat) : {m : nat | m <= n} :=
  exist (fun m => m <= n) 0 ltac:(induction n; constructor; assumption).
Definition zero_of (n : nat) : nat := proj1_sig (half_sig n).
Lemma zero_of_le : forall n, zero_of n <= n.
Proof. intro n. unfold zero_of. destruct (half_sig n) as [m H]. exact H. Qed.
Lemma le_trans_alt : forall a b c, a <= b -> b <= c -> a <= c.
Proof. intros a b c H1 H2. induction H2; [exact H1 | constructor; exact IHle]. Qed.

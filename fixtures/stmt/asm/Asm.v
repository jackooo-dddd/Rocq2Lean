(* Synthetic assembly fixture (docs/ASSEMBLY.md; tests/statement/check_assembly.py). Not Prosa: every
   case of pending-to-final assembly, once each.
   - double_zero:        a theorem statement without prerequisites;
   - half_sig:           a definition with an extracted proof obligation (pending on it);
   - zero_of:            a definition pending through half_sig;
   - zero_of_le:         a statement pending on the obligation (its task is generalized over it);
   - is_zero_of:         a pending inductive (its constructor mentions zero_of);
   - is_zero_of_intro:   a statement about the pending inductive: its generalized proof is about
                         RocqPending.is_zero_of, which is a different type from the re-emitted
                         Rocq.is_zero_of (the assembly boundary);
   - pick:               opaque data of a type with many values (nat);
   - pick_succ:          a definition pending on that opaque value;
   - pick_succ_pos:      a statement pending on it. *)
Definition double (n : nat) : nat := n + n.
Lemma double_zero : double 0 = 0.
Proof. reflexivity. Qed.
Definition half_sig (n : nat) : {m : nat | m <= n} :=
  exist (fun m => m <= n) 0 ltac:(induction n; constructor; assumption).
Definition zero_of (n : nat) : nat := proj1_sig (half_sig n).
Lemma zero_of_le : forall n, zero_of n <= n.
Proof. intro n. unfold zero_of. destruct (half_sig n) as [m H]. exact H. Qed.
Inductive is_zero_of : nat -> nat -> Prop :=
| izo : forall n, is_zero_of n (zero_of n).
Lemma is_zero_of_intro : forall n, is_zero_of n (zero_of n).
Proof. exact izo. Qed.
Definition pick : nat.
Proof. exact 3. Qed.
Definition pick_succ : nat := S pick.
Lemma pick_succ_pos : 0 < pick_succ.
Proof. unfold pick_succ, lt. apply le_n_S. apply le_0_n. Qed.

(* M6 fixture: inductives with a non-uniform parameter (the recursive occurrence changes it), as
   MathComp's ssrnat.acc_nat. Lean has no non-uniform parameters: the parameter becomes an index, and
   Rocq's matches (which bind it as a parameter) are lowered with a convoy equation. *)

(* Type-valued: matches whose return type mentions the parameter. *)
Inductive countdown (n : nat) : Type :=
| cd_stop : countdown n
| cd_step : countdown (S n) -> countdown n.

Definition cd_is_stop (n : nat) (c : countdown n) : bool :=
  match c with cd_stop _ => true | cd_step _ _ => false end.

Definition cd_tail (n : nat) (c : countdown n) : option (countdown (S n)) :=
  match c with cd_stop _ => None | cd_step _ c' => Some c' end.

Definition cd_example : countdown 3 := cd_step 3 (cd_stop 4).

Lemma cd_is_stop_ex : cd_is_stop 3 cd_example = false.
Proof. reflexivity. Qed.

Lemma cd_tail_ex : cd_tail 3 cd_example = Some (cd_stop 4).
Proof. reflexivity. Qed.

(* Prop-valued, acc_nat-like: inversion with an impossible branch. *)
Inductive accb (P : nat -> bool) (i : nat) : Prop :=
| AccB0 : P i = true -> accb P i
| AccBS : accb P (S i) -> accb P i.

Lemma accb_inv (P : nat -> bool) (m : nat) : accb P m -> P m = false -> accb P (S m).
Proof.
  intros h H. destruct h as [e | a].
  - rewrite H in e. discriminate.
  - exact a.
Qed.

Lemma accb_start (P : nat -> bool) : P 2 = true -> accb P 0.
Proof. intro e. apply AccBS, AccBS, AccB0, e. Qed.

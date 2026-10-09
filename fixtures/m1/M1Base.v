(* M1 fixtures: declaration kinds, Section discharge, a simple inductive. *)
Definition two : nat := S (S O).
Definition two_eq : two = S (S O) := eq_refl.                (* transparent, proof-valued *)
Lemma two_eq_qed : two = S (S O). Proof. reflexivity. Qed.    (* opaque, proof-valued *)
Definition three_opaque : nat. Proof. exact (S two). Qed.     (* opaque, data-valued *)
Lemma two_refl_defined : two = two. Proof. reflexivity. Defined.
Definition let_test : nat := let x := two in S x.

Section Sec.
  Variable n : nat.
  Definition add_two := S (S n).
  Lemma add_two_eq : add_two = S (S n). Proof. reflexivity. Qed.
End Sec.

Inductive Color : Set := Red | Green.

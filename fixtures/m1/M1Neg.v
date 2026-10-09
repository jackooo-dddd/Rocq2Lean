(* Negative M1 inputs: a genuine assumption and relaxed source checking. *)
From M1 Require Import M1Base.
Axiom ax : two = two.
Lemma uses_ax : two = two. Proof. exact ax. Qed.
#[bypass_check(universes)] Definition relaxed : nat := two.
Lemma uses_relaxed : relaxed = two. Proof. reflexivity. Qed.

(* Lowering-audit fixture: a fixpoint with two same-typed trailing arguments. *)
From M3 Require Import M3Types.
Fixpoint swapacc (n : RNat) (a b : RNat) {struct n} : RNat :=
  match n with RZ => a | RS p => swapacc p b a end.
Lemma swapacc_RS : forall n a b, swapacc (RS n) a b = swapacc n b a. Proof. reflexivity. Qed.

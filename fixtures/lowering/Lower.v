(* Lowering-audit fixture: a fixpoint with two same-typed trailing arguments. *)
From M3 Require Import M3Types.
Fixpoint swapacc (n : RNat) (a b : RNat) {struct n} : RNat :=
  match n with RZ => a | RS p => swapacc p b a end.
Lemma swapacc_RS : forall n a b, swapacc (RS n) a b = swapacc n b a. Proof. reflexivity. Qed.
(* Two nullary constructors with same-typed branches: swapping the minor premises is type-correct. *)
Inductive B2 : Set := T2 | F2.
Definition neg2 (b : B2) : B2 := match b with T2 => F2 | F2 => T2 end.
Lemma neg2_T2 : neg2 T2 = F2. Proof. reflexivity. Qed.

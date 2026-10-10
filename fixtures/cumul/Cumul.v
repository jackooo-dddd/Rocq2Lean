(* Controls for the cumulativity tier (docs/UNIVERSE_TRANSLATION.md).

   R2B-P negative control: the proof-local level m's fact Set < m is required by this declaration's
   OWN typing (Prop : Type@{m}), not by an outside declaration. Lean types Prop at Sort 1 and solves
   m := 0, but the Rocq instance m := Set is ill-typed: the rule's source obligation must fail. *)
Universe m.
Definition prop_in_m : nat := let _ : Type@{m} := Prop in 0.

(* R2B-P positive control: Set < n is imposed by ANOTHER declaration (prop_in_n below); this
   declaration only uses n as a let-bound sort, like Program's `let U := Type in` obligations. *)
Universe n.
Definition uses_n : nat := let U : Type@{n+1} := Type@{n} in let _ : U := nat in 0.
Definition prop_in_n : Type@{n+1} := Type@{n} -> Prop.
Definition force_n : nat := let _ : Type@{n} := Prop in 0.

(* R3-up positive: a reference to wrap's result level b used at the referrer's own level c by upward
   cumulativity (b <= c), like MathComp Monoid.isLaw.phant_axioms. *)
Universe a b c.
Constraint a <= b.
Constraint b <= c.
Inductive wrap (A : Type@{a}) : Type@{b} := mk : A -> wrap A.
Definition up (A : Type@{a}) : Type@{c} := wrap A.
Definition up_nat : Type@{c} := up nat.
(* R2B-S negative control: the same value, but c also occurs in a binder type, so lowering c changes
   what the declaration quantifies over: the result-sort lowering does not apply *)
Definition up_binder (F : Type@{c} -> nat) : Type@{c} := up nat.

(* R3-down positive: a monomorphic constant at a global level l applied to an argument of a lower
   level by cumulativity (nat : Set <= Type@{l}), like Stdlib RingMicromega.PolC Z in
   ZMicromega.ZArithProof; Lean instantiates the reference at the argument's level. *)
Universe l.
Definition Box (C : Type@{l}) : Type@{l} := list C.
Inductive proof : Type@{l} := pdone : proof | pstep : Box nat -> proof -> proof.
Fixpoint steps (p : proof) : nat := match p with pdone => 0 | pstep b q => length b + steps q end.
Lemma box_len (b : Box nat) : length b = length b. Proof. reflexivity. Qed.
Example steps_ex : steps (pstep (cons 1 (cons 2 nil)) (pstep nil pdone)) = 2 := eq_refl.

(* bounded solver positive: both's result level b is read through the fact interpretation
   max(b, a) (a <= b); a use at one level gives Lean the postponed constraint max(?b, ?a) = a *)
Universe sa sb.
Constraint sa <= sb.
Definition both (A : Type@{sa}) (B : Type@{sb}) : Type@{sb} := prod A B.
Definition useboth (C : Type@{sa}) : Type@{sb} := both C C.
Definition useboth_nat : Type@{sb} := useboth nat.

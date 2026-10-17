(* Rule E fixture (docs/EQ_LOWERING.md): CoqEAL's `refinesE` shape, an equality of convertible relations
   stated at a larger universe than theirs (Rocq: cumulativity). Synthetic. *)
Universes a b c.
Constraint b < c.
Definition refines (A B : Type@{a}) (R : A -> B -> Type@{c}) := R.
(* convertible operands (refines unfolds to R): lowered to R's universe *)
Lemma refinesE (A B : Type@{a}) (R : A -> B -> Type@{b}) : @eq (A -> B -> Type@{c}) (refines A B R) R.
Proof. reflexivity. Qed.
(* not convertible (R, S distinct variables): never lowered *)
Lemma neq (A B : Type@{a}) (R S : A -> B -> Type@{b}) (h : R = S) : @eq (A -> B -> Type@{c}) R S.
Proof. rewrite h; reflexivity. Qed.
(* a statement whose conclusion is an equality at a type that does not end in a sort (for a forged report) *)
Lemma other (A : Type@{a}) (x : A) : x = x.
Proof. reflexivity. Qed.

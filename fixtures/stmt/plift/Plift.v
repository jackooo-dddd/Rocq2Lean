(* Rule P fixture (docs/PROP_LIFT.md): propositions used at a Type, through Rocq's Prop <= Type
   cumulativity, in the shapes of CoqEAL's refinement relations (fun_hrel, Rnat). Synthetic. *)
Definition frel (A B : Type) (f : B -> A) : A -> B -> Type := fun a b => f b = a.
Definition R : nat -> nat -> Type := frel nat nat S.
(* a proof of the proposition used as an inhabitant of the lifted type (obligation, PULift.up) *)
Definition r1 : R 1 0 := eq_refl.
(* an inhabitant of the lifted type used as a proof (PULift.down) *)
Definition back (a b : nat) (h : R a b) : S b = a := h.
(* a statement whose codomain is the lifted type: stated as the proposition *)
Lemma r_succ (n : nat) : R (S (S n)) (S n).
Proof. reflexivity. Qed.
(* a relation class over Type-valued relations, used at the lifted relation *)
Class refines (A B : Type) (Rel : A -> B -> Type) (a : A) (b : B) := refines_rel : Rel a b.
Definition refine_one : refines nat nat R 1 0 := r1.
Definition refine_back (a b : nat) (h : refines nat nat R a b) : S b = a := back a b h.
(* a proof at an argument position that expects the lifted type: its obligation states `R 1 0` *)
Definition pick (a b : nat) (h : R a b) : nat := b.
Definition r2 : nat := pick 1 0 eq_refl.
(* a match on an inhabitant of the lifted type, as the equation it lifts (PULift.down) *)
Definition dmatch (a b : nat) (h : R a b) : nat := match h with eq_refl => b end.

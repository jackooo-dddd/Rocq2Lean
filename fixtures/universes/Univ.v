(* Universe-interpretation fixtures: named monomorphic levels with explicit constraints. *)
Universe ua ub uc.
Constraint ua <= ub.
Constraint ub < uc.
Definition idb (A : Type@{ub}) (a : A) : A := a.
(* Reference at a lower level, justified by ua <= ub (cumulativity). *)
Definition usea (A : Type@{ua}) (a : A) : A := idb A a.
(* Reference with a shared level: the argument must be the declaration's own parameter. *)
Definition useb (A : Type@{ub}) (a : A) : A := idb A a.
(* Repeated references in one body. *)
Definition usea_twice (A : Type@{ua}) (a : A) : A := idb A (idb A a).
(* Reference at Set (Set <= ub). *)
Definition use_set (n : nat) : nat := idb nat n.
(* Composition through two generalized constants. *)
Definition via_usea (A : Type@{ua}) (a : A) : A := usea A (idb A a).
Lemma usea_id : forall (A : Type@{ua}) (a : A), usea A a = a. Proof. reflexivity. Qed.
(* A strict inclusion: needs ub < uc as type-in-type-free cumulativity, which the generalized
   Lean declaration (no cumulativity) cannot express. *)
Definition big : Type@{uc} := Type@{ub}.

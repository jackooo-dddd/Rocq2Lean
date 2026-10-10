(* R6 fixture: universe-polymorphic constants (genuine Rocq polymorphism, as in Corelib.Classes). *)
Set Universe Polymorphism.
Definition pid@{u} (A : Type@{u}) (a : A) : A := a.
Definition prel@{u} (A : Type@{u}) := A -> A -> Prop.
Definition pcomp@{u v w} {A : Type@{u}} {B : Type@{v}} {C : Type@{w}} (g : B -> C) (f : A -> B) (x : A) : C := g (f x).
Lemma pid_eq@{u} (A : Type@{u}) (a : A) : pid A a = a.
Proof. reflexivity. Qed.
(* a polymorphic constant using another one at its own variables *)
Definition ptwice@{u} (A : Type@{u}) (f : A -> A) : A -> A := pcomp@{u u u} f f.
(* needs cumulativity Type@{u} <= Type@{v} under the constraint u < v: Lean has neither *)
Definition plift@{u v | u < v} (A : Type@{u}) : Type@{v} := A.
Unset Universe Polymorphism.

Definition use_set : nat := pid nat 3.
Definition use_rel : prel nat := fun x y => x = y.
Lemma use_lemma : pid nat 3 = 3.
Proof. apply pid_eq. Qed.
Definition use_twice : nat := ptwice nat S 1.
Lemma use_twice_2 : use_twice = 3.
Proof. reflexivity. Qed.
(* an instance at a global (monomorphic) level of this declaration: pid@{l} with A : Type@{l} *)
Definition use_glob (A : Type) (a : A) : A := pid A a.

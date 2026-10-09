(* M2 expression fixtures. *)
Definition prop_id : forall P : Prop, P -> P := fun P p => p.
Definition compose (f g : nat -> nat) (x : nat) : nat := f (g x).
Definition twice (f : nat -> nat) : nat -> nat := compose f f.
Definition nested_let (n : nat) : nat :=
  let x := S n in let y := S x in let x := y in S x.        (* shadowing *)
Definition let_in_type : let T := nat in T -> nat := fun t => t.
Definition dep_id (A : Set) (x : A) : A := x.
Definition dep_pair (n : nat) (p : n = n) : n = n := p.
Definition pick_first (x y : nat) : nat := x.
Definition pick_second (x y : nat) : nat := y.
Definition f : nat := S O.                                   (* same short name as M2B.f *)
Lemma twice_succ : forall n, twice S n = S (S n). Proof. intro n. reflexivity. Qed.
Lemma first_second : forall x y, pick_first x y = pick_second y x. Proof. reflexivity. Qed.
Lemma vm_proof : twice S (twice S O) = S (S (S (S O))). Proof. vm_compute. reflexivity. Qed.
Lemma change_proof : forall n, compose S S n = S (S n). Proof. intro n. change (S (S n) = S (S n)). reflexivity. Qed.
Lemma dep_use : dep_id nat f = S O. Proof. reflexivity. Qed.
Definition shadow_params : nat -> nat -> nat := fun (x : nat) => fun (x : nat) => x.
Lemma shadow_inner : forall a b, shadow_params a b = b. Proof. reflexivity. Qed.

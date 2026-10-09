(* M3b: case analysis lowered to recursors. *)
From M3 Require Import M3Types.
Definition pred_r (n : RNat) : RNat := match n with RZ => RZ | RS m => m end.
Definition pred_nat (n : nat) : nat := match n with O => O | S m => m end.
Definition head_or {A : Set} (d : A) (l : RList A) : A := match l with RNil => d | RCons x _ => x end.
Definition tree_root_or {A : Set} (d : A) (t : Tree A) : A := match t with Leaf => d | Node _ x _ => x end.
(* Indexed, dependent: rebuild Vec A n from its constructor. *)
Definition vid {A : Set} {n : nat} (v : Vec A n) : Vec A n :=
  match v in Vec _ m return Vec A m with VNil => VNil | VCons x t => VCons x t end.
(* Indexed, dependent return type computed from the index. *)
Definition vtail {A : Set} {n : nat} (v : Vec A (S n)) : Vec A n :=
  match v in Vec _ m return match m with O => RNat | S k => Vec A k end with
  | VNil => RZ | VCons _ t => t end.
Lemma pred_r_RS : forall n, pred_r (RS n) = n. Proof. intro n. reflexivity. Qed.
Lemma pred_nat_S : forall n, pred_nat (S n) = n. Proof. intro n. reflexivity. Qed.
Lemma head_or_cons : forall (A : Set) (d x : A) l, head_or d (RCons x l) = x. Proof. reflexivity. Qed.
Lemma vid_cons : forall (A : Set) n (x : A) (t : Vec A n), vid (VCons x t) = VCons x t. Proof. reflexivity. Qed.
Lemma vtail_cons : forall (A : Set) n (x : A) (t : Vec A n), vtail (VCons x t) = t. Proof. reflexivity. Qed.
Lemma eq_sym_nat : forall a b : nat, a = b -> b = a. Proof. intros a b H. destruct H. reflexivity. Qed.

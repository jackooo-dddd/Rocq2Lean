(* Holdout fixtures: written after freezing the implementation at tag pilot-freeze-1. *)
From M3 Require Import M3Types M3Fix.

Inductive Bin : Set := BZ : Bin | B0 : Bin -> Bin | B1 : Bin -> Bin.
Fixpoint incr (b : Bin) : Bin := match b with BZ => B1 BZ | B0 b' => B1 b' | B1 b' => B0 (incr b') end.
Lemma incr_not_BZ : forall b, incr b <> BZ.
Proof. intros b H. destruct b; simpl in H; discriminate H. Qed.

Inductive ROpt (A : Set) : Set := RNone : ROpt A | RSome : A -> ROpt A.
Arguments RNone {A}. Arguments RSome {A}.
Definition omap {A B : Set} (f : A -> B) (o : ROpt A) : ROpt B :=
  match o with RNone => RNone | RSome a => RSome (f a) end.
Lemma omap_id : forall (A : Set) (o : ROpt A), omap (fun x => x) o = o.
Proof. intros A o. destruct o; reflexivity. Qed.

Inductive Pair (A B : Set) : Set := MkPair : A -> B -> Pair A B.
Arguments MkPair {A B}.
Definition swap {A B : Set} (p : Pair A B) : Pair B A := match p with MkPair a b => MkPair b a end.
Lemma swap_swap : forall (A B : Set) (p : Pair A B), swap (swap p) = p.
Proof. intros A B p. destruct p; reflexivity. Qed.

Inductive Le : nat -> nat -> Prop :=
| le_n : forall n, Le n n
| le_S : forall n m, Le n m -> Le n (S m).
Lemma le_0 : forall n, Le 0 n.
Proof. induction n as [|n IH]. - apply le_n. - apply le_S. exact IH. Qed.

Fixpoint app {A : Set} (l1 l2 : RList A) : RList A :=
  match l1 with RNil => l2 | RCons x t => RCons x (app t l2) end.
Lemma length_app : forall (A : Set) (l1 l2 : RList A), lengthR (app l1 l2) = addR (lengthR l1) (lengthR l2).
Proof. intros A l1 l2. induction l1 as [|x t IH]; simpl. - reflexivity. - rewrite IH. reflexivity. Qed.

Lemma addR_n_RS : forall n m, addR n (RS m) = RS (addR n m).
Proof. induction n as [|n IH]; intro m; simpl. - reflexivity. - rewrite IH. reflexivity. Qed.
Lemma addR_n_RZ' : forall n, addR n RZ = n.
Proof. induction n as [|n IH]; simpl. - reflexivity. - rewrite IH. reflexivity. Qed.
Lemma addR_comm : forall n m, addR n m = addR m n.
Proof. induction n as [|n IH]; intro m; simpl. - rewrite addR_n_RZ'. reflexivity. - rewrite IH, addR_n_RS. reflexivity. Qed.
Lemma addR_assoc : forall a b c, addR (addR a b) c = addR a (addR b c).
Proof. induction a as [|a IH]; intros b c; simpl. - reflexivity. - rewrite IH. reflexivity. Qed.

Fixpoint size {A : Set} (t : Tree A) : RNat :=
  match t with Leaf => RZ | Node l _ r => RS (addR (size l) (size r)) end.
Lemma size_mirror : forall (A : Set) (t : Tree A), size (mirrorR t) = size t.
Proof.
  intros A t. induction t as [|l IHl x r IHr]; simpl.
  - reflexivity.
  - rewrite IHl, IHr, addR_comm. reflexivity.
Qed.

Fixpoint vapp {A : Set} {n m : nat} (v : Vec A n) (w : Vec A m) : Vec A (n + m) :=
  match v in Vec _ k return Vec A (k + m) with
  | VNil => w
  | VCons x t => VCons x (vapp t w)
  end.
Lemma vapp_nil : forall (A : Set) m (w : Vec A m), vapp VNil w = w.
Proof. reflexivity. Qed.

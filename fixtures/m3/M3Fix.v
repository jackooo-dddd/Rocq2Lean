(* M3c: structural recursion lowered to recursors. *)
From M3 Require Import M3Types.
Fixpoint addR (n m : RNat) {struct n} : RNat := match n with RZ => m | RS p => RS (addR p m) end.
Fixpoint lengthR {A : Set} (l : RList A) : RNat := match l with RNil => RZ | RCons _ t => RS (lengthR t) end.
Fixpoint mapR {A B : Set} (f : A -> B) (l : RList A) : RList B :=
  match l with RNil => RNil | RCons x t => RCons (f x) (mapR f t) end.
Fixpoint mirrorR {A : Set} (t : Tree A) : Tree A :=
  match t with Leaf => Leaf | Node l x r => Node (mirrorR r) x (mirrorR l) end.
Fixpoint addAcc (n m : RNat) {struct n} : RNat := match n with RZ => m | RS p => addAcc p (RS m) end.
Fixpoint vmap {A B : Set} (f : A -> B) {n : nat} (v : Vec A n) : Vec B n :=
  match v with VNil => VNil | VCons x t => VCons (f x) (vmap f t) end.
Fixpoint double_nat (n : nat) : nat := match n with O => O | S p => S (S (double_nat p)) end.
(* Open-variable definitional equations, checked by reflexivity in Rocq and re-checked in Lean. *)
Lemma addR_RZ : forall m, addR RZ m = m. Proof. reflexivity. Qed.
Lemma addR_RS : forall n m, addR (RS n) m = RS (addR n m). Proof. reflexivity. Qed.
Lemma lengthR_nil : forall A : Set, lengthR (@RNil A) = RZ. Proof. reflexivity. Qed.
Lemma lengthR_cons : forall (A : Set) (a : A) xs, lengthR (RCons a xs) = RS (lengthR xs). Proof. reflexivity. Qed.
Lemma mirrorR_node : forall (A : Set) l (x : A) r, mirrorR (Node l x r) = Node (mirrorR r) x (mirrorR l). Proof. reflexivity. Qed.
Lemma addAcc_RS : forall n m, addAcc (RS n) m = addAcc n (RS m). Proof. reflexivity. Qed.
Lemma vmap_cons : forall (A B : Set) (f : A -> B) n (x : A) (t : Vec A n), vmap f (VCons x t) = VCons (f x) (vmap f t). Proof. reflexivity. Qed.
Lemma double_nat_S : forall n, double_nat (S n) = S (S (double_nat n)). Proof. reflexivity. Qed.
(* Closed computations. *)
Lemma addR_2_1 : addR (RS (RS RZ)) (RS RZ) = RS (RS (RS RZ)). Proof. reflexivity. Qed.
Lemma mirror_small : mirrorR (Node (Node Leaf RZ Leaf) (RS RZ) Leaf) = Node Leaf (RS RZ) (Node Leaf RZ Leaf). Proof. reflexivity. Qed.

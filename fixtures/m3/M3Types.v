(* M3a: fresh inductive types (parameters restricted to Set). *)
Inductive RNat : Set := RZ : RNat | RS : RNat -> RNat.
Inductive RList (A : Set) : Set := RNil : RList A | RCons : A -> RList A -> RList A.
Inductive Tree (A : Set) : Set := Leaf : Tree A | Node : Tree A -> A -> Tree A -> Tree A.
Inductive Vec (A : Set) : nat -> Set :=
| VNil : Vec A O
| VCons : forall n, A -> Vec A n -> Vec A (S n).
Arguments RNil {A}. Arguments RCons {A}. Arguments Leaf {A}. Arguments Node {A}.
Arguments VNil {A}. Arguments VCons {A n}.

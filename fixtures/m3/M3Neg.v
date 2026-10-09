(* M3 negative inputs: patterns outside the support profile, which must be rejected explicitly. *)
From M3 Require Import M3Types M3Fix.
Fixpoint evenR (n : RNat) : RNat := match n with RZ => RS RZ | RS p => oddR p end
with oddR (n : RNat) : RNat := match n with RZ => RZ | RS p => evenR p end.
Fixpoint half (n : RNat) : RNat := match n with RS (RS p) => RS (half p) | _ => RZ end.
Fixpoint addPre (k : RNat) (n : RNat) {struct n} : RNat := match n with RZ => k | RS p => addPre (RS k) p end.
CoInductive Stream : Set := SCons : RNat -> Stream -> Stream.
Definition sprop_id (P : SProp) (p : P) : P := p.
Polymorphic Definition pid@{u} (A : Type@{u}) (a : A) : A := a.
Inductive Rose : Set := RNode : RList Rose -> Rose.
Fixpoint rose_size (r : Rose) : RNat := match r with RNode _ => RS RZ end.

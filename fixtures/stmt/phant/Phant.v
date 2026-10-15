(* Rule Q-a fixture (docs/PHANTOM_SORT.md): HB's phantom unification check, whose sort arguments Rocq
   types by cumulativity at a level above both carriers. Synthetic. *)
From Corelib Require Import ssreflect.
(* HB.structures.unify's shape *)
Definition unify (T1 T2 : Type) (t1 : T1) (t2 : T2) (s : nat) := phantom T1 t1 -> phantom T2 t2.
Universes a b c.
(* the check at one common sort Type@{c} for two carriers at independent levels a, b (a, b < c) *)
Definition chk (A : Type@{a}) (B : Type@{b}) (h : unify Type@{c} Type@{c} A B 0) : nat := 0.
(* a statement whose hypothesis is such a check (HB's builder obligations) *)
Lemma chk_stmt (A : Type@{a}) (B : Type@{b}) (h : unify Type@{c} Type@{c} A B 1) : chk A B h = 0.
Proof. reflexivity. Qed.
(* not a phantom definition: the body is not a chain of phantom checks *)
Definition notph (T1 : Type) (t1 : T1) := t1 = t1.
Definition chk_np (A : Type@{a}) (h : notph Type@{c} A) : nat := 0.

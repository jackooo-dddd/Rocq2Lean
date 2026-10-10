(* M6: the real Stdlib/Corelib functions behind lia's certificates (not copies): mutual fixpoints
   (Pos.add/add_carry, Pos.sub_mask/sub_mask_carry), decreasing matches that are not outermost
   (Pos.compare_cont, Pos.eqb, Z.pos_sub, ListDef.nth), a let-bound partial recursive application
   (Pos.peano_rect), recursion on accessibility proofs (Acc_rect, Acc_inv: a functional recursive
   field, a non-uniform parameter). Closed computations and open-variable computation rules. *)
From Stdlib Require Import PArith.BinPos ZArith.BinInt Lists.List.
Import ListNotations.
Open Scope positive_scope.

Example add_ex : Pos.add 7 12 = 19 := eq_refl.
Example add_carry_ex : Pos.add_carry 7 12 = 20 := eq_refl.
Example sub_mask_ex : Pos.sub_mask 12 7 = Pos.IsPos 5 := eq_refl.
Example sub_mask_ex2 : Pos.sub_mask 7 12 = Pos.IsNeg := eq_refl.
Example compare_ex : Pos.compare 13 9 = Gt := eq_refl.
Example compare_cont_ex : Pos.compare_cont Eq 9 13 = Lt := eq_refl.
Example eqb_ex : Pos.eqb 21 21 = true := eq_refl.
Example pos_sub_ex : Z.pos_sub 5 9 = (-4)%Z := eq_refl.
Example peano_ex : Pos.peano_rect (fun _ => nat) 0%nat (fun _ n => S n) 6 = 5%nat := eq_refl.
Example nth_ex : nth 2 [10; 20; 30]%nat 0%nat = 30%nat := eq_refl.

Lemma add_step (p q : positive) : Pos.add p~1 q~1 = (Pos.add_carry p q)~0. Proof. reflexivity. Qed.
Lemma sub_mask_step (p q : positive) : Pos.sub_mask p~0 q~1 = Pos.succ_double_mask (Pos.sub_mask_carry p q).
Proof. reflexivity. Qed.
Lemma compare_cont_step (r : comparison) (p q : positive) : Pos.compare_cont r p~1 q~0 = Pos.compare_cont Gt p q.
Proof. reflexivity. Qed.
Lemma eqb_step (p q : positive) : Pos.eqb p~0 q~0 = Pos.eqb p q. Proof. reflexivity. Qed.
Lemma pos_sub_step (p q : positive) : Z.pos_sub p~1 q~1 = Z.double (Z.pos_sub p q). Proof. reflexivity. Qed.
Lemma peano_step (P : positive -> Type) (a : P 1) (f : forall p, P p -> P (Pos.succ p)) (q : positive) :
  Pos.peano_rect P a f q~0 = Pos.peano_rect (fun p => P p~0) (f _ a) (fun p x => f _ (f _ x)) q.
Proof. reflexivity. Qed.
Lemma nth_step {A} (m : nat) (a : A) (t : list A) (d : A) : nth (S m) (a :: t) d = nth m t d. Proof. reflexivity. Qed.

(* Acc: structural recursion on an accessibility proof (functional recursive field) *)
Lemma acc_rect_step (A : Type) (R : A -> A -> Prop) (P : A -> Type)
  (f : forall x, (forall y, R y x -> Acc R y) -> (forall y, R y x -> P y) -> P x) (x : A) (h : forall y, R y x -> Acc R y) :
  Acc_rect P f (Acc_intro x h) = f x h (fun y r => Acc_rect P f (h y r)).
Proof. reflexivity. Qed.
Lemma acc_inv_step (A : Type) (R : A -> A -> Prop) (x : A) (h : forall y, R y x -> Acc R y) :
  Acc_inv (Acc_intro x h) = h.
Proof. reflexivity. Qed.

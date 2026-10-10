(* M6 fixture: structural recursion on a proof of a two-constructor Prop inductive, into data
   (the pattern of MathComp's ssrnat.find_ex_minn). Lean cannot eliminate such a proof into Type:
   the translator lowers the fixpoint to Acc.rec over its call-graph relation. *)

Inductive accb (P : nat -> bool) (i : nat) : Prop :=
| AccB0 : P i = true -> accb P i
| AccBS : accb P (S i) -> accb P i.

(* The first m' >= m with P m' = true. The recursive call's decreasing argument is a match on the
   proof h; its AccB0 branch is impossible because P m = false (dead code by False elimination). *)
Fixpoint search (P : nat -> bool) (m : nat) (h : accb P m) {struct h} : nat :=
  (if P m as b return P m = b -> nat
   then fun _ => m
   else fun e =>
     search P (S m)
       (match h in accb _ _ return accb P (S m) with
        | AccB0 _ _ t => False_ind _ (eq_ind true (fun b => if b then True else False) I false
                                         (eq_trans (eq_sym t) e))
        | AccBS _ _ a => a
        end)) eq_refl.

Definition P2 (n : nat) : bool := match n with 2 => true | _ => false end.

Definition h0 : accb P2 0 := AccBS P2 0 (AccBS P2 1 (AccB0 P2 2 eq_refl)).

(* Computation through the translated recursion (Lean must unfold Acc.rec through the
   well-foundedness proof). *)
Lemma search_ex : search P2 0 h0 = 2.
Proof. reflexivity. Qed.

Lemma search_ex1 : search P2 1 (AccBS P2 1 (AccB0 P2 2 eq_refl)) = 2.
Proof. reflexivity. Qed.

(* Open-variable unfolding: the recursion step holds by conversion for an arbitrary proof a, so the
   translation must unfold Acc.rec definitionally on an open argument. *)
Lemma search_step0 (a : accb P2 1) : search P2 0 (AccBS P2 0 a) = search P2 1 a.
Proof. reflexivity. Qed.

(* Case B fixture (structure carrier levels; docs/CARRIER_LEVELS.md). Not Prosa. The MathComp
   declarations are the real ones (exported with their closure); only these two statements are synthetic:
   - pair_nat_refl : a generic eqType paired with nat's canonical eqType (prod_eqType T nat_eqType), the
                     shape of Classic's fp_rta_comp statements (rt_bounds : seq (Task * nat));
   - pair_nat_in   : membership in a sequence of such pairs (in_mem through prod_eqType's predType). *)
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
Lemma pair_nat_refl (T : eqType) (x : T) (n : nat) : (x, n) == (x, n).
Proof. by rewrite eqxx. Qed.
Lemma pair_nat_in (T : eqType) (s : seq (T * nat)) (x : T * nat) : x \in x :: s.
Proof. by rewrite inE eqxx. Qed.

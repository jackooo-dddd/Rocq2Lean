(* Rule R fixture (coherence modulo an R2F reading; docs/COHERENCE_READINGS.md). Not Prosa. The MathComp
   declarations are the real ones (exported with their closure): choice's sub-type Countable instance,
   whose references read shared levels as max(u_l, ...), and fintype's factory_66 that uses it at
   ordinal. The statements below are synthetic:
   - sub_pickle_refl : a generic sub-countType of a generic countType (choice's sub-type instance);
   - ord_pickle_refl : ordinal's countType (fintype's factory_66 chain). *)
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype choice fintype.
Lemma sub_pickle_refl (T : countType) (P : pred T) (sT : subCountType P) (x : sT) : pickle x = pickle x.
Proof. by []. Qed.
Lemma ord_pickle_refl (n : nat) (i : 'I_n) : pickle i = pickle i.
Proof. by []. Qed.
(* Rule H: a generic eqType binder T (carrier eqtype.51) beside a value whose prerequisite hypotheses are
   instantiated at concrete carriers (nat's eqType at 0, through 'I_n's eqType in Prosa's seqset): the
   shape of Classic's Affinity.task_affinity. *)
From prosa.util Require Import seqset.
Definition ord_affinity (n : nat) := {set 'I_n}.
Definition task_ord_affinity (T : eqType) (n : nat) := T -> ord_affinity n.

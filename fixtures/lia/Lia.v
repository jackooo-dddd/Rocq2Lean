(* M6 completion: small theorems proved by Rocq's lia. Their proof terms carry real micromega
   certificates (ZMicromega.ZTautoChecker over Psatz witnesses) checked by reflection; the
   translation transports these proof terms and their whole dependency closure, never a tactic. *)
From Stdlib Require Import Lia ZArith.
Open Scope Z_scope.

Lemma lia_nat_lt (n m : nat) : (n <= m)%nat -> (n < m + 1)%nat. Proof. lia. Qed.
Lemma lia_nat_sum (a b c : nat) : (a + b <= c)%nat -> (a <= c)%nat. Proof. lia. Qed.
Lemma lia_z_step (x y : Z) : x < y -> x + 1 <= y. Proof. lia. Qed.
Lemma lia_z_two (x y : Z) : 2 * x + 3 <= 2 * y -> x < y. Proof. lia. Qed.
Lemma lia_nat_sub (n m : nat) : (m <= n)%nat -> (n - m + m = n)%nat. Proof. lia. Qed.

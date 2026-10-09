Definition id_nat (n : nat) : nat := n.

Theorem id_nat_correct : forall n : nat, id_nat n = n.
Proof.
  intro n.
  reflexivity.
Qed.

Definition f : nat := S (S O).                               (* same short name as M2A.f *)
From M2 Require M2A.
Lemma fs_differ : M2A.f = S O /\ True -> f = S (S O). Proof. intros _. reflexivity. Qed.
Lemma f_values : M2A.f = S O. Proof. reflexivity. Qed.
Lemma f_values_b : f = S (S O). Proof. reflexivity. Qed.

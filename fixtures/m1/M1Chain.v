(* A separately compiled module: cross-module and opaque dependency chains. *)
From M1 Require Import M1Base.
Lemma chain_qed : two = S (S O). Proof. exact two_eq_qed. Qed.
Lemma chain_sec : add_two two = S (S two). Proof. exact (add_two_eq two). Qed.
Lemma chain_opaque_data : three_opaque = three_opaque. Proof. reflexivity. Qed.
Lemma chain_chain : two = S (S O). Proof. exact chain_qed. Qed.
Definition uses_color : Color := Red.

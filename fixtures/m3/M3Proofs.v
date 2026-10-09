(* M3d: original induction proofs, written the ordinary way. *)
From M3 Require Import M3Types M3Case M3Fix.
Lemma addR_n_RZ : forall n, addR n RZ = n.
Proof. induction n as [|n IH]; simpl. - reflexivity. - rewrite IH. reflexivity. Qed.
Lemma length_map : forall (A B : Set) (f : A -> B) xs, lengthR (mapR f xs) = lengthR xs.
Proof. intros A B f xs. induction xs as [|x xs IH]; simpl. - reflexivity. - rewrite IH. reflexivity. Qed.
Lemma mirror_mirror : forall (A : Set) (t : Tree A), mirrorR (mirrorR t) = t.
Proof. intros A t. induction t as [|l IHl x r IHr]; simpl. - reflexivity. - rewrite IHl, IHr. reflexivity. Qed.
Lemma vmap_id : forall (A : Set) n (v : Vec A n), vmap (fun x => x) v = v.
Proof. intros A n v. induction v as [|n x t IH]; simpl. - reflexivity. - rewrite IH. reflexivity. Qed.
Lemma vid_id : forall (A : Set) n (v : Vec A n), vid v = v.
Proof. intros A n v. destruct v; reflexivity. Qed.

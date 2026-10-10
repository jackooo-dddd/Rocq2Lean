(* Regression fixture (found during M5): fixpoint branches that mention the decreasing argument or
   an index variable of its type. Inside a branch, run at every recursion depth, these denote the
   constructor applied to the branch's fields and that constructor's indices, not the outermost
   call's arguments. Each lemma is proved by computation (reflexivity). *)
From M3 Require Import M3Types.
Fixpoint keep (n : nat) : nat := match n with O => n | S p => keep p end.
Fixpoint subx (n m : nat) {struct n} : nat := match n, m with S k, S l => subx k l | _, _ => n end.
Fixpoint vlen {A : Set} {n : nat} (v : Vec A n) : nat := match v with VNil => n | VCons _ t => S (vlen t) end.
Lemma keep_3 : keep 3 = 0. Proof. reflexivity. Qed.
Lemma subx_3_3 : subx 3 3 = 0. Proof. reflexivity. Qed.
Lemma subx_5_2 : subx 5 2 = 3. Proof. reflexivity. Qed.
Lemma vlen_2 : vlen (VCons 1 (VCons 2 VNil)) = 2. Proof. reflexivity. Qed.
Lemma sub_3_3 : 3 - 3 = 0. Proof. reflexivity. Qed.

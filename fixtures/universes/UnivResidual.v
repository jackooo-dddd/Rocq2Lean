(* A universe level that nothing constrains: ur occurs only in the body of `cst` (a proof-local
   level, rule R2B), and nothing in that body fixes it. The translator defaults it to its minimal
   model (Set < ur gives 1) only with a justification (the declaration is kernel-valid for every
   value of the level), re-checked by the consumer. *)
Universe ur.
Definition cst : nat := let _ := (fun (A : Type@{ur}) (a : A) => a) in O.
Definition use_cst : nat := cst.
Lemma use_cst_eq : use_cst = O. Proof. reflexivity. Qed.

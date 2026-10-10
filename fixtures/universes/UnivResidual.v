(* A universe level that nothing constrains at a reference: `cst` mentions the global level ur
   (so its translation has a universe parameter), but its use in `use_cst` fixes no level. The
   translator defaults it to 0 only with a justification (the declaration is kernel-valid for every
   value of the level), re-checked by the consumer. *)
Universe ur.
Definition cst : nat := let _ := (fun (A : Type@{ur}) (a : A) => a) in O.
Definition use_cst : nat := cst.
Lemma use_cst_eq : use_cst = O. Proof. reflexivity. Qed.

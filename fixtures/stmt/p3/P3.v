(* Rule round 2, P3 fixture (tests/statement/check_multi_instance.py). Not Prosa.
   - odat:  opaque data whose body has a proof subterm (an obligation, generic in odat's level), the
            shape of MathComp's pair_eqP;
   - use2:  a definition using odat at two universe instances (nat, and a parameter's type B): its
            pending artifact needs odat's obligation at two instances. *)
Definition odat (A : Type) (x : A) : {y : A | y = x}.
Proof. exists x. reflexivity. Qed.
Definition use2 (B : Type) (b : B) : B :=
  match proj1_sig (odat nat 0) with 0 => proj1_sig (odat B b) | _ => b end.
Lemma use2_id (B : Type) (b : B) : use2 B b = use2 B b.
Proof. reflexivity. Qed.

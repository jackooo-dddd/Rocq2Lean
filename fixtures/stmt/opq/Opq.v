(* Synthetic A′ fixture (docs/OPAQUE_DATA.md; tests/statement/check_opaque.py). Not Prosa: opaque data
   (Qed constants of a Set/Type type) whose bodies are translated mechanically, opacity kept, proof
   subterms extracted as obligations.
   - pick:            opaque data without proof subterms (a value of a type with many values);
   - pick_succ(_pos): a definition and a statement using it;
   - bounded:         opaque data with a proof subterm (2 <= 5): pending on its obligation;
   - bval(_le):       a definition and a statement pending through it;
   - nat_eqP:         reflect-valued opaque data by induction (the shape of MathComp's eqnP), its
                      proof subterms extracted under binders;
   - eq_dec_nat:      a transparent definition computing with nat_eqP;
   - eqb_refl:        a statement about the boolean test, independent of nat_eqP. *)
Definition pick : nat.
Proof. exact 3. Qed.
Definition pick_succ : nat := S pick.
Lemma pick_succ_pos : 0 < pick_succ.
Proof. unfold pick_succ, lt. apply le_n_S. apply le_0_n. Qed.

Definition bounded : {m : nat | m <= 5}.
Proof. exists 2. repeat constructor. Qed.
Definition bval : nat := proj1_sig bounded.
Lemma bval_le : bval <= 5.
Proof. unfold bval. destruct bounded as [m H]. exact H. Qed.

Inductive reflect (P : Prop) : bool -> Set :=
| ReflectT : P -> reflect P true
| ReflectF : ~ P -> reflect P false.
Fixpoint eqb (n m : nat) : bool :=
  match n, m with
  | 0, 0 => true
  | S n', S m' => eqb n' m'
  | _, _ => false
  end.
Definition nat_eqP : forall n m : nat, reflect (n = m) (eqb n m).
Proof.
  induction n as [|n IH]; destruct m as [|m]; simpl.
  - apply ReflectT; reflexivity.
  - apply ReflectF; discriminate.
  - apply ReflectF; discriminate.
  - destruct (IH m) as [h|h].
    + apply ReflectT; rewrite h; reflexivity.
    + apply ReflectF; intro e; injection e; exact h.
Qed.
Definition eq_dec_nat (n m : nat) : {n = m} + {n <> m} :=
  match nat_eqP n m with ReflectT _ h => left h | ReflectF _ h => right h end.
Lemma eqb_refl : forall n, eqb n n = true.
Proof. induction n as [|n IH]; simpl; [reflexivity | exact IH]. Qed.

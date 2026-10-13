(* Synthetic fixture for Task B (docs/TERMINATION.md; tests/statement/check_termination.py). Not Prosa:
   recursion whose recursive call is on a subterm that Rocq's guard condition establishes only by
   reducing a structural function (MathComp's edivn_rec / modn_rec shape), and the dependents a
   lowering with a termination obligation must handle:
   - sub:         structural subtraction; returns its first argument or a subterm of it;
   - edivr:       fix loop m q {struct m} := match sub m d with 0 => (q, m) | S m' => loop m' (S q) end;
   - modr:        the same recursion with one argument (the modn_rec shape);
   - divr:        a definition computed through edivr;
   - divr_le:     a theorem statement about divr;
   - T3, t3:      a type that is nat only if divr 7 2 reduces to 3, and a value of it (needs
                  definitional unfolding of edivr: the conversion-dependence boundary);
   - divr_7_2:    a statement about the closed value (no conversion needed to state it). *)
Fixpoint sub (m n : nat) {struct m} : nat :=
  match m, n with
  | S m', S n' => sub m' n'
  | _, _ => m
  end.
Definition edivr (d : nat) : nat -> nat -> nat * nat :=
  fix loop (m q : nat) {struct m} :=
    match sub m d with
    | 0 => (q, m)
    | S m' => loop m' (S q)
    end.
Definition modr (d : nat) : nat -> nat :=
  fix loop (m : nat) {struct m} :=
    match sub m d with
    | 0 => m
    | S m' => loop m'
    end.
Definition divr (m d : nat) : nat := fst (edivr (pred d) m 0).
Lemma divr_le : forall m d, divr m d <= divr m d.
Proof. intros; apply le_n. Qed.
Definition T3 : Type := match divr 7 2 with 3 => nat | _ => bool end.
Definition t3 : T3 := 0.
Lemma divr_7_2 : divr 7 2 = 3.
Proof. reflexivity. Qed.

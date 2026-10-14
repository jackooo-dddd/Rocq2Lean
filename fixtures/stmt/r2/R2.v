(* Rule-round 2 fixture (tests/statement/check_universe_r2.py). Not Prosa.
   - pairR:   an inductive whose parameters share one level (CoqEAL list_R's shape: one level for
              both carriers and the relation); Rocq instantiates it with carriers at independent
              levels by cumulativity;
   - pairR_intro: a statement quantifying over two carriers at independent levels; its Lean
              translation through pairR's single level would identify them (narrowing): refused;
   - two:     a statement with two independent binder levels (the negative control narrows it). *)
Universe ul.
Inductive pairR (A1 A2 : Type@{ul}) (R : A1 -> A2 -> Type@{ul}) : Type@{ul} :=
  PR : forall a1 a2, R a1 a2 -> pairR A1 A2 R.
Lemma pairR_intro (A : Type) (C : Type) (R : A -> C -> Type) (a : A) (c : C) (r : R a c) :
  exists p : pairR A C R, p = p.
Proof. exists (PR A C R a c r). reflexivity. Qed.
Lemma two (A : Type) (B : Type) (f : A -> B) : f = f.
Proof. reflexivity. Qed.

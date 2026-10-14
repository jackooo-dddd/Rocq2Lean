(* R-SPLIT fixture (tests/statement/check_level_split.py, docs/LEVEL_SPLIT.md). Not Prosa.
   - pR:      list_R's shape: one level `us` for both carriers and the relation, the result at its own
              level `ur` above it (an upper bound the copies must inherit);
   - fun_R:   a definition (CoqEAL's map_R / pred_R shape): `uf` is the sort of three parameters and
              occurs nowhere else; its result is the separate level of `B_R`;
   - pR_intro / fun_R_id: statements that use pR / fun_R at carriers of independent levels (Rocq:
              by cumulativity; Lean: only through the split view);
   - qR / qR_intro: `uq` also occurs in a constructor argument: not eligible; the statement stays
              refused (binder independence), as before the rule;
   - gR:      `ug` also occurs in the body: not eligible (the negative control forges a split of it);
   - pR_tail: a split definition referencing the split pR at the same level `us` (its copies are
              arguments for pR's copies: `us__s<i> <= us`). *)
Universe us ur.
Inductive pR (A1 A2 : Type@{us}) (R : A1 -> A2 -> Type@{us}) : Type@{ur} :=
  | pR_nil : pR A1 A2 R
  | pR_cons : forall a1 a2, R a1 a2 -> pR A1 A2 R -> pR A1 A2 R.
Definition pR_tail (A1 A2 : Type@{us}) (R : A1 -> A2 -> Type@{us}) (x : pR A1 A2 R) : pR A1 A2 R :=
  match x with pR_nil _ _ _ => pR_nil A1 A2 R | pR_cons _ _ _ _ _ _ t => t end.
Universe uf.
Definition fun_R (A1 A2 : Type@{uf}) (A_R : A1 -> A2 -> Type@{uf}) (B1 B2 : Type) (B_R : B1 -> B2 -> Type)
  (f1 : A1 -> B1) (f2 : A2 -> B2) : Type :=
  forall a1 a2, A_R a1 a2 -> B_R (f1 a1) (f2 a2).
Lemma pR_intro (A : Type) (C : Type) (R : A -> C -> Type) :
  exists p : pR A C R, p = p.
Proof. exists (pR_nil A C R). reflexivity. Qed.
Lemma fun_R_id (A : Type) (C : Type) (R : A -> C -> Type) (f : fun_R A C R A C R (fun x => x) (fun x => x)) :
  f = f.
Proof. reflexivity. Qed.
Universe uq uq2.
Inductive qR (A1 A2 : Type@{uq}) (R : A1 -> A2 -> Type@{uq}) : Type@{uq2} :=
  qR_mk : forall T : Type@{uq}, (T -> A1) -> qR A1 A2 R.
Lemma qR_intro (A : Type) (C : Type) (R : A -> C -> Type) (a : A) :
  exists p : qR A C R, p = p.
Proof. exists (qR_mk A C R A (fun x => x)). reflexivity. Qed.
Universe ug ug2.
Definition gR (A1 A2 : Type@{ug}) : Type@{ug2} := A1 -> A2 -> Type@{ug}.

(* R-CARRIER synthetic fixture (tests/statement/check_carrier.py; docs/CARRIER_LEVELS.md). Not Prosa.
   A minimal eqType / subType hierarchy with MathComp's universe shape, for the correspondence proofs
   (tests/statement/proofs/carrier_correspondence.lean), which concern only these declarations:
   - eqT : one carrier level cb1 (the structure is monomorphic, as Equality.type);
   - prodEq : two eqT operands and their product (P2: the operands' carriers vary independently);
   - natEq : nat's instance (its carrier stays nat, at the lowest level);
   - subT / sval / insubT : a subtype structure over a base carrier T : Type@{cs1} whose own sort is at
     cs2 <= cs1 (P1: the parameter carrier is read minimally; insubT keeps both carriers generic);
   - prod_nat_refl / insub_some : statements over a generic eqT paired with natEq, and over insubT;
   - prod_same : a genuine dependency (the operands are equal: typing relates their carriers, never split). *)
Universes cb1 cb2.
Record eqT : Type@{cb2} := EqPack { carrier : Type@{cb1}; eqop : carrier -> carrier -> bool }.
Definition prodEq (T1 T2 : eqT) : eqT :=
  EqPack (carrier T1 * carrier T2) (fun x y => andb (eqop T1 (fst x) (fst y)) (eqop T2 (snd x) (snd y))).
Definition natEq : eqT := EqPack nat Nat.eqb.
Lemma prod_nat_refl (T : eqT) (x : carrier T) (n : nat) :
  eqop (prodEq T natEq) (x, n) (x, n) = andb (eqop T x x) (Nat.eqb n n).
Proof. reflexivity. Qed.
Lemma prod_same (T1 T2 : eqT) (e : T1 = T2) (x : carrier (prodEq T1 T2)) : x = x.
Proof. reflexivity. Qed.
Universes cs1 cs2 cs3.
Constraint cs2 <= cs1.
Record subT (T : Type@{cs1}) (P : T -> bool) : Type@{cs3} :=
  SubPack { ssort : Type@{cs2}; sval : ssort -> T; ssub : forall x, P x = true -> ssort }.
Definition insubT (T : Type@{cs1}) (P : T -> bool) (sT : subT T P) (x : T) : option (ssort T P sT) :=
  (if P x as b return P x = b -> option (ssort T P sT) then fun h => Some (ssub T P sT x h) else fun _ => None) eq_refl.
Lemma insub_some (T : Type@{cs1}) (P : T -> bool) (sT : subT T P) (x : T) (h : P x = true) :
  insubT T P sT x = insubT T P sT x.
Proof. reflexivity. Qed.

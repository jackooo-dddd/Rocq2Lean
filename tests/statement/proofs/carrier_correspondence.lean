import Rocq2LeanOut
/-!
R-CARRIER correspondence for the synthetic CbSyn fixture only. The independent carrier levels
`a, b` are compared with the common level `max a b` by explicitly lifting both carriers.
These are representation proofs about translated declarations, not corpus proofs.
-/
noncomputable section
namespace CarrierCorrespondence

/-- Lift an equality structure's carrier, retaining its operation through `ULift.down`. -/
def liftEq.{a, b, r} (T : Rocq.SF.CbSyn.eqT.{a, r}) :
    Rocq.SF.CbSyn.eqT.{max a b, r} :=
  Rocq.SF.CbSyn.eqT.EqPack (ULift.{max a b} (Rocq.SF.CbSyn.carrier T))
    (fun x y => Rocq.SF.CbSyn.eqop T x.down y.down)

universe a b r

section equality
variable (T : Rocq.SF.CbSyn.eqT.{a, r})

def eqUp (x : Rocq.SF.CbSyn.carrier T) :
    Rocq.SF.CbSyn.carrier (liftEq.{a, b, r} T) := ULift.up x

def eqDown (x : Rocq.SF.CbSyn.carrier (liftEq.{a, b, r} T)) :
    Rocq.SF.CbSyn.carrier T := x.down

theorem eq_down_up (x : Rocq.SF.CbSyn.carrier T) :
    eqDown T (eqUp.{a, b, r} T x) = x := rfl

theorem eq_up_down (x : Rocq.SF.CbSyn.carrier (liftEq.{a, b, r} T)) :
    eqUp T (eqDown T x) = x := rfl

theorem liftEq_eqop (x y : Rocq.SF.CbSyn.carrier T) :
    Rocq.SF.CbSyn.eqop (liftEq.{a, b, r} T) (eqUp T x) (eqUp T y) =
      Rocq.SF.CbSyn.eqop T x y := rfl
end equality

section product
variable (T1 : Rocq.SF.CbSyn.eqT.{a, r}) (T2 : Rocq.SF.CbSyn.eqT.{b, r})

def prodUp (x : Rocq.SF.CbSyn.carrier (Rocq.SF.CbSyn.prodEq.{a, b, r, r, r} T1 T2)) :
    Rocq.SF.CbSyn.carrier (Rocq.SF.CbSyn.prodEq.{max a b, max a b, r, r, r}
      (liftEq.{a, b, r} T1) (liftEq.{b, a, r} T2)) :=
  Rocq.Corelib.Init.Datatypes.prod.rec
    (fun x1 x2 => Rocq.Corelib.Init.Datatypes.prod.pair _ _ (ULift.up x1) (ULift.up x2)) x

def prodDown (x : Rocq.SF.CbSyn.carrier
    (Rocq.SF.CbSyn.prodEq.{max a b, max a b, r, r, r}
      (liftEq.{a, b, r} T1) (liftEq.{b, a, r} T2))) :
    Rocq.SF.CbSyn.carrier (Rocq.SF.CbSyn.prodEq.{a, b, r, r, r} T1 T2) :=
  Rocq.Corelib.Init.Datatypes.prod.rec
    (fun x1 x2 => Rocq.Corelib.Init.Datatypes.prod.pair _ _ x1.down x2.down) x

theorem prod_down_up
    (x : Rocq.SF.CbSyn.carrier (Rocq.SF.CbSyn.prodEq.{a, b, r, r, r} T1 T2)) :
    prodDown T1 T2 (prodUp T1 T2 x) = x := by
  induction x with
  | pair x1 x2 => rfl

theorem prod_up_down (x : Rocq.SF.CbSyn.carrier
    (Rocq.SF.CbSyn.prodEq.{max a b, max a b, r, r, r}
      (liftEq.{a, b, r} T1) (liftEq.{b, a, r} T2))) :
    prodUp T1 T2 (prodDown T1 T2 x) = x := by
  induction x with
  | pair x1 x2 => rfl

theorem prod_eqop
    (x y : Rocq.SF.CbSyn.carrier (Rocq.SF.CbSyn.prodEq.{a, b, r, r, r} T1 T2)) :
    Rocq.SF.CbSyn.eqop (Rocq.SF.CbSyn.prodEq.{a, b, r, r, r} T1 T2) x y =
      Rocq.SF.CbSyn.eqop (Rocq.SF.CbSyn.prodEq.{max a b, max a b, r, r, r}
        (liftEq.{a, b, r} T1) (liftEq.{b, a, r} T2)) (prodUp T1 T2 x) (prodUp T1 T2 y) := by
  induction x with
  | pair x1 x2 =>
    induction y with
    | pair y1 y2 => rfl
end product

section natural
-- The split operands are genuinely at different levels: `a + 1` and `0`.
-- In particular, the second operand's carrier is still Nat, before the common-level lift.
variable (T : Rocq.SF.CbSyn.eqT.{a + 1, r})

theorem prod_nat_down_up
    (x : Rocq.SF.CbSyn.carrier (Rocq.SF.CbSyn.prodEq.{a + 1, 0, r, r, r}
      T Rocq.SF.CbSyn.natEq.{r})) :
    prodDown T Rocq.SF.CbSyn.natEq (prodUp T Rocq.SF.CbSyn.natEq x) = x :=
  prod_down_up T Rocq.SF.CbSyn.natEq x

theorem prod_nat_up_down (x : Rocq.SF.CbSyn.carrier
    (Rocq.SF.CbSyn.prodEq.{a + 1, a + 1, r, r, r}
      (liftEq.{a + 1, 0, r} T) (liftEq.{0, a + 1, r} Rocq.SF.CbSyn.natEq))) :
    prodUp T Rocq.SF.CbSyn.natEq (prodDown T Rocq.SF.CbSyn.natEq x) = x :=
  prod_up_down T Rocq.SF.CbSyn.natEq x

theorem prod_nat_eqop (x y : Rocq.SF.CbSyn.carrier T) (n m : Nat) :
    Rocq.SF.CbSyn.eqop (Rocq.SF.CbSyn.prodEq.{a + 1, 0, r, r, r} T Rocq.SF.CbSyn.natEq)
      (Rocq.Corelib.Init.Datatypes.prod.pair _ Nat x n)
      (Rocq.Corelib.Init.Datatypes.prod.pair _ Nat y m) =
    Rocq.SF.CbSyn.eqop (Rocq.SF.CbSyn.prodEq.{a + 1, a + 1, r, r, r}
      (liftEq.{a + 1, 0, r} T) (liftEq.{0, a + 1, r} Rocq.SF.CbSyn.natEq))
      (Rocq.Corelib.Init.Datatypes.prod.pair _ _ (ULift.up x) (ULift.up n))
      (Rocq.Corelib.Init.Datatypes.prod.pair _ _ (ULift.up y) (ULift.up m)) := rfl
end natural

section subtype
variable (T : Type a) (P : T → Rocq.Corelib.Init.Datatypes.bool)
  (S : Rocq.SF.CbSyn.subT.{a, b, r} T P)

/-- The fixture's value projection, which is not exported by the two selected roots. -/
def subValue : Rocq.SF.CbSyn.ssort T P S → T :=
  Rocq.SF.CbSyn.subT.rec (motive := fun S => Rocq.SF.CbSyn.ssort T P S → T)
    (fun _ value _ => value) S

def liftSub : Rocq.SF.CbSyn.subT.{max a b, max a b, r}
    (ULift.{max a b} T) (fun x => P x.down) :=
  Rocq.SF.CbSyn.subT.SubPack _ _ (ULift.{max a b} (Rocq.SF.CbSyn.ssort T P S))
    (fun x => ULift.up (subValue T P S x.down))
    (fun x h => ULift.up (Rocq.SF.CbSyn.ssub T P S x.down h))

def subUp (x : Rocq.SF.CbSyn.ssort T P S) :
    Rocq.SF.CbSyn.ssort _ _ (liftSub T P S) := ULift.up x

def subDown (x : Rocq.SF.CbSyn.ssort _ _ (liftSub T P S)) :
    Rocq.SF.CbSyn.ssort T P S := x.down

theorem sub_down_up (x : Rocq.SF.CbSyn.ssort T P S) :
    subDown T P S (subUp T P S x) = x := rfl

theorem sub_up_down (x : Rocq.SF.CbSyn.ssort _ _ (liftSub T P S)) :
    subUp T P S (subDown T P S x) = x := rfl

theorem liftSub_value (x : Rocq.SF.CbSyn.ssort T P S) :
    subValue _ _ (liftSub T P S) (subUp T P S x) = ULift.up (subValue T P S x) := rfl

theorem liftSub_ssub (x : T) (h : P x = Rocq.Corelib.Init.Datatypes.bool.true) :
    Rocq.SF.CbSyn.ssub _ _ (liftSub T P S) (ULift.up x) h =
      subUp T P S (Rocq.SF.CbSyn.ssub T P S x h) := rfl
end subtype

/-- The exporter retains Rocq's option inductive; use this lossless view for Lean's Option.map. -/
def toOption {A : Type a} (x : Rocq.Corelib.Init.Datatypes.option A) : Option A :=
  Rocq.Corelib.Init.Datatypes.option.rec (fun x => some x) none x

def fromOption {A : Type a} : Option A → Rocq.Corelib.Init.Datatypes.option A
  | some x => Rocq.Corelib.Init.Datatypes.option.Some _ x
  | none => Rocq.Corelib.Init.Datatypes.option.None _

theorem fromOption_toOption {A : Type a} (x : Rocq.Corelib.Init.Datatypes.option A) :
    fromOption (toOption x) = x := by
  induction x with
  | Some x => rfl
  | None => rfl

theorem toOption_fromOption {A : Type a} (x : Option A) :
    toOption (fromOption x) = x := by
  cases x <;> rfl

section insertion
variable (T : Type a) (P : T → Rocq.Corelib.Init.Datatypes.bool)
  (S : Rocq.SF.CbSyn.subT.{a, b, r} T P)
  (h : Rocq.SF.CbSyn.insubT__rocq2lean_obligation_1.statement.{a, b, r})
  (hLift : Rocq.SF.CbSyn.insubT__rocq2lean_obligation_1.statement.{max a b, max a b, r})

/-- The operation correspondence in the generated option type, with both prerequisites explicit. -/
theorem insub_lift (x : T) :
    @RocqPending.SF.CbSyn.insubT.{max a b, max a b, r} hLift
      (ULift.{max a b} T) (fun x => P x.down) (liftSub T P S) (ULift.up x) =
    fromOption (Option.map (subUp T P S)
      (toOption (@RocqPending.SF.CbSyn.insubT.{a, b, r} h T P S x))) := by
  -- Abstract the dependent branch before eliminating the boolean. The prerequisite proofs
  -- are arbitrary; Lean's definitional proof irrelevance identifies their reflexive equalities.
  have commute (q : Rocq.Corelib.Init.Datatypes.bool)
      (make : q = Rocq.Corelib.Init.Datatypes.bool.true → Rocq.SF.CbSyn.ssort T P S) :
      Rocq.Corelib.Init.Datatypes.bool.rec
        (motive := fun t => q = t →
          Rocq.Corelib.Init.Datatypes.option (Rocq.SF.CbSyn.ssort _ _ (liftSub T P S)))
        (fun e => Rocq.Corelib.Init.Datatypes.option.Some _ (subUp T P S (make e)))
        (fun _ => Rocq.Corelib.Init.Datatypes.option.None _) q rfl =
      fromOption (Option.map (subUp T P S) (toOption
        (Rocq.Corelib.Init.Datatypes.bool.rec
          (motive := fun t => q = t → Rocq.Corelib.Init.Datatypes.option (Rocq.SF.CbSyn.ssort T P S))
          (fun e => Rocq.Corelib.Init.Datatypes.option.Some _ (make e))
          (fun _ => Rocq.Corelib.Init.Datatypes.option.None _) q rfl))) := by
    induction q with
    | true => rfl
    | false => rfl
  exact commute (P x) (Rocq.SF.CbSyn.ssub T P S x)

theorem insub_lift_map (x : T) :
    toOption (@RocqPending.SF.CbSyn.insubT.{max a b, max a b, r} hLift
      (ULift.{max a b} T) (fun x => P x.down) (liftSub T P S) (ULift.up x)) =
    Option.map (subUp T P S)
      (toOption (@RocqPending.SF.CbSyn.insubT.{a, b, r} h T P S x)) := by
  rw [insub_lift T P S h hLift x, toOption_fromOption]
end insertion

end CarrierCorrespondence
end

#print axioms CarrierCorrespondence.eq_down_up
#print axioms CarrierCorrespondence.eq_up_down
#print axioms CarrierCorrespondence.liftEq_eqop
#print axioms CarrierCorrespondence.prod_down_up
#print axioms CarrierCorrespondence.prod_up_down
#print axioms CarrierCorrespondence.prod_eqop
#print axioms CarrierCorrespondence.prod_nat_down_up
#print axioms CarrierCorrespondence.prod_nat_up_down
#print axioms CarrierCorrespondence.prod_nat_eqop
#print axioms CarrierCorrespondence.sub_down_up
#print axioms CarrierCorrespondence.sub_up_down
#print axioms CarrierCorrespondence.liftSub_value
#print axioms CarrierCorrespondence.liftSub_ssub
#print axioms CarrierCorrespondence.fromOption_toOption
#print axioms CarrierCorrespondence.toOption_fromOption
#print axioms CarrierCorrespondence.insub_lift
#print axioms CarrierCorrespondence.insub_lift_map

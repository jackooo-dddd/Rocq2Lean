import Rocq2LeanOut
/-!
Rule P correspondence (docs/PROP_LIFT.md §3), for the lift itself and for the synthetic fixture
`fixtures/stmt/plift` (`SF.Plift`) only. These are representation proofs about `PULift` and the
translated fixture declarations, not corpus proofs; checked without axioms by
tests/statement/check_prop_lift.py.
-/
namespace PropLiftCorrespondence

universe u a b c

/-! C1: `PULift.{u+1, 0} P ≃ P`, both round trips definitional (ι and structure η). -/

theorem toProp {P : Prop} (x : PULift.{u+1, 0} P) : P := x.down
def ofProp {P : Prop} (h : P) : PULift.{u+1, 0} P := PULift.up h

theorem toProp_ofProp {P : Prop} (h : P) : toProp (ofProp.{u} h) = h := rfl
theorem ofProp_toProp {P : Prop} (x : PULift.{u+1, 0} P) : ofProp (toProp x) = x := rfl

/-- The lifted type is inhabited exactly when the proposition holds. -/
theorem nonempty_iff {P : Prop} : Nonempty (PULift.{u+1, 0} P) ↔ P :=
  ⟨fun ⟨x⟩ => x.down, fun h => ⟨PULift.up h⟩⟩

/-! C3: no new collapse — the lifted type is a subsingleton (by its single constructor and Lean's
definitional proof irrelevance of the field), as `P` itself is. -/

theorem lift_subsingleton {P : Prop} (x y : PULift.{u+1, 0} P) : x = y := by
  cases x; cases y; rfl
theorem prop_subsingleton {P : Prop} (x y : P) : x = y := rfl

/-! C4: the lifted type is exactly at `Type u`, the image of the source sort `Type@{l}` (`l ↦ u`). -/

def liftAt (P : Prop) : Type u := PULift.{u+1, 0} P
theorem liftAt_eq (P : Prop) : liftAt.{u} P = PULift.{u+1, 0} P := rfl

/-! C2 on the fixture: each lifted position is the source proposition, transported along C1. -/

/-- `frel A B f a b := f b = a` (Prop at `Type@{l}`) is translated as that proposition, lifted. -/
theorem frel_eq (A : Type a) (B : Type b) (f : B → A) (x : A) (y : B) :
    Rocq.SF.Plift.frel.{a, b, c} A B f x y = PULift.{c+1, 0} (f y = x) := rfl

theorem frel_iff (A : Type a) (B : Type b) (f : B → A) (x : A) (y : B) :
    Nonempty (Rocq.SF.Plift.frel.{a, b, c} A B f x y) ↔ f y = x := nonempty_iff

theorem R_iff (x y : Nat) : Nonempty (Rocq.SF.Plift.R.{c} x y) ↔ y.succ = x := nonempty_iff

/-- The lift adds no dependence on the universe level: every instance states the same proposition. -/
theorem R_level_indep (x y : Nat) :
    Nonempty (Rocq.SF.Plift.R.{a} x y) ↔ Nonempty (Rocq.SF.Plift.R.{b} x y) :=
  (R_iff x y).trans (R_iff x y).symm

/-- A lifted obligation statement (`r2`'s proof at `pick`'s argument of type `R 1 0`) states the
proposition that `R 1 0` lifts (§3.3: the head chain `R`, `frel` δβ-inlined). -/
theorem r2_obligation_lifted :
    Rocq.SF.Plift.r2__rocq2lean_obligation_1.statement ↔ Nonempty (Rocq.SF.Plift.R.{c} 1 0) :=
  (R_iff 1 0).symm

/-- `PULift.up` at a use (`r1 : R 1 0 := ⟨h⟩`) followed by `down` gives back the proof. -/
theorem r1_down (h : Rocq.SF.Plift.r1__rocq2lean_obligation_1.statement) :
    (@RocqPending.SF.Plift.r1.{c} h).down = h := rfl

/-- The transported definitions compute as their sources: `r2 = pick 1 0 _ = 0`, and `dmatch`'s match
on the lowered equation (`PULift.down h`) reduces to its branch. -/
theorem r2_value (h : Rocq.SF.Plift.r2__rocq2lean_obligation_1.statement) :
    @RocqPending.SF.Plift.r2 h = 0 := rfl

theorem dmatch_value (n : Nat) (h : Rocq.SF.Plift.R.{c} n.succ n) :
    Rocq.SF.Plift.dmatch.{c} n.succ n h = n := rfl

end PropLiftCorrespondence

#print axioms PropLiftCorrespondence.toProp_ofProp
#print axioms PropLiftCorrespondence.ofProp_toProp
#print axioms PropLiftCorrespondence.nonempty_iff
#print axioms PropLiftCorrespondence.lift_subsingleton
#print axioms PropLiftCorrespondence.liftAt_eq
#print axioms PropLiftCorrespondence.frel_eq
#print axioms PropLiftCorrespondence.frel_iff
#print axioms PropLiftCorrespondence.R_level_indep
#print axioms PropLiftCorrespondence.r2_obligation_lifted
#print axioms PropLiftCorrespondence.r1_down
#print axioms PropLiftCorrespondence.r2_value
#print axioms PropLiftCorrespondence.dmatch_value

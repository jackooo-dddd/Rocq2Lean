import Rocq2LeanOut
/-!
R-SPLIT correspondence (fixture only; docs/LEVEL_SPLIT.md §3). Synthetic proofs about the fixture's
own translated declarations — never corpus proofs.

An off-diagonal instance of a split declaration (copies at independent levels `a, b, c`) is
isomorphic to the *diagonal* instance at `m = max a b c` (every copy at one level: the source
declaration, `Rocq.SF.Split.pR` at the source's single level) applied to the `ULift`ed arguments —
Lean's explicit form of Rocq's cumulativity `Type@{a} ≤ Type@{m}`. So the split view accepts exactly
the instances Rocq accepts, up to that lifting, and adds no other inhabitants.
-/
noncomputable section
namespace SplitCorrespondence


universe a b c r

section ind
variable {A : Type a} {C : Type b} (R : A → C → Type c)

/-- The relation on the lifted carriers (the diagonal's third argument). -/
abbrev liftR : ULift.{max a b c} A → ULift.{max a b c} C → Type (max a b c) :=
  fun x y => ULift.{max a b c} (R x.down y.down)

def up (x : Rocq.SF.Split.pR.{a, b, c, r} A C R) :
    Rocq.SF.Split.pR.{max a b c, max a b c, max a b c, r} (ULift.{max a b c} A) (ULift.{max a b c} C) (liftR R) :=
  Rocq.SF.Split.pR.rec (motive := fun _ => Rocq.SF.Split.pR.{max a b c, max a b c, max a b c, r} (ULift.{max a b c} A) (ULift.{max a b c} C) (liftR R))
    (Rocq.SF.Split.pR.pR_nil _ _ _) (fun a1 a2 h _ ih => Rocq.SF.Split.pR.pR_cons _ _ _ ⟨a1⟩ ⟨a2⟩ ⟨h⟩ ih) x

def down (y : Rocq.SF.Split.pR.{max a b c, max a b c, max a b c, r} (ULift.{max a b c} A) (ULift.{max a b c} C) (liftR R)) :
    Rocq.SF.Split.pR.{a, b, c, r} A C R :=
  Rocq.SF.Split.pR.rec (motive := fun _ => Rocq.SF.Split.pR.{a, b, c, r} A C R)
    (Rocq.SF.Split.pR.pR_nil _ _ _) (fun a1 a2 h _ ih => Rocq.SF.Split.pR.pR_cons _ _ _ a1.down a2.down h.down ih) y

theorem down_up (x : Rocq.SF.Split.pR.{a, b, c, r} A C R) : down R (up R x) = x := by
  induction x with
  | pR_nil => rfl
  | pR_cons a1 a2 h t ih => exact congrArg (Rocq.SF.Split.pR.pR_cons A C R a1 a2 h) ih

theorem up_down (y : Rocq.SF.Split.pR.{max a b c, max a b c, max a b c, r} (ULift.{max a b c} A) (ULift.{max a b c} C) (liftR R)) :
    up R (down R y) = y := by
  induction y with
  | pR_nil => rfl
  | pR_cons a1 a2 h t ih => exact congrArg (Rocq.SF.Split.pR.pR_cons _ _ (liftR R) a1 a2 h) ih
end ind

section defn
universe e f g
variable {A1 : Type a} {A2 : Type b} (AR : A1 → A2 → Type c) {B1 : Type e} {B2 : Type f}
  (BR : B1 → B2 → Type g) (f1 : A1 → B1) (f2 : A2 → B2)

def fup (h : Rocq.SF.Split.fun_R.{a, b, c, e, f, g} A1 A2 AR B1 B2 BR f1 f2) :
    Rocq.SF.Split.fun_R.{max a b c, max a b c, max a b c, e, f, g} (ULift.{max a b c} A1) (ULift.{max a b c} A2)
      (fun x y => ULift.{max a b c} (AR x.down y.down)) B1 B2 BR (fun x => f1 x.down) (fun x => f2 x.down) :=
  fun x y r => h x.down y.down r.down

def fdown (h : Rocq.SF.Split.fun_R.{max a b c, max a b c, max a b c, e, f, g} (ULift.{max a b c} A1) (ULift.{max a b c} A2)
      (fun x y => ULift.{max a b c} (AR x.down y.down)) B1 B2 BR (fun x => f1 x.down) (fun x => f2 x.down)) :
    Rocq.SF.Split.fun_R.{a, b, c, e, f, g} A1 A2 AR B1 B2 BR f1 f2 :=
  fun x y r => h ⟨x⟩ ⟨y⟩ ⟨r⟩

theorem fdown_fup (h : Rocq.SF.Split.fun_R.{a, b, c, e, f, g} A1 A2 AR B1 B2 BR f1 f2) : fdown AR BR f1 f2 (fup AR BR f1 f2 h) = h := rfl
theorem fup_fdown h : fup AR BR f1 f2 (fdown AR BR f1 f2 h) = h := rfl
end defn

end SplitCorrespondence
end

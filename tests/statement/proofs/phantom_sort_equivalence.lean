import Rocq2LeanOut
/-!
Rule Q-a equivalence (docs/PHANTOM_SORT.md §4), for the synthetic fixture `fixtures/stmt/phant`
(`SF.Phant`, HB's `unify` shape) only. Representation proofs about translated fixture declarations,
not corpus proofs; checked without axioms by tests/statement/check_phantom_sort.py.

The lowering replaces the sort arguments of a phantom check by the types of their values. Every
instance of a phantom check holds (phantom's constructor), so any two instances, at any sort
arguments, are equivalent propositions: a hypothesis of a lowered check is neither weaker nor stronger
than the source's.
-/
namespace PhantomSortEquivalence

universe a b c d k

/-- Every phantom proposition holds. -/
theorem phantom_holds {T : Type k} (t : T) : Rocq.Corelib.ssr.ssreflect_rw.phantom.{k} T t :=
  Rocq.Corelib.ssr.ssreflect_rw.phantom.Phantom T t

/-- Every instance of the phantom check holds, whatever its sort arguments and values. -/
theorem unify_holds (T1 : Type a) (T2 : Type b) (t1 : T1) (t2 : T2) (s : Nat) :
    Rocq.SF.Phant.unify.{a, b} T1 T2 t1 t2 s := fun _ => phantom_holds t2

/-- Any two instances are equivalent: in particular the source's check at one common sort (here
`Type c`, both carriers at `c`) and the lowered check at the carriers' own sorts. -/
theorem unify_equiv (T1 : Type a) (T2 : Type b) (t1 : T1) (t2 : T2) (s : Nat)
    (U1 : Type c) (U2 : Type d) (u1 : U1) (u2 : U2) (s' : Nat) :
    Rocq.SF.Phant.unify.{a, b} T1 T2 t1 t2 s ↔ Rocq.SF.Phant.unify.{c, d} U1 U2 u1 u2 s' :=
  ⟨fun _ => unify_holds U1 U2 u1 u2 s', fun _ => unify_holds T1 T2 t1 t2 s⟩

/-- The lowered hypothesis of `chk_stmt` (sorts `Type a`, `Type b`) is equivalent to the source's
(common sort `Type (max a b)`, at which both carriers can be lifted): the statement assumes nothing more
or less than the source does. -/
theorem chk_hyp_equiv (A : Type a) (B : Type b) (s : Nat) :
    Rocq.SF.Phant.unify.{a+1, b+1} (Type a) (Type b) A B s ↔
      Rocq.SF.Phant.unify.{max a b + 1, max a b + 1} (Type (max a b)) (Type (max a b))
        (ULift.{max a b} A) (ULift.{max a b} B) s :=
  unify_equiv _ _ _ _ _ _ _ _ _ _

/-- The lowered statement does not depend on the hypothesis' proof: it holds for one proof iff for all. -/
theorem chk_stmt_hyp_irrelevant (A : Type a) (B : Type b)
    (h h' : Rocq.SF.Phant.unify.{a+1, b+1} (Type a) (Type b) A B (Nat.succ Nat.zero)) :
    Rocq.SF.Phant.chk.{a, b} A B h = Rocq.SF.Phant.chk.{a, b} A B h' := rfl

/-- The lowered statement's hypothesis can always be discharged. -/
theorem chk_hyp_dischargeable (A : Type a) (B : Type b) (s : Nat) :
    Rocq.SF.Phant.unify.{a+1, b+1} (Type a) (Type b) A B s := unify_holds _ _ _ _ _

end PhantomSortEquivalence

#print axioms PhantomSortEquivalence.phantom_holds
#print axioms PhantomSortEquivalence.unify_holds
#print axioms PhantomSortEquivalence.unify_equiv
#print axioms PhantomSortEquivalence.chk_hyp_equiv
#print axioms PhantomSortEquivalence.chk_stmt_hyp_irrelevant
#print axioms PhantomSortEquivalence.chk_hyp_dischargeable

import Rocq2LeanOut
/-!
Rule T correspondence (docs/COINDUCTIVE.md §4), for the synthetic fixture `fixtures/stmt/coind`
(`SF.Coind`, Classic's `Task_T` shape) only. Representation proofs about translated fixture declarations,
not corpus proofs; checked without axioms by tests/statement/check_coinductive.py. The Rocq side of T1
(`Task_T_eta`, every inhabitant of the coinductive type is a constructor application) is proved by Rocq in
the fixture itself.
-/
noncomputable section
namespace CoinductiveCorrespondence

/-- T1: the translated type is exactly the record of its four fields (both round trips hold). -/
def toTuple (x : Rocq.SF.Coind.Task_T) : Nat × Nat × Nat × Nat :=
  Rocq.SF.Coind.Task_T.rec (motive := fun _ => Nat × Nat × Nat × Nat) (fun a b c d => (a, b, c, d)) x

def ofTuple (p : Nat × Nat × Nat × Nat) : Rocq.SF.Coind.Task_T :=
  Rocq.SF.Coind.Task_T.build_task p.1 p.2.1 p.2.2.1 p.2.2.2

theorem ofTuple_toTuple (x : Rocq.SF.Coind.Task_T) : ofTuple (toTuple x) = x :=
  Rocq.SF.Coind.Task_T.rec (motive := fun x => ofTuple (toTuple x) = x) (fun _ _ _ _ => rfl) x

theorem toTuple_ofTuple (p : Nat × Nat × Nat × Nat) : toTuple (ofTuple p) = p := rfl

/-- T1, Lean side: the translated statement of the source's (Rocq-proved) η lemma holds. -/
theorem Task_T_eta_holds : Rocq.SF.Coind.Task_T_eta.statement := fun x =>
  Rocq.SF.Coind.Task_T.rec (motive := fun x => x = Rocq.SF.Coind.Task_T.build_task (Rocq.SF.Coind.get_P x)
      (Rocq.SF.Coind.get_C x) (Rocq.SF.Coind.Task_T.rec (motive := fun _ => Nat) (fun _ _ c _ => c) x)
      (Rocq.SF.Coind.Task_T.rec (motive := fun _ => Nat) (fun _ _ _ d => d) x))
    (fun _ _ _ _ => rfl) x

/-- T2: the eliminations compute as in the source (ι), e.g. the translated `get_P_build` holds by
reduction. -/
theorem get_P_build_holds : Rocq.SF.Coind.get_P_build.statement := fun _ _ _ _ => rfl

end CoinductiveCorrespondence
end

#print axioms CoinductiveCorrespondence.ofTuple_toTuple
#print axioms CoinductiveCorrespondence.toTuple_ofTuple
#print axioms CoinductiveCorrespondence.Task_T_eta_holds
#print axioms CoinductiveCorrespondence.get_P_build_holds

# Rule T: non-recursive coinductive types as inductive types

Status: **adopted** (proposed and approved 2026-10-15; ITERATION_LOG entry 16). Implementation:
`nonRecursiveBlock` (`Rocq2Lean/Translate.lean`), the block emission (`Rocq2Lean/Emit.lean`), and the
independent audit check `check_coinductive` (`tools/audit.py`). Test: `scripts/test-coinductive`.

## 1. Measured frontier

Classic's `prosa.classic.implementation.uni.basic.extraction_tdma.Task_T` is the corpus's only coinductive
type (COINDUCTIVE, `UNSUPPORTED_FEATURE: coinductive type`). It blocks **13 protected roots**, every
protected declaration of `extraction_tdma`, `Task_T` itself included, and nothing else.

```
CoInductive Task_T : Set := build_task : nat -> nat -> nat -> nat -> Task_T.
```

How its 12 dependents use it (measured on the S9 export):

| Use | Declarations |
|---|---|
| `match` on `Task_T`, non-dependent, into `nat` (field projections) | `get_slot`, `get_D`, `get_P`, `get_cost` |
| no match on `Task_T` (lists of tasks, `fix` over `list`, `bool` matches) | `In`, `cycle`, `schedulable_tsk`, `schedulability_test`, `schedulability_tdma`, `task_eq` |
| statements | `schedulability_tdma_valid`, `schedulability_test_valid` |

No `cofix` occurs anywhere in the export (0 declarations).

## 2. Why a general coinductive encoding is not needed here

`Task_T` is **non-recursive**: no constructor argument mentions `Task_T`. Its functor is the constant
`F X = nat × nat × nat × nat`, whose least and greatest fixed points coincide. The type is a record of four
naturals, declared with `CoInductive`. No infinite value exists. A general encoding of coinductive types in
Lean (M-types, streams as functions, quotient-based final coalgebras) would be needed for a *recursive*
coinductive. The corpus has none, so the proposal is deliberately restricted to the non-recursive case.

## 3. The proposed rule T

A coinductive block is translated as the Lean inductive with the same parameters, indices, constructors
and universe rule (M3a), when all of the following hold. The conditions are recomputed from the source by
the translator and, independently, by the audit:

1. **single body, not mutual**;
2. **non-recursive**: no constructor argument type mentions a type of the block;
3. **no `cofix`** in any accepted declaration that mentions the block. A `cofix` of a non-recursive type
   has no guarded recursive call, so its body is the value; but Rocq does not unfold it outside a match.
   It stays refused, as today, so no definitional surplus arises from it.

The row reports `coinductive_as_inductive: true`. The audit accepts the Lean inductive for a `CoFinite`
source block only with this flag and under conditions 1–2 (recomputed; constructor arguments are stored
innermost first, so `args[k]` lies under the parameters and `len(args) − 1 − k` earlier arguments), and
rejects the flag on any other block. Condition 3 holds because the term translation refuses every `cofix`.
Before rule T, the audit had no check on a block's kind (the translator refused every coinductive); it now
checks it for every claimed block.

## 4. Correspondence obligations

| | Obligation | How it would be discharged |
|---|---|---|
| T1 | **Same carrier.** The source type and the target inductive have the same constructor with the same fields, and every inhabitant is a constructor application: in Rocq, `∀ x : Task_T, x = let 'build_task a b c d := x in build_task a b c d` (by `destruct`, propositional); in Lean, structure η (definitional). | A synthetic Rocq fixture (`CoInductive` of the same shape) with that lemma proved in Rocq (tests only), and the Lean counterpart; both types are shown isomorphic to `nat × nat × nat × nat` with both round trips. |
| T2 | **Eliminations.** Rocq's `match` on the coinductive (ι: `match build_task a b c d with build_task x y z w => t` ↦ `t[a,b,c,d]`) is translated by the existing M3b lowering to `Task_T.rec`, with the same ι rule. Lean's recursor is dependent: a superset of Rocq's (dependent) case analysis on a coinductive. | The kernel; the audit's existing case checks (unchanged). |
| T3 | **No definitional surplus that changes a statement.** Lean adds definitional η for the one-constructor type, which Rocq has only propositionally (T1). Extra definitional equalities do not change which proposition a structurally translated statement denotes, since it is equal in Rocq by T1. No `cofix` is admitted (condition 3), so no ν-unfolding surplus arises. | Argument above; the audit checks condition 3. |
| T4 | **Universes and positivity.** As for any inductive (R2T/R5): `Task_T : Set` becomes `Type`, and positivity is checked by Lean's kernel (trivial: non-recursive). | Existing checks. |
| T5 | **Protected interfaces.** `Task_T` is protected. Its interface (`Task_T : Set`, `build_task : nat → nat → nat → nat → Task_T`) is translated unchanged; only the fixed-point kind differs, which is unobservable for a non-recursive type (T1). | The protection listing names the row (`coinductive_as_inductive`). |

## 5. Negative controls (`scripts/test-coinductive`, fixture `fixtures/stmt/coind`)

* a recursive coinductive (a stream) stays refused;
* a non-recursive coinductive with a `cofix` in a dependent stays refused;
* a forged row claiming the flag on a recursive block is audit-rejected;
* a forged row translating a coinductive without the flag is audit-rejected, as today.

In the test: the recursive `stream` refused and its cofixpoint not claimed; a non-recursive cofixpoint
refused; forged rows (`Task_T` without the flag, an inductive with it) audit-rejected; unit controls on the
audit criterion. The first fixture run caught a wrong argument-order assumption in both copies (the
recursive `stream` was accepted); fixed before anything was committed.

## 6. Correspondence proofs

`tests/statement/proofs/coinductive_correspondence.lean` (axiom-free): the translated `Task_T` is
isomorphic to `Nat × Nat × Nat × Nat` (both round trips), the translated statement of the Rocq-proved η
lemma holds (T1, Lean side; the Rocq side is proved by Rocq in the fixture), and the eliminations compute
as in the source (T2).

## 7. Decision

Approved 2026-10-15: non-recursive coinductive types translated as Lean inductive types, with T1–T5.
Expected effect: the 13 protected roots of `extraction_tdma`. Recursive coinductive types remain refused;
the corpus has none.

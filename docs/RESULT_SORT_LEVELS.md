# R3G-F: result-sort-only levels of field references (experimental rule)

Status: approved for controlled development on 2026-10-14 (the result-sort-only universe family);
developed on branch `rules-rsonly`; reviewed and merged into `main` on 2026-10-14 (ITERATION_LOG
entry 10). Case B (§1) is not covered and stays blocked pending a representation decision.

## 1. The cases, distinguished on source and target terms

STATEMENT_FREE_LEVEL_PINNED has 356 member rows in the R-SPLIT run. Each was classified
mechanically by where the pinned level occurs in the referenced declaration's source
(`scratchpad pin_classify.py`; evidence in `reports/statement_only/rsonly/`):

| Case | Rows | Pinned level |
|---|---|---|
| **A: result-sort-only** | 280 | `eqtype.hasDecEq.axioms_ (T : Type@{29}) : Type@{32}`: level 32 (144 rows); `choice.hasChoice.axioms_`: level 299 (136 rows) |
| **B: carrier (a field sort)** | 58 + 18 | `Equality.type`'s `sort : Type@{51}` (50); `Countable.type` 959 (5); `Choice.type` 333 (3); `JobType`/`TaskType` (`:= Equality.type`) (18) |

**Case A mechanism.** Take the reproducer `Builders_32.HB_unnamed_factory_34` obligation 5:

```
∀ d (T : Type@{4444}) (m : hasDecEq.axioms_ T), unify (Equality.axioms_ T) … (Equality.axioms_.Class T m) …
```

* `Equality.axioms_`'s field is `hasDecEq.axioms_ T`.
* Level 32 is not a level of `Equality.axioms_`'s own source, and no argument determines it. The
  existing minimal-level rule for inductives (R3″) therefore fixed it to 0:
  `Class : (T : Type u51) → hasDecEq.axioms_.{u51, 0} T → …`.
* The statement's binder `m : hasDecEq.axioms_.{_, ?32} T` must then unify `?32 := 0`, and C-1
  (generality) refuses that, correctly.

**Case B mechanism (not covered by this rule).** Take `prod_eqType SporadicTask nat_eqType` in a Classic
statement.
* `nat_eqType` is `Equality.type.{0, …}`, because it packs `Nat : Type 0`.
* `prod_eqType` takes both operands at one carrier level, so the generic `SporadicTask`'s carrier is
  forced to 0.
* In Rocq, `Equality.type` is one monomorphic type that already contains `nat` by cumulativity
  inside `Pack`.
* A faithful Lean form would need a different representation: either a lifted carrier for concrete
  instances (`ULift Nat`, with transport at every use of `sort`), or per-operand carrier levels for
  structure operations. That is a semantic policy decision, so case B stays blocked.

The 751 protected roots blocked by STATEMENT_FREE_LEVEL_PINNED + SOLUTION_FACT_VIOLATED are blocked
through case B (`HB_unnamed_mixin_107`, `Countable.type`'s carrier) and two solution-fact rows
(`eqtype.insub`, `fintype.HB_unnamed_factory_57`). Case A lies on the dependency frontier of 79
protected roots, all of which are also blocked by B, solution facts or kernel failures.

## 2. The rule (R3G-F)

**Applicability.** The rule is derived mechanically in `processInductive`'s discovery pass and in
`Split.resultOnlyLevels`. A level metavariable `σ` qualifies when it:
* occurs only in the *constructor fields* of a non-template, single-body block (not in its arity);
* is the argument, at every one of its references, for the same source level `l`;
* where `l` is **result-sort-only** in each referenced declaration, meaning every occurrence of `l` in
  that declaration's source is in its result sort (the arity's final sort or the body's `sort`), or
  `l` is one of that declaration's own R3G-F levels.

The level `l` is then taken when it:
* is not a level of the block's source;
* is not a template level;
* is bounded by the block: the native facts entail `l ≤ s` for a level `s` of the block's source
  result sort (in Rocq the field fits the block's sort).

No HB name, error message or whitelist is involved.

**Representation.** `l` becomes an implicit universe parameter `u_l` of the block, alongside the
existing R3G implicit levels.
* **Minimal reading.** In every R2F interpretation, an R3G-F level is read *minimally*: `ι l = u_l`. It
  is not raised by the levels below it (its lower bounds, such as `51 ≤ 32`), but it still raises the
  levels above it. For example `Equality.axioms_` reads its own level 55 as `max(u55, u32, u51)`, its
  field is `hasDecEq.axioms_.{u51, u32} T`, and its arity is `Type u51 → Type (max u32 u51 u55)`.
* **Why minimal.** This is R-SPLIT's principle (approved): the parameter stands for an argument `a ≤ l`,
  R3-checked at every use, and lower bounds need not hold for arguments. It admits no new kind of
  instance: the previous representation's `hasDecEq.axioms_.{u51, 0}` was already one.
* **Scope.** A level is read minimally in a declaration only where it is *implicit* there (not a level
  of the declaration's own source) and is an R3G-F level of a block in the declaration's **dependency
  closure** (`rsClosure` / audit `RS_CLOSURE`). This makes the reading depend only on what the
  declaration depends on, never on unrelated blocks or translation order.

Only one occurrence is represented differently: a result-sort-only level of a referenced declaration,
at a universe argument in a constructor field. Its argument is now `u_l` instead of R3″'s `0`. Nothing
else changes:
* no binder range: the arity's parameter and index domains, and every field's own sort, are untouched;
* no source fact (no fact is added or weakened; the minimal reading omits lower bounds from the
  interpretation only);
* no constructor or projection.

There is **no lifting and no transport**. Field types are the source's field types at parameterized
levels. The previous translation is the instance `u_l := 0`. So no conversion is needed at uses:
projections, recursors and dependent eliminations are the kernel-generated ones of the generalized
block. The fixture exercises them with `getop` (projections), `pack_eta` (dependent elimination) and
`mk_op` (a constructed instance).

**Applicability at constants.** At a reference to a constant (for example the projection
`Finite.sort`), a level counts as result-sort-only when it is an R3G-F level of the constant's
dependency closure and not a level of its own source: it reaches the constant only through such
blocks. Without this, `ProcessorState`'s field `Core : Finite.type` defaulted `Finite.type`'s new levels
to 0, and the protected range was correctly refused.

**Development history (corpus-measured).**
* v1 (`6ff07a7`): R2F-read R3G-F levels put `max` expressions in argument positions everywhere; a
  validated but severe regression (549 / 593 / 3,128 / 204).
* v2–v3 (`c77696c`, `2200033`): minimal reading; v3 left one direct regression, the protected
  `ProcessorState`, through global order-dependent minimality.
* v4 (`6fe8890`): dependency-closure scope plus applicability at constants.

**References.** An argument for `u_l` at a use is R3-checked like any implicit level: it is at most `l`
in the source graph, or it is `u_l` / `ι l` when the use shares `l`. A statement mentioning both the
mixin and the class (case A) now has one class for the mixin's level, generic in `u_l`.

**Boundaries and what remains unsupported.**
* Single-body, non-template blocks only.
* Levels that occur only in the arity keep the existing R3G rule.
* A field's *carrier* level is still R3″ (0); this is case B, for example the fixture's `holder`,
  which is kernel-rejected before and after the rule.
* A block whose parameter's type is a generalized structure reads the structure's new levels through
  that structure's interpretation. `wrapA (e : typeE)` gets `typeE.{u23, u23, u23, u23+1}`, the mixin
  level at the carrier level. That is R3-admissible (`51 ≤ 32`) and definitionally the old form. A
  statement that needs `e` at a *higher* mixin level than its carrier would pin it. Any such
  regression is measured on the corpus, not assumed absent.

## 2b. A separate mechanism: P2 retry tier for definitions

This is not part of R3G-F. It has its own reproducer: the fixture's `pr1`, MathComp `eqtype.pred1`'s
shape.
* **Problem.** A definition that unifies two references at R2F-read arguments
  (`max ?a X = max ?b X`) was accepted only by defaulting its levels (`pred1`, and through it
  `fintype.finite_axiom`).
* **Retry.** Such a definition is retried with the existing statement-mode P2 joint identification and
  the M6 bounded solver (`?a := ?b`: both references at one instance, as in the source).
* **Guards.** The retry is kept only when the kernel accepts it with fewer defaulted levels, *and*
  every universe parameter it adds occurs in the definition's type. A parameter occurring only in the
  value, such as `ssrnat.leq`'s, would be undetermined at every use: inside `fintype.ordinal` it pinned
  dependent statements.
* **Policy basis.** Within existing approved rules (P2, entry 7; M6 solver); the kernel and the audit's
  R3 and generality checks apply unchanged.

## 2c. Attribution (ablation, ITERATION_LOG entry 10)

The full corpus was run at `6fe8890` with the P2 retry tier disabled and everything else unchanged
(run `r2l-run-RS4abl`, uncommitted measurement patch; validated):

| Run | Accepted | Audited Pending | Blocked | Direct Failure | Rows gained over R-SPLIT |
|---|---|---|---|---|---|
| R-SPLIT baseline | 673 | 2,177 | 1,518 | 106 | |
| R3G-F only (ablation) | 673 | 2,177 | 1,518 | 106 | 276 (internal), 0 protected |
| R3G-F + P2 retry tier | 673 | 2,180 | 1,518 | 103 | 279 (3 protected) |

* **R3G-F** solves 276 internal rows: exactly 144 `hasDecEq.axioms_` and 132 `hasChoice.axioms_`
  case-A pins. It adds **zero protected roots on its own**, because every protected path through case A
  is also blocked by case B or by structure-carrier solution-fact failures.
* **The P2 retry tier for definitions** is responsible for the **three** newly supported protected
  roots, all previously refused by coherence:
  * `delay_propagation.propagated_arrival_curve_valid`;
  * `delay_propagation.propagated_arrival_curve_respected`;
  * `task_intra_interference_bound.instantiated_task_intra_interference_is_bounded`.
* Neither change loses a claimed row.

## 3. Independent checks

* **Audit** (`check_result_sort_implicit`, statement and proof mode, counter
  `result_sort_implicit_checked`). For every reported level it checks independently that the level:
  1. is an implicit level, not a level of the block's source, of a single-body non-template block;
  2. is result-sort-only in a declaration referenced by a constructor field. This is recomputed from
     that declaration's source by occurrence paths (`result_only_levels`), or the level is that
     declaration's own checked R3G-F level;
  3. is bounded by the block's source result sort in the native graph;
  4. occurs in no binder domain of the arity, and as a sort nowhere in a constructor type.

  Its R2F copy (`own_level_interp`) applies the same minimal reading, scoped by the same dependency
  closure (`RS_CLOSURE`, recomputed from the source dependency lists in source order). Its applicability
  test at constants (`ro_of`) is recomputed from the source as well.

  The existing checks apply on top of these: the implicit level must be the argument (its
  interpretation) of a reference for it, R3 holds at every reference, the structural comparison with
  the source holds, and generality holds.
* **Consumer** (`resultImplicitOk`, detector `levels`): on the imported inductive alone, the
  parameter occurs in no binder domain of the arity but does occur in its final sort, and occurs as a
  sort in no constructor type.
* **Negative controls** (`tests/statement/check_result_sort.py`): each is accepted by the kernel and
  rejected by the independent checks.

  | Forged change | Rejected by |
  |---|---|
  | A genuine carrier level claimed as result-sort-only (`wrapA`) | audit, consumer |
  | A field at a level that is not its interpretation (`axE`) | audit |
  | A carrier range raised by the new level (`typeE`'s `sort` field; dependents fail to replay, as expected) | audit, consumer |
  | A dependent use narrowed, the mixin level fixed in `unify_like` | audit |

* **Positive controls:**
  * the fixture (`axE`, `typeE`, `unify_like`, `mk_op`);
  * the real `Equality.axioms_` and `Equality.type`;
  * the real obligation 5, accepted and also instantiated at nonzero universes through the kernel.

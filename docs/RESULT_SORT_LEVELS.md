# R3G-F: result-sort-only levels of field references (experimental rule)

Status: **experimental**, branch `rules-rsonly`. The rule was approved for controlled development on
2026-10-14 (the result-sort-only universe family). It is not merged until the implementation, its
validation boundaries and the full-corpus results are reviewed. See ITERATION_LOG entry 10.

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
existing R3G implicit levels. The block's levels are read through the existing R2F interpretation,
which now includes `l`. For example `Equality.axioms_`: its own level 55 is read as
`max(u55, u32, u51)`, its field is `hasDecEq.axioms_.{u51, ι 32} T`, and its arity is
`Type u51 → Type (max u32 u51 u55)`.

Only one occurrence is represented differently: a referenced declaration's result-sort-only level, at
a universe argument in a constructor field. Its argument is now `ι l` instead of R3″'s `0`. Nothing
else changes:
* no binder range: the arity's parameter and index domains, and every field's own sort, are
  untouched;
* no source fact: the R2F interpretation reads the native facts, unchanged;
* no constructor or projection.

There is **no lifting and no transport**. Field types are the source's field types, at the
interpretation of their source levels, as for any other level of a monomorphic declaration (R2T/R2F).
The previous translation is literally the instance `u_l := 0`, because `ι l` at `u_l := 0` is the old
argument. So no conversion is needed at uses: projections, recursors and dependent eliminations are
the kernel-generated ones of the generalized block. They are exercised by the fixture's `getop`
(projections), `pack_eta` (dependent elimination) and `mk_op` (a constructed instance).

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

## 3. Independent checks

* **Audit** (`check_result_sort_implicit`, statement and proof mode, counter
  `result_sort_implicit_checked`). For every reported level it checks independently that the level:
  1. is an implicit level, not a level of the block's source, of a single-body non-template block;
  2. is result-sort-only in a declaration referenced by a constructor field. This is recomputed from
     that declaration's source by occurrence paths (`result_only_levels`), or the level is that
     declaration's own checked R3G-F level;
  3. is bounded by the block's source result sort in the native graph;
  4. occurs in no binder domain of the arity, and as a sort nowhere in a constructor type.

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

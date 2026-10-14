# R-SPLIT: one source level shared by several parameter sorts

Status: approved as a controlled translation-rule extension (Option A, 2026-10-14); developed on
branch `rules-split`, reviewed and merged into `main` (2026-10-14) after the semantic correspondence
and the full-corpus results (ITERATION_LOG entry 9).

## 1. The problem

A monomorphic Rocq declaration may use one global level `l` as the sort of several parameter
binders. CoqEAL's parametricity relations are the corpus instances:

```
Inductive list_R (A1 A2 : Type@{190}) (A_R : A1 -> A2 -> Type@{190}) : list A1 -> list A2 -> Type@{381}
```

Rocq's cumulativity lets every use instantiate each parameter with a type at its *own* level `a ≤ l`
(`list_R A C R` with `A : Type@{a}`, `C : Type@{c}`, `a ≠ c`). A Lean translation with one universe
parameter `u_l` forces all of those arguments to one level, so every statement that uses
`list_R` at carriers of independent levels identifies them, which narrows the statement. P1 refuses
such statements (COUPLED_BINDER_LEVELS). Nothing in the source forces the identification.

## 2. The rule

**Eligibility.** The translator (`Rocq2Lean/Split.lean`) and the auditor (`level_split_view` in
`tools/audit.py`) derive it independently, each from the source declaration alone. A source level `l`
of a monomorphic declaration is eligible when both of the following hold:

* `l` is the final sort (`∀ …, Sort l`, possibly `max(l, …)`) of the type of at least two parameter
  binders, and those binder types mention `l` nowhere else. For a constant, "parameter binder" means
  the type's binder and the body's λ at the same position. For a single-body, non-template inductive,
  it means the arity's binder, the parameter context's entry and every constructor's binder at that
  position.
* Every other occurrence of `l` in the whole exported declaration is in the declaration's final
  result sort. That includes bodies, constructor arguments and indices, projections, universe
  instances, primitive data and native metadata. For an inductive, the arity's final sort and the
  body's `sort` count as the result sort.

The translator counts occurrences. The auditor compares sets of JSON paths at which the level's name
occurs. Only a level that every occurrence can be separated from is split. A level that occurs
anywhere else must stay related to that occurrence, so it is never split.

**Split view.** Each group binder `i` gets a fresh copy `l__s<i>`. Each copy is its own universe
parameter, `u_<l>__s<i>`. A result-sort occurrence of `l` becomes the join `max(l__s<i>, …)` of the
copies. Nothing else changes. The declaration is then translated by the existing rules, with the
kernel checking it as usual. The split view is kept only if the kernel accepts it *and every copy
stays a universe parameter*: a copy that is solved or defaulted (the residual-default path of
definitions) makes the split degenerate. Otherwise the declaration is translated unsplit, exactly as
before (`translateSplit` in `Rocq2Lean/Emit.lean`). The report field `level_split` lists
`{level, params, copies}`. Copy names depend only on `(l, i)`, so two split declarations that share
`l` at the same position share a copy name. Both copies range over the same levels.

**Facts.** A copy lies below its level (`l__s<i> ≤ l`): it stands for an argument `a ≤ l`, and R3
checks `a ≤ l` at every use. A copy also inherits the *upper* bounds of `l` (`l ≤ m` and `l < m`
become `l__s<i> ≤ m` and `l__s<i> < m`). It never inherits a lower bound (`k ≤ l`): an argument below
`l` need not lie above `k`. The fact `l__s<i> ≤ l` is what lets a split declaration pass a copy-level
argument to another declaration at `l`. The fixture `pR_tail` passes its copies to the split `pR`.
These are the only changes to the fact table, and both checkers apply them independently
(`UniverseFacts.extend` / `Split.copiedRelations` and audit `Facts`).

**References.** Each copy stands for the source level `l`. At every reference to a split declaration,
R3 reads the universe argument for copy `i` as an argument for `l`, so the argument `a` must satisfy
`a ≤ l` in the source graph. This is exactly Rocq's cumulativity condition for using the monomorphic
declaration at an argument of level `a`. In the translator, `constGlobals` maps the copies back. In
the auditor, `gen` maps the copies back through `SPLIT_COPIES`.

## 3. Semantic correspondence

1. **Diagonal recovery.** Renaming every copy back to `l` (and collapsing the join `max(l, l, …)`)
   gives back the source declaration exactly. The auditor checks this per row (`level_unsplit`), and
   also over the whole corpus source: it holds for all 13 eligible declarations. So the diagonal
   instance `u_<l>__s<i> := u_l` of the translation is the translation of the source declaration.
2. **Every other accepted instance is justified by cumulativity.** In Rocq a use instantiates
   parameter `i` at level `a_i ≤ l`, a constraint of the source graph. In Lean the copy for `i` is
   instantiated at `a_i`. The audit's R3 check requires `a_i ≤ l` to be entailed by the source facts
   at every reference. Lean therefore accepts an off-diagonal instance only where Rocq accepts the
   same use through cumulativity. A reference that raises a copy above `l` is rejected, as for any
   R3 argument.
3. **The off-diagonal instances add no new inhabitants.** `tests/statement/proofs/split_correspondence.lean`
   is a synthetic proof about the fixture's own translated declarations, never a corpus proof. It
   shows that an instance at levels `a, b, c` is isomorphic to the diagonal instance at
   `m = max a b c` applied to the `ULift`ed carriers and relation. `ULift` is Lean's explicit form of
   `Type@{a} ≤ Type@{m}`. The proof covers the inductive (`pR`, `up`/`down` with both round trips) and
   the definition (`fun_R`). It is checked without axioms.

A diagonal specialization alone is not used as evidence. Point 2 covers each use, and point 3 covers
each instance.

## 4. Independent checks

* **Audit** (`tools/audit.py`, statement mode):
  * The reported split must equal the split derived from the source.
  * Copies must be fresh levels: no source level, nothing in the declaration, and a name shared with
    another split declaration only for the same level.
  * Every copy must be a universe parameter of the row.
  * The diagonal must recover the source.
  * The row is then audited against the split view by every existing check: structure, own levels,
    R3 with copies mapped back, binder independence and generality.
  * Output: `level_split_checked`.
* **Consumer** (`Rocq2Lean/Verify.lean`, detector `levels`): on the imported declaration's type
  alone, the parameter of copy `i` must occur as a sort only in the final sort of binder `i`'s
  domain, after the hypotheses, and in the type's final sort. Universe arguments of references are
  R3-checked by the audit.
* **Negative controls** (`tests/statement/check_level_split.py`): each is accepted by the kernel and
  rejected by the independent checks.
  * A forged split of the ineligible `gR`, whose level also occurs in the body: rejected by the audit
    for eligibility, and still rejected with the report field hidden.
  * Copies exchanged between binders: rejected by the consumer and by the audit.
  * A split row with one copy identified with another: rejected by the consumer and by the audit.
  * The statement narrowed to the diagonal: rejected by the audit (not forced by the source).

## 5. Scope

The rule applies to monomorphic declarations only: single-body, non-template inductives, and
constants with bodies. Proof-valued statements are never split; each binder of a statement already
has its own level. In the corpus, 13 declarations (17 levels) are eligible. All are CoqEAL
parametricity relations: `list_R`, `prod_R`, `list_R_rect`, `map_R`, `foldr_R`, `zip_R`, `pred_R`,
`all_R`, `has_R`, `cat_R`, `filter_R`, `flatten_R` and `last_R`.

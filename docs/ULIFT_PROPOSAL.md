# Proposal 1: rule U — interface-preserving local adapters for Rocq cumulativity

Status: **not implemented (user decision, 2026-10-18).** Plan adopted 2026-10-17 (user); rule U defined as
interface-preserving local adapters (user, 2026-10-17). The experiment of §7 found **no conflict at a local
position**: none on the 16-declaration GEL/HB frontier left by Stage 6 (§9), none among all 127 unprotected universe
rejections of S21 (§9.1), so neither variant unblocks a declaration. The conflicts are in statements, at generated
`.statement` references, or in the choice of a proof-local level's value (proposal 2). Generic transport lemmas are allowed **in the experiment only**; no change
to the proof-generation policy is adopted (§5). Companion: `docs/UNIVERSE_SOLVER_PROPOSAL.md` (proposal 2),
whose located conflicts are this rule's input.

## 1. Problem

Rocq types `A : Type@{i}` at `Type@{j}` whenever `i ≤ j` (cumulativity). Lean has no cumulativity: a term is
well typed only at its exact universe, so the translation must *equate* levels that Rocq only *orders*. When
that equation violates a source fact or the generality requirement, the declaration is refused. Today each
recurring shape has its own rule or tier (R3↑, R2B-P, R2B-S, R3↓, R-SPLIT, R-CARRIER copies, rule E, …).

Measured on S17 (245 direct failures, 205 unclaimed protected roots):

| Failing check (from the final message) | Direct failures |
|---|---|
| proof-local level solved by typing, native fact violated (R2B) | 160 |
| coherence on a shared level (upper bound) | ≤ 31 |
| kernel type mismatch | 13 |
| defaulted level not justified (R3′) | 11 |
| no raising (R3) not entailed | 9 |
| other (course-of-values, binder levels, narrowing, …) | 21 |

Of the 205 roots, 123 are blocked only by universe families (SOLUTION_FACT_VIOLATED, REFERENCE_RAISING,
COUPLED_BINDER_LEVELS, UNIVERSE_OTHER, REFERENCE_COHERENCE); 67 of them need all four of the first.

## 2. The rule: interface-preserving local adapters

Where every existing tier fails *because* Lean requires a level equality at a point where Rocq used
`Type@{i} ≤ Type@{j}`, the translator inserts a local adapter at that point and nowhere else: the value enters
the higher-universe context lifted (`ULift.up`, at `ULift.{r,s} A : Type (max s r)` = `Type@{j}`'s image) and
leaves it lowered (`.down`). The declaration's **type (its interface) is the source image, unchanged**; no
library type, no other declaration and no protected statement changes representation.

```lean
def highId (T : Type (u + 1)) (x : T) : T := x
def myFunction (A : Type u) (x : A) : A := (highId (ULift.{u+1} A) (ULift.up x)).down   -- rfl: = x
```

### 2.1 Where an adapter is local (checked in Lean 4.33.1, 2026-10-17)

| Shape of the higher context | Status |
|---|---|
| returns `T` itself, or a type not mentioning `T` | local; round trips definitional (`down (up x) ≡ x`, `up (down y) ≡ y`) |
| returns a type former of `T` (`List T`, `option T`, `T × B`, `T → B`) | needs `map down`; identities such as `map (down ∘ up) = id` on an abstract value are **lemmas**, not definitional |
| takes an instance over `T` (HB structure), fields about the operations only | a lifted instance with wrapped operations; proof fields transport definitionally (`fun a => h a.down`) |
| takes an instance over `T` with a field about **equality of carrier elements** (`eqP`, `reflect (a = b) …`) | needs `a.down = b.down ↔ a = b` (ULift injectivity): a **lemma** |
| a later use relies on a carrier conversion (`sort (Pack A …) ≡ A`) | not local: the lifted instance's carrier is `ULift A` |

A context that is not local stays blocked (variant 1) or, in the experiment only, is transported with the
generic lemmas of §5 (variant 2).

## 3. Correspondence: three independent checks

Adapter erasure alone is **not** sufficient (dependent structures, carrier equality, transported fields).
A row with adapters must pass all of:

1. **Adapter erasure (structural).** Removing `ULift`, `ULift.up`, `ULift.down` (and, in variant 2, the
   transport wrappers of §5 with their lemma applications) gives exactly the source term's image; each erased
   `ULift` sits where the source uses `A : Type@{i}` at `Type@{j}`, with `i ≤ j` entailed by the source
   graph and the target level exactly `j`'s image (no raising).
2. **Universe generality (independent).** The existing source-derived checks run unchanged on the row:
   `check_statement_generality`, binder independence, protected ranges, R3/R2B on every reference outside
   the adapters. An adapter never fixes, identifies or lowers a level the source leaves free.
3. **Semantic correspondence (independent).** The interface is the source image (the declaration's type
   equals the adapter-free translation's type); every lifted value is used only through `up`/`down` at the
   adapter boundary; a dependent position whose type mentions the lifted carrier is either re-lowered
   definitionally or the row is refused; generic correspondence lemmas (U1–U5, §4) cover every adapter
   shape used, and the consumer re-checks the row in a fresh process.

## 4. Obligations (Mathlib-free, axiom-free)

* **U1** `A ≃ ULift A` with both round trips definitional.
* **U2** interface preservation: the declaration's type is the source image.
* **U3** levels: no raising (`i ≤ j` entailed), target exactly `j`'s image.
* **U4** no adapter in a protected declaration's type, statement closure or conversion closure; protected
  interfaces are never changed.
* **U5** no generated corpus proof (variant 1). In variant 2, only the fixed lemmas of §5, listed by name.

Generic lemmas in `tests/statement/proofs/ulift_correspondence.lean`, as for rule P's C1–C5.

## 5. Generic transport lemmas (experiment only; not an adopted policy)

The user is open to **fixed, generic, axiom-free** transport lemmas, but the proof-generation policy is not
changed: variant 2 exists only to measure what they would buy.

* Fixed list, written once, kernel-checked, axiom audit empty: ULift injectivity
  (`a.down = b.down ↔ a = b`), `map` round trips for the type formers met (`map (down ∘ up) = id`), and
  eqType/`reflect` transport (an `eqP`-style field over `ULift A` from the field over `A`).
* Never corpus-specific; the translator may only apply lemmas from the list; the audit checks that every
  applied lemma is on the list and that its statement is the fixed one.
* Adopting variant 2 later is a separate policy decision.

## 6. Boundaries

* Unprotected library declarations only (MathComp, CoqEAL, Corelib). Protected declarations — Prosa **and**
  Classic — are never adapted, narrowed or changed.
* Last tier only: applied to a declaration that every existing tier rejected, gated on a located
  cumulativity conflict, with its own budget. Every previously claimed row stays byte-identical.
* No axioms, no `sorry`, no Mathlib in the translator or the auditor.

## 7. Experiment on the GEL/HB frontier (before any implementation approval)

Inputs: the GEL/HB frontier **re-derived from S21** (23 declarations at S17), with the dependencies that
reproduce it; the conflicts located by the solver's stage-A records where available.

| Variant | What is tried |
|---|---|
| 0. baseline | the S21 implementation (no adapters) |
| 1. local adapters | adapters at located cumulativity points; only the shapes of §2.1 that are local; nothing else |
| 2. adapters + generic lemmas | variant 1 plus the fixed lemmas of §5 for functorial returns and carrier-equality fields |

Per variant, measured and reported: newly accepted / pending declarations (frontier and downstream), newly
supported protected roots, new proof obligations (count, kind, and how many are instances of the fixed
lemmas), translation time (frontier and full corpus if run), and the classification of every frontier
member by the shapes of §2.1. Controls: every previously claimed row byte-identical, protected interfaces
unchanged, consumer and audit (with the three checks of §3) OK, forged-row negatives (wrong level, raising,
adapter in a protected statement, unreported adapter, a dependent position left lifted, a lemma not on the
list, a changed interface). The experimental tier is off by default and not merged; the report comes before
any implementation approval, with the remaining limitations.

## 8. Process

Experiment on its own branch from `main` after Stage 6 is merged; merge `main` into a branch before any
squash. Commits and pushes follow the project rules (CLAUDE.md: only when the user asks). ITERATION_LOG
entry for the experiment.

## 9. First result: classification of the frontier (2026-10-17)

**Input.** The GEL/HB frontier after Stage 6, re-derived from S21's attempt log and the source dependency graph:
**16 declarations** (23 at S17), all `UNIVERSE_REJECTED`. Frontier subset `front-sh2` (2,139 declarations, the
16 and their closures; implementation `solver-a` = S21 + stage-A diagnostics, report rows of the 16 unchanged).
For each of the 16, the stage-A shadow record (the first attempt re-run with a fresh level at every reference,
stopped after Lean's checker and unification) gives the classes of levels typing forces together. Each
occurrence carries the constant it belongs to and whether it sits in the type or the value. The classes were
matched with the levels named by the row's rejection message (`tools/solver_locate.py`, extended).

| Group | Rejection | Forced join, and where it is | Shape (§2.1) | Variant 1 | Variant 2 |
|---|---|---|---|---|---|
| `ssrint`: `intRing.comMixin` obligations 16, 23, 26, 32; `mulz_addl`; `intOrdered.subz_ge0` (6) | statement specialization refused: a carrier level (`choice.299`, `choice.333`) free in the source is fixed to `Set`'s image at a reference to an HB mixin or canonical instance of `int` | `int : Set` passed where the mixin's carrier is `Type@{choice.299}`; the class also joins `eqtype.32` (unrelated). The references are in the **statement** (type) of each declaration | carrier conversion: the statement uses `int`'s operations through `sort (instance) ≡ int`; with a lifted carrier the statement would be about `ULift int` | no: the adapter would sit in the interface (U2) | no: transporting the statement back to `int` is an equivalence proof about this statement, not an instance of a fixed lemma |
| `Order/Builders_62.factory_64` obligations 16–22 (7) | binder levels `order.15913 ≤ order.15972` forced (both become `u_preorder_110`); in 3 of them first a proof-local `preorder.119` solved above a fact | the obligation's **own binder levels** joined, through structure arguments and prerequisite `.statement` references; `order.16020` joined with `HB.structures.27/28/32` (unrelated) at `id_phant` statements | interface coupling (two binders of the statement at one level) | no: not a value position | no |
| `preorder.119` (in 17, 18, 22) | native fact `preorder.116__c1 ≤ preorder.119` not satisfied by `119 := max(…, 116__c0, …)` | a value position, but the failure is the choice between two R-CARRIER copies of one source level, not a missing cumulativity step | — (copy selection) | not applicable | not applicable |
| HB builders `Num/Builders_67.factory_69`, `Algebra/Builders_74.factory_78` (2) | raising at a reference to the declaration's own prerequisite `….obligation_1.statement` (`numdomain.14499 + 1`, `max(nmodule.1457, 2212, 625) + 1` against `divalg.3106`, `nmodule.1104`) | Lean's computed level (a `max`) is **above** the source's at a translator-generated `.statement` constant | raising: `ULift` only raises, it cannot lower a level | no | no |
| `GRing/Builders_406.factory_411` obligation 109 (1) | proof-local `rings_modules_and_algebras.11469` solved as `…11246`, violating `11469 < HB.structures.23` | joined with `nmodule.1457/2404/625` through prerequisite `.statement` references (type and value) | proof-local level identified, no cumulativity point | no | no |

**Measured, per variant.**

| | Variant 0 (S21) | Variant 1 (local adapters) | Variant 2 (+ fixed lemmas) |
|---|---|---|---|
| frontier declarations accepted or pending | 0 / 16 | 0 / 16 (no local position found) | 0 / 16 |
| downstream declarations, protected roots gained | — | 0, 0 | 0, 0 |
| new proof obligations | — | 0 | 0 (no lemma of §5 would be used) |
| translation time | `front-sh2`: 63 min on 2,139 declarations, incl. shadow re-runs | unchanged (no adapter tried) | unchanged |
| claimed rows changed, protected interfaces changed | — | 0, 0 (nothing implemented) | 0, 0 |

Variants 1 and 2 were not implemented: implemented per §6 (last tier, gated on a located cumulativity point at a
local position), they would not fire on any of the 16, so the counts above follow from the classification. An
implementation would only be worth building for a frontier that has such positions.

**What the frontier actually needs** (not proposed here; for the decision):

* `ssrint` (6): admit a reference that fixes a monomorphic library level the source leaves free at `Set`'s image
  (a specialization, recorded in the row, that the check refuses today). This is the generality policy, not
  cumulativity. It is a solver question (proposal 2, stage C) or a policy decision.
* `order` (7): the two binder levels are joined by typing in the statement itself. Under interface preservation
  neither adapters nor the solver can separate them. They stay blocked unless the interface may change.
* builders (3): couplings at translator-generated prerequisite `.statement` constants (raising, a proof-local
  level identified). The measured H⁺ relaxation did not unblock them (`docs/SOLVER_STAGE_A.md` §6). Candidate:
  give a prerequisite statement the level structure of its use site (proposal 2, stage B/C).

**Limitations of this result.**

* 21% of the occurrences in the 16 records are not attributed to a constant (levels created outside the
  reference path, e.g. by P3 hypotheses or instance re-elaboration); the classes they join are still listed.
* The record is of the first attempt's term structure. For P3 rows, hypothesis sharing itself depends on the
  level choice (19 GAP records on the `prof-A` subset), so another tier's structure may couple differently.
* Shape classification is by position (type vs value, which constant), not by a constructed adapter. The §2.1
  shapes were checked in Lean separately on small models, not on these terms.
* One frontier only. The wider set of S21's unprotected universe rejections is classified in §9.1.

### 9.1 Second result: all unprotected universe rejections of S21 (2026-10-18)

**Input.** The 127 unprotected `UNIVERSE_REJECTED` rows of S21 (the 16 of §9 included), shadow-recorded on
their closures (`uni-sh2`: 2,631 declarations, `solver-a` with `R2L_SHADOW_INST`, so that occurrences inside
assigned expression metavariables are attributed). Report rows of the 127 are unchanged from S21. Classifier:
for each record, the classes of the levels the rejection names; a member whose source level differs from the
class's base level (≤, ≥ or unrelated in the source graph) is a forced join, attributed to the type side (T),
the value side (V), both, or unattributed (−).

**Correction to the classifier.** 121 of the 127 records are obligations, translated as
`….statement : Prop := P`. The value side of such a constant is the stated proposition `P` itself, its
interface: an adapter there changes what the obligation states (U2). A first run counted their V joins as
local; they are interface positions. With that correction:

| Verdict | Declarations |
|---|---|
| interface: joins in the proposition of a `.statement` (all `numdomain` HB factories 10, 14, 16 obligations: proof-local `numdomain.3686`-type levels identified with an own level, violating a native fact against `divalg.3442`) | 96 |
| interface: joins at type positions (and, for `refines_abstr` and `HB_unnamed_factory_69`, also at value positions) | 9 |
| joins only at unattributed positions | 18 |
| no forced join at the named levels | 4 |
| **value-local candidates** | **0** |

The six non-statement records are `refines_apply`, `refines_abstr`, `HB_unnamed_factory_3`, `_69`, `_78`
(type-position joins) and `CMorphisms.iffT_flip_arrow_subrelation` (one unattributed join). `factory_69`, listed
in the frontier work as a possible value-only case, also has type-position joins (`T/≤` 7, `TV/unrelated` 492):
it is an interface case.

**Measured.** Variant 1 and variant 2: 0 of 127 declarations, 0 dependents, 0 protected roots, 0 new
obligations; translation time unchanged (nothing to build). Upper bound for reference: even if the 96
obligations were accepted by any means, **no** blocked protected declaration would be fully unblocked (4
depend on them, all also blocked by the §9 frontier: `factory_64` obligations, `factory_78`, `mulz_addl`);
3 unprotected blocked declarations would be. Fixing all 127 would fully unblock 85 of the 180 blocked protected
declarations, so the frontier matters, but its conflicts are not cumulativity at local positions. Run time:
4 h 03 min for 2,631 declarations with shadow recording (memory capped at 14 GB, next to S21b).

**Consequence for the decision.** Under interface preservation, rule U has no input in the current corpus: the
conflicts are in statements (obligation propositions, binder levels), at translator-generated `.statement`
references, or in the choice of a proof-local level's value. The last kind (the 96, and the CoqEAL
`38663`/`38671` rows such as `refine_task`, where rule P's tier fails with a proof-local level solved below a
native fact) is a solver question: a solution satisfying the source facts would separate the level without an
adapter (proposal 2, stages B–C).

**Limitations.** Same as §9: classification by position, not by built adapters; first attempt only;
unattributed joins (18 declarations have only those) could be anywhere, but 17 of those 18 are statements, whose
every position is interface.

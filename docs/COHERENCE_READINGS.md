# Rules R and H: shared-level coherence modulo an R2F reading; prerequisite instances

Status: adopted on 2026-10-15 (the user's approval of the measured proposal, ITERATION_LOG entry 11 §9),
on branch `rules-coherence`. Rule H (§5) was found while fixing R's one regression (Classic
`Affinity.task_affinity`). ITERATION_LOG entry 12.

## 1. The failure

R3 coherence (docs/UNIVERSE_TRANSLATION.md): at a reference, a source level `l` that the referring
declaration *shares* with the referenced one must get the argument `u_l` exactly. A declaration whose
type mentions `l` stays generic in `l` only if every use of `l` is `l` itself.

R2F reads an inductive's own level `l` as `ι l = max (u_l, ι m + k, …)` over the source facts `m ≤ l`
(`m < l`) between its own levels. A referring declaration that reconstructs such a reading in an
argument gets `max (u_l, u_m)`, which is not syntactically `u_l`. Coherence refused it. The plain
tiers then failed, and the definition was accepted only on the R3↓ tier with defaulted levels.

Found at `choice.eqtype_sub_type__canonical__choice_Countable`: `Countable.type`'s level 299 is read
as `max (u_299, u_577)` (with `577 ≤ 299` in the source). Before R, the instance had 4 defaulted levels.
The default flowed to `ordinal.{0}` and caused `fintype.HB_unnamed_factory_66`'s obligation 1 to be
refused, which blocked 712 protected roots (entry 11).

## 2. The rule

At a reference, an argument for a shared source level `l` may be `max (u_l, s₁, …, sₙ)` provided that:

* `u_l` occurs with offset 0;
* every other summand passes R3 (no raising): `Set + c ≤ l`, and `m + k ≤ l` for each own level `m`,
  entailed by the source graph;
* `l` is not a motive-level (R8) parameter on either side; there the argument is `u_l + 1`;
* `l` is not proof-local; such a level's argument must still be its R2S solution.

**Why it is not a specialization.** At every model of the source facts, every `sᵢ ≤ l`, so the
argument equals `l`. That is the justification R2F itself uses. The referring declaration keeps `u_l`
as a universe parameter, so nothing is narrowed. The generality checks (C-1: `freeLevelRef`, audit
`check_statement_generality`) are unchanged.

**Implementations (independent):**
* translator: `checkInstantiation` (Rocq2Lean/Translate.lean);
* audit: `check_universe_args` (tools/audit.py).

Both compute the normal form `max (c, p₁ + k₁, …)` themselves and run their own R3 check on the
remaining summands.

## 3. Controls

`scripts/test-coherence` (`tests/statement/check_coherence.py`, fixture `fixtures/stmt/coh`: real
exporter, real MathComp declarations, plus two synthetic statements):

| Kind | Control | Result |
|---|---|---|
| Positive | The Countable instance: claimed with no defaulted level; its references read 299 as `max (u_299, u_577)` | holds |
| Positive | `factory_66`, its obligation 1, `ord_pickle_refl`, `sub_pickle_refl` | claimed (before R: obligation refused, the others blocked/refused) |
| Negative (forged row) | `max (u_299, u_1007)` with `1007 ≤ 299` not entailed (raising) | audit-rejected |
| Negative (forged row) | `u_577` for the shared 299 on a plain tier (a specialization) | audit-rejected |
| Unit (audit) | reading, reordered reading, `max (u_l, Set+1)` | accepted |
| Unit (audit) | raising summand, `u_a + 1`, `Set + 2`, `u_l + 1`, no `u_l` summand, motive-level, proof-local | rejected |

`tests/smoke/UniverseRules.lean` holds the same unit cases for the translator's `checkInstantiation`
as `#guard`s.

## 4. Boundaries (rule R)

* On the R3↓ (cumulativity) tier, lower arguments are reported and R3-checked, as before.
* R does not touch coherence *by construction*. A body that instantiates a constant at a concrete level
  (`unit`'s finType, carrier 0) also pins the binder that shares the level (`Job`'s carrier 51). That
  family (ideal `processor_state` and others) needs per-occurrence instantiation of shared levels in
  bodies. It is recorded separately (entry 12).

## 5. Rule H: prerequisite statements are instantiated where they are used (R3↓ at hypotheses)

**The failure (R's regression).** Classic `Affinity.task_affinity (T : eqType) (n : nat) := T -> affinity n`
shares `eqtype.51` with its binder `T` (`Equality.type`'s carrier).
* Its value uses `affinity n = {set 'I_n}`, a pending definition.
* One of `affinity`'s prerequisite hypotheses is `inj_eqAxiom`'s obligation 1 at `nat_eqType`, whose
  carrier is 0. In Rocq this is the global level 51, which `nat : Set` reaches by cumulativity.
* `task_affinity` inherits that hypothesis, of type `inj_eqAxiom_obligation_1.statement.{…, 0, …}`.
  Coherence held its argument for the shared 51 to `u_51`, so the plain tiers were refused.
* On the R3↓ tier, every shared reference takes a fresh level, and `T`'s carrier was then solved to 0.
  That narrows a protected binder range, so it was refused.
* Before R, the dependency chain was specialized enough to hide this. Under R it is general, and the
  conflict surfaced.

**The rule.** At a reference to a proof task's *statement* (`<leaf>.statement`, the type of a generated
prerequisite hypothesis), an argument for a shared level may lie below it. This is R3↓ (no raising:
`Set + c ≤ l`, `m + k ≤ l` entailed), on every tier.

**Justification.** The hypothesis is not a binder of the source declaration; it is generated by the
translator.
* Its instance is fixed by the use that needs the prerequisite: here, `nat_eqType` at carrier 0. That
  is the only Lean instance `nat_eqType` has, because there is no lift.
* Rocq used the prerequisite at `l` with arguments of lower levels, by cumulativity, which is R3↓'s own
  justification. The no-raising check keeps the instance one Rocq accepts.
* The declaration's own levels and binder ranges are unchanged, and the generality checks (C-1) still
  apply.
* The hypothesis is a proposition about concrete instances. A proof of the prerequisite, which is
  generic in its levels, instantiates to it.

**Implementations (independent):**
* translator: `checkUniverseObligations`, which recognizes statement targets by `GEnv.leafStmtTargets`,
  filled when a proof task's statement is registered;
* audit: `check_universe_args`, with `HYP_STATEMENTS` taken from the source's proof tasks (`is_leaf`
  plus the generated statements) under both target namings.

**Controls** (`scripts/test-coherence` §5):

| Kind | Control | Result |
|---|---|---|
| Positive | `task_ord_affinity` (fixture; Classic's shape, with Prosa's `seqset`) | claimed on a plain tier, `T : Equality.type.{…, u_51, …}` |
| Baseline (without H) | The same row | accepted only on the R3↓ tier, `T : Equality.type.{…, 0, …}` (narrowed; refused for a protected definition such as `task_affinity`) |
| Positive | The row's prerequisite hypotheses | some instantiated at carrier 0 for the shared 51 |
| Negative (forged row) | Those hypotheses at `u_51 + 1` (raising) | audit-rejected |
| Unit (audit) | Lower argument (`u_a`, `Set`) at a statement | accepted |
| Unit (audit) | Lower argument at any other reference | rejected |
| Unit (audit) | Raising (`u_b`), offset (`u_a + 1`) at a statement | rejected |

## 6. Coherence by unification: shared levels per occurrence (stage 3, entry 13)

**The failure (PROTECTED_RANGE_NARROWED, 597 roots alone after R and H).** Every reference to a shared
level used the declaration's one level variable ("coherence by construction"). Wherever typing needed a
referenced definition's R2F *reading* of that level, there was only one variable to fit it, so it was
identified or solved. Three shapes on the measured frontier:

* **`JobType := Equality.type`** reads its level 58 as `max (u32, u51+1, u55, u58)`.
  * `Equality.sort` applied to `Job : JobType` needs that reading at its 58 position, while the
    binder has `u58`.
  * Every plain tier was ill-typed: `?58 =?= max (…, ?58)` has no solution.
* **`schedule`.** Its result sort `?22` must equal `ProcessorState`'s reading of `State`'s level,
  `max (?22, ?51, ?101)`.
  * The bounded solver settled on `22 := max (51, 101)`. The source has only `51 ≤ 22`, so this tied
    `PState`'s `State` universe to the job carrier.
  * `JobReady` (332 roots on its frontier) inherited the narrowing.
* **`ProcessorState`.** Its R2F interpretation reads both `Job`'s carrier and `Core`'s carrier as
  `max (u51, u101)`, because 51 and 101 are mutually equal in the source graph.
  * `processor_state`'s `Core := unit` (carrier 0) therefore pinned `Job`'s carrier.
  * The plain-parameter attempt (M6) failed only because of the first shape.

**The change (construction only; acceptance is unchanged in kind).**

1. **Per-occurrence levels.** On a new retry tier, a reference to a level shared with the declaration
   takes a fresh level metavariable per occurrence. After the value's type is unified with the declared
   type (inside `solveLevels`, before the parameters are named), every such metavariable left free is
   bound back to the declaration's own variable (`rebindShared`). Only typing can therefore give an
   occurrence another argument, for example a referenced definition's reading.
   * Where typing solved the own level through one of its own occurrences (`?l := max (…, ?occ)`), the
     occurrence is the parameter `u_l`.
   * That level is then booked as *interpreted*, and its solution must be exactly its R2F reading
     (`ownLevelInterp`), or the tier is refused.
   * Order: constants try the tier after the strict tiers. Blocks try plain parameters per occurrence
     before the R2F interpretation, as M6 orders plain before R2F.
2. **Blocks with plain parameters per occurrence** (`sort_interp`): the arity's final sort is read
   through the R2F interpretation. That equals the source sort at every model, and it bounds the
   fields' readings (`Finite.type`'s at 110, with `101 < 110` in the source). Every binder and field
   keeps plain parameters.
3. **Generality retry for definitions.** A definition accepted with an own *type* level solved by
   typing is retried with per-occurrence levels. The retry is kept only if it is accepted with fewer
   solved type levels and no more defaults.
4. **Discovery modulo readings** (blocks):
   * an arity argument `max (?x, …)` built from a reading makes `?x` a candidate, when `?x` is an
     argument for the same source level elsewhere;
   * prerequisite-statement references decide no class (rule H; R-CARRIER refinement 1).

**The checks, in their general form (one principle).** Rule R is stated as equality at every model of
the source facts:
* `equalAtModels` (translator) and `equal_at_models` (audit), on summands with `u_m` read as `m`.
* The argument for a shared level `l` must equal `l` at every model, and every summand still passes R3.
  This subsumes §2's `max (u_l, s…)` and also admits a source-equal `u_m`.
* The same holds for the argument for a solved or interpreted own level: it must equal the solution
  or image at every model.
* The generality checks (`freeLevelRef`, `check_statement_generality`) accept a binder argument that
  equals the referenced level at every model. This extends R-CARRIER refinement 5 (source-equal
  summands) to readings such as `max (u58, u32, u51+1, u55, u22)`.

Justification: an argument equal to the level at every model of the source facts is the source's
level, so it is no specialization. This is rule R's justification, applied wherever coherence or
generality compares a level with its expected value.

## 7. Blocks (stage 4, entry 14)

Four refinements of the block ladder. Each keeps the existing checks, and each has an independent
audit copy.

1. **R3G for field-only classes.**
   * A reference level class that occurs only in constructor fields, and that R3G-F does not take, is
     discovered like an arity class (same conditions).
   * The block is tried with it first. If the kernel finds a field too big, it is tried without it
     (R3″'s 0, as before).
   * Example: Classic `ConcreteTask.concrete_task`, whose `affinity` field references `choice`'s 1007.
2. **R3G for template blocks.**
   * Discovery also runs on template blocks.
   * Their implicit levels are ordinary non-template parameters, which the constructors must leave free.
     One that the constructors solve is refused, and the block falls back.
   * The audit's `ind_params` takes implicit levels for template blocks. They must not occur explicitly
     in the source and are never solved.
   * Example: `paper_model.SystemEvolutions (Omega : Type@{33}) (Job : JobType)`.
3. **Per-occurrence discovery and rebinding.**
   * Discovery also runs with shared levels per occurrence. Classes that coherence by construction
     identified with an own level (a lower carrier under `Equality.sort`) can then be named.
   * In `rebindShared`, a class is bound to its *lowest* level, the one entailed below every other, as
     R3G chooses. A class whose lowest level is not an own level is left to R3G.
   * Per-occurrence levels also apply on the R3↓ tier, tried first there. They do *not* apply to
     universe-polymorphic instance levels: an instance level stays the image of the source level, as the
     audit requires. Corpus run U4 showed that per-occurrence instance levels gave `reverse_coercion`
     arguments the audit correctly rejected. Such blocks go to δβ-inlining instead.
4. **An implicit level is a reference's argument** (translator, mirroring the audit): every implicit
   level of a block must be the argument (its parameter, or its R2F image) of some reference for that
   level. Otherwise the attempt is refused. Without this, the fresh-and-default R3↓ form could declare
   an implicit level that stands for nothing while its reference was specialized to 0. The audit
   rejected that form; the translator now refuses it too.

**δβ-inlining of erasing polymorphic definitions** (last tier for blocks):
* An *erasing* definition is a transparent universe-polymorphic constant whose body, after its leading
  λs, mentions no universe variable: `reverse_coercion x' x := x'`.
* When every attempt on a block fails, the whole ladder is run on the block with those applications
  δβ-reduced. The result is definitionally equal and carries none of the instance's levels.
* Example: `concrete_job`'s field `Equality.sort (reverse_coercion Equality.type Type@{25} inst
  concrete_task)`, which Rocq type-checks only through `Type@{21} ≤ Type@{25}`, becomes
  `Equality.sort inst`.
* The audit re-derives the erasing property for each reported name (`erasing_poly_body`). It replaces
  the block's source by its inlined form (`inline_erasing_block`) before every other check, and rejects
  a report whose inlining leaves an occurrence or changes nothing.

**Controls:** `scripts/test-blocks`.

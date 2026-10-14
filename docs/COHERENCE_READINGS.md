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

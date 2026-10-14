# Rule R: shared-level coherence modulo an R2F reading

Status: adopted on 2026-10-15 (the user's approval of the measured proposal, ITERATION_LOG entry 11 §9),
on branch `rules-coherence`. ITERATION_LOG entry 12.

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

## 4. Boundaries

* On the R3↓ (cumulativity) tier, lower arguments are reported and R3-checked, as before.
* R does not touch coherence *by construction*. A body that instantiates a constant at a concrete level
  (`unit`'s finType, carrier 0) also pins the binder that shares the level (`Job`'s carrier 51). That
  family (ideal `processor_state` and others) needs per-occurrence instantiation of shared levels in
  bodies. It is recorded separately (entry 12).

# M6 — Prosa v0.6 on the fixed toolchain: report

**Status:**
- **M6.1 / M6.2 met:** 61 genuine Prosa behavior theorems are VERIFIED.
- **M6.3 met for the finish-time development:** `finish_time`, `finished_at_finish_time`,
  `earliest_finish_time` and `response_time` are VERIFIED, with their original proofs.
- **`completes_at_finish_time` is not translated.** Its proof ends in `lia`, whose certificate
  needs the micromega closure, which is not supported (details below).

**Toolchain.** Unchanged: Lean v4.33.1, Rocq 9.3.0, MetaRocq Template `c18395ad` (unpatched),
MathComp 2.6.0 (switch `rocq930-mc`, `docs/ENVIRONMENT_M5.md`). The Prosa additions (MathComp
algebra and finite-group, mathcomp-zify, the micromega plugin) are install-only and recorded in
`toolchains.lock.json`.

| Criterion | Result |
|---|---|
| Prosa source compatibility under Rocq 9.3 | 5 isolated patches; 10 of 357 files changed; all of Prosa builds; no definition rewritten, no proof script changed (`compat/prosa-0.6/README.md`) |
| Elaborated declarations compared with the original environment | Rocq 9.0.1 + MathComp 2.4 (switch `prosa-0.6`, released `rocq-prosa` 0.6) vs the patched build. 281 declarations of the FinishTime closure: every `behavior/*` definition IDENTICAL; `finish_time`/`response_time` identical modulo printing. One statement differs (`util.bigop.big_pred1_seq`), because MathComp 2.6 dropped its own `eqfun` (`reports/m6/compat_comparison_finish_time.json`) |
| A genuine Prosa theorem with its full closure, original proof kernel-checked | `finished_at_finish_time`, `earliest_finish_time` (FinishTime, closure 123); 61 behavior theorems (closure 426) |
| No axiom / sorry / invented proof | consumer: `collectAxioms` empty for every target; every proof is the Rocq proof term of Prosa's own script, translated. No proof from the earlier correspondence project was used |
| Audits | independent structural, universe, dependency and axiom audits: OK on every reported run |
| 50–100 declarations and 10–20 theorems | 65 Prosa theorems VERIFIED as roots, plus 13 fresh holdouts; closures of 426, 411 and 123 declarations (MathComp, Corelib, Stdlib and Prosa) |
| M1–M5 regressions | `test-all` 18/18 (`test-m6` added) |

## Compatibility

`scripts/setup-prosa` fetches the original release (sha512 of the opam package), applies
`compat/prosa-0.6/patches/*` and builds with the lock's switch. The causes are all upstream:
- `ssreflect.done` moved to `ssreflect_rw`;
- a stray identifier that Rocq 9.0 ignored;
- the `of` binder was removed (`& T` replaces it);
- MathComp 2.6 dropped `Global Set SsrOldRewriteGoalsOrder`, which the patch restores;
- MathComp 2.6 changed the `\sum_` notation level (patch 0005 restores the original parse).

No legacy-Rocq exporter was needed.

## Results

| Run | Roots | Closure | Status |
|---|---|---|---|
| `runs/m6-behavior61` (`reports/m6/behavior61.json`) | 61 lemmas of `analysis.facts.behavior.{arrivals,service,completion}` | 426 | VERIFIED |
| `runs/m6-finishtime4` (`reports/m6/finishtime.json`) | `finish_time`, `finished_at_finish_time`, `earliest_finish_time`, `response_time` | 123 | VERIFIED |
| fresh holdouts after `m6-freeze-1` (`reports/m6/holdout_results.json`) | 20 lemmas of `analysis.facts.behavior.{deadlines,supply}` | 411 (the 13 translated) | 13/20 translated and kernel-checked on the frozen implementation, VERIFIED as their own run; 7 blocked by known classes |

## Fresh holdouts

Roots were chosen after the freeze tag `m6-freeze-1` and committed before running
(`reports/m6/holdout_selection.json`); the implementation was unchanged since the tag.

**Prosa: 13/20 translated and kernel-checked.** The 13 are VERIFIED as their own run (closure
411): `incomplete_implies_later_deadline`, `scheduled_at_implies_later_deadline`,
`service_invariant_implies_deadline_met`, `service_at_le_supply_at`,
`pos_service_impl_pos_supply`, `blackout_or_supply`, `supply_at_complement`,
`is_blackout_complement`, `supply_at_le_1`, `supply_during_last_plus_before`,
`blackout_during_last_plus_before`, `blackout_during_unit_growth`, `progress_inside_supplies`.

The 7 blocked roots (`incomplete_implies_scheduled_later`, `unit_supply_proc_service_case`,
`supply_during_bound`, `blackout_during_bound`, `supply_during_complement`,
`blackout_during_complement`, `blackout_during_cat`) fall only into classes already listed below:
`lia`'s arithmetic closure, `leqif`, `simpl_pred`, `nary_congruence`, `big_const_seq`. No new
failure kind appeared.

**MathComp: 14/14 VERIFIED** (one selected root, `eqtype.eqxx`, is a notation and was excluded).

## What was implemented (translator, auditor, consumer)

Each rule has an independent copy in the auditor, and the strict rules are unchanged for
declarations they already accept (`docs/UNIVERSE_TRANSLATION.md`, `docs/SUPPORT_PROFILE.md`,
`docs/TRUST.md`).

1. **R6, universe-polymorphic constants.** Universe variables become Lean parameters `v_i`, and
   instances are translated and audited exactly. This covers `Corelib.Classes.Morphisms`.
2. **Universe structure of MathComp/Prosa:**
   - R2⁺: fact-reduced sorts (`relation`);
   - R3G: implicit levels of references become parameters (`finite_axiom`; Prosa `ProcessorState`);
   - R2F-c: fact interpretation of a constant's own levels (`JobType := eqType`);
   - R8: motive levels admit `Prop` (bigop `big_rec2`/`big_ind` with `Prop` motives);
   - a reported cumulativity tier: R3↑ lifting (`Monoid.isLaw.phant_axioms`) and R2B-P (`Prop`
     typing of proof-local levels in `Morphisms`).
3. **Non-uniform inductive parameters.** These come from the native `nparams_rec`; a `match` on
   such a type lowers through a convoy equation. This covers MathComp's `acc_nat`.
4. **Accessibility lowering.** Structural recursion on a proof of a `Prop` inductive into data,
   for MathComp `find_ex_minn`, on which Prosa's `finish_time` rests:
   - it becomes `Acc.rec` over the call-graph relation of the body;
   - well-foundedness is proved by `I.rec` into `Prop`, replaying Rocq's guard reasoning;
   - the lowered function computes in Lean's kernel (`fixtures/accfix`: `search P2 0 h0 = 2` by
     `eq_refl`).
5. **Fixes found on the way:**
   - inductive R3 coherence against the R2F interpretation (latent since M5);
   - the auditor's comparison of recursor binder types modulo the level normal form;
   - binder names without macro scopes;
   - the replay parser reads `[anonymous]`;
   - an auditor bug where R2F-c skipped the R2B fact check on a forced level (caught by the
     audit itself on `Morphisms`).

## Tests

`test-m6` (in `test-all`) exercises R6, non-uniform parameters and the accessibility lowering on
fixtures and on MathComp. It includes three type-correct mutations that the kernel accepts and
the structural audit rejects, a forged R6 instance, and an honest kernel rejection (`plift`).
`test-m6-prosa` (long-running, not in `test-all`) reruns both Prosa sets from the patched build.
Universe-rule changes of earlier suites:
- `pid`, a former M3 negative, is now supported and verified;
- `length_rev` and `in_rev`, former M4 blockers, are now VERIFIED.

## Unsupported, with paths

`completes_at_finish_time` is blocked through `lia`'s certificate
(`reports/m6/completes_at_finish_time_blockers.json`). In the micromega/ZArith closure:
- mutual fixpoints: `Pos.add`/`add_carry`, `Pos.sub_mask`/`sub_mask_carry`;
- fixpoints whose decreasing match is not outermost: `Z.pos_sub`, `Pos.eqb`, `Pos.compare_cont`,
  `Pos.peano_rect`, `ListDef.nth`;
- higher-order recursive calls: `Tauto.xcnf`;
- `Acc_inv`, a functional recursive field;
- universe mismatches in `Ring_theory.ring_morph` and `RingMicromega`.

43 of the 104 candidate behavior lemmas are blocked by universe forms the rules do not cover
(`reports/m6/inspect_behavior.json`, `runs/m6-behavior`):
- MathComp `leqif` instantiates `prod` at `Prop`;
- `manifest_simpl_pred` (a `max` instantiation Lean's unifier cannot invert);
- `nary_congruence_statement` (residual level);
- Prosa `JobReady` (schedule's monomorphic instance);
- bigop `big_const_seq`.

The remaining Prosa lemmas need these forms, `lia`, or both.

## Next technical changes

1. **A universe-constraint solver for postponed `max` constraints.** Lean's unifier leaves
   `max(?a, ?b) = L` unsolved. Solving these under the native facts would subsume the retry tiers
   and unblock `simpl_pred`, `JobReady` and `nary_congruence`.
2. **Mutual structural fixpoints over one inductive** (a recursor into a product), and **matches
   whose decreasing match is not outermost** (reordering or `brecOn`). Together these give the
   positive/Z arithmetic, and with it `lia` certificates, which unblocks
   `completes_at_finish_time` and most Prosa lemmas.
3. **`Prop`-instantiation of template inductives** (`prod` at `Prop`) as a separate generated
   `Prop` inductive.

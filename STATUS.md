# Status

**2026-10-16 — Stage 5: job_task, rule P, rule Q-a, rule T, speed (merged into `main` after validation).**
* **Rules adopted (approved 2026-10-15):** rule P, `PULift` for a proposition used at a type
  (`docs/PROP_LIFT.md`, C1–C5 proofs); rule Q-a, phantom-only sort lowering for HB's `unify`/`id_phant`
  (`docs/PHANTOM_SORT.md`, equivalence proofs; **Q-b not adopted**); rule T, non-recursive coinductive types
  as inductives (`docs/COINDUCTIVE.md`, T1–T5). New suites: `test-prop-lift`, `test-phantom-sort`,
  `test-coinductive`.
* **No-policy fixes:** `job_task` (δβ-inlining of erasing definitions for constants), the erasing tier's own
  levels, R3G for definitions as a last resort (`refine_maxn`/`refine_minn`), P3 collapse with normalized
  levels, a proof-mode audit crash.
* **Corpus** at `38df8a9` (run `r2l-run-S17`; all checks OK): **685 Accepted / 3,584 Audited Pending / 184
  Blocked / 21 Direct Failure**, 205 unclaimed (S8: 676 / 3,538 / 235 / 25, 260 unclaimed).
  * 55 protected roots newly supported since S8; 0 regressions; all rows +1,965 claimed, 0 lost.
* **Open:** the GEL/order group (79 roots) behind a 23-declaration HB frontier (R-CARRIER copies × copied
  facts), next; Classic `job_eqdef` needs a representation decision; translation time (4 h 36 min, P3
  attempts) is the next speed target.
* ITERATION_LOG entry 15.

**2026-10-15 — Stage 4: blocks, terminations and translator speed (merged into `main` after validation).**
* `gcdn` (B-P termination statements), R3G for template blocks and field-only classes, δβ-inlining of
  erasing polymorphic definitions, native compilation and conditional tiers.
* **Corpus** at `f5e373c` (run `r2l-run-S8`; all checks OK):
  **676 Accepted / 3,538 Audited Pending / 235 Blocked / 25 Direct Failure** (S3: 673 / 3,477 / 299
  / 25).
  * 558 protected roots newly supported since RH2; 0 regressions; all rows +1,988 since S3, 0 lost.
* Full-corpus translation takes 22.5 min, native (S4 interpreted: more than 106 min).
* **Awaiting decisions (decided in stage 5):** rule P (now `docs/PROP_LIFT.md`), rule Q (now
  `docs/PHANTOM_SORT.md`, Q-a), and coinductive `Task_T` (now `docs/COINDUCTIVE.md`, rule T).
* ITERATION_LOG entry 14.

**2026-10-15 — Stage 3: coherence by unification, shared levels per occurrence (branch
`rules-occurrence`; merged into `main` after validation).**
* `docs/COHERENCE_READINGS.md` §6, with rule R in its general form (equality at every source model).
* **Corpus** at `2c78107` (run `r2l-run-S3`; consumer, audit, instances, provenance and tasks OK):
  **673 Accepted / 3,477 Audited Pending / 299 Blocked / 25 Direct Failure** (RH2: 673 / 2,983 / 785
  / 33).
  * 494 protected roots newly supported; 0 regressions; all rows +531 claimed, 0 lost.
* 324 protected roots remain unclaimed.
* `fun_hrel` (Prop ≤ Type) and `Task_T` (coinductive) need representation decisions.
* ITERATION_LOG entry 13.

**2026-10-15 — Rules R and H (branch `rules-coherence`; merged into `main` after validation).**
* **Rule R** (`docs/COHERENCE_READINGS.md`): shared-level coherence modulo an R2F reading. An argument
  `max (u_l, s…)` whose other summands pass R3 equals `l` at every model of the source facts.
* **Rule H** (same document, §5): R3↓ at proof tasks' statements, the types of generated prerequisite
  hypotheses, on every tier. It fixes R's one regression (Classic `Affinity.task_affinity`).
* **Corpus** at `2e46cbf` (run `r2l-run-RH2`; consumer, audit, source instances, provenance and task
  rendering OK): **673 Accepted / 2,983 Audited Pending / 785 Blocked / 33 Direct Failure** (from CB3's
  673 / 2,260 / 1,494 / 47).
  * 723 protected roots newly supported (702 Classic); 0 protected regressions;
  * all rows: +737 claimed, 0 lost.
  * R alone (run RR, `b915360`): 673 / 2,834 / 933 / 34 (+575, one regression); H adds +149.
* REFERENCE_COHERENCE is gone. The largest remaining family is PROTECTED_RANGE_NARROWED: 11 members,
  597 roots blocked by it alone.
* ITERATION_LOG entry 12.

**2026-10-15 — R-CARRIER, case B Option 2 (branch `rules-carrier`; merged into `main` and pushed on
2026-10-15).**
* Per-operand carrier universe levels: P1 decoupled parameter carriers, P2 implicit operand copies
  `l__c<k>`, P3 proof-local levels never represent a class, and refinements 1–5
  (`docs/CARRIER_LEVELS.md`).
* **Corpus** at `ee4e779` (run `r2l-run-CB3`; consumer, audit, source instances and provenance OK):
  **673 Accepted / 2,260 Audited Pending / 1,494 Blocked / 47 Direct Failure** (from 673 / 2,180 /
  1,518 / 103).
  * 80 protected roots newly Audited Pending, all Classic;
  * 0 protected regressions; 0 claimed rows lost; +161 claimed rows.
* Case B, `insub`, `factory_57` and `mixin_107` are fixed.
* The 761-root STATEMENT_FREE_LEVEL_PINNED group is **not** unblocked. Its frontier is now
  `fintype.HB_unnamed_factory_66` obligation 1 (712 roots), a consequence of the REFERENCE_COHERENCE
  mechanism.
* ITERATION_LOG entry 11.

**2026-10-14 — current baseline: R3G-F + the P2 retry tier for definitions (branch `rules-rsonly`,
reviewed, merged into `main`).**
* **R3G-F** (`docs/RESULT_SORT_LEVELS.md`) handles result-sort-only levels of class records. It solves
  276 internal MathComp rows and adds no protected root on its own (ablation).
* **The P2 retry tier for definitions** supports 3 more protected Prosa roots, previously refused by
  coherence.
* **Corpus** at the validated implementation `6fe8890` (run `r2l-run-RS4`; consumer, audit, source
  instances and provenance OK), on the fixed 4,474 protected roots: **673 Accepted / 2,180 Audited
  Pending / 1,518 Blocked / 103 Direct Failure**.
* **Open:** case B (carrier levels of structures with concrete instances) awaits a representation
  decision. ITERATION_LOG entry 10.

**2026-10-14 — rule round 2 + P3 + R-SPLIT (branches `rules-r2`, `rules-split`;
reviewed, merged into `main` by fast-forward to `69dc4cc`).** Binder-level independence and joint
level metavariables (entry 7), per-instance prerequisite hypotheses (entry 8), and R-SPLIT
(`docs/LEVEL_SPLIT.md`, entry 9). Corpus at the validated implementation `a28c4b3` (run
`r2l-run-SPLIT2`; consumer, audit, source instances, provenance OK), the fixed 4,474 protected roots:
**673 Accepted / 2,177 Audited Pending / 1,518 Blocked / 106 Direct Failure** (the baseline of
entry 10).

**2026-10-14 — checkpoint after B + C-1 (branch `task-c`; merged into `main` 2026-10-14).**
- **A** (`main`): assembly, proof-check tests, corpus provenance (36/36 round trips; manifest bound).
- **B** (termination obligations + unfolding equations, `docs/TERMINATION.md`) and **C-1 correctness
  repair** (`docs/UNIVERSE_FAMILY_C.md` §2): no statement, and no protected quantification range, is
  specialized at a universe level the source leaves free — refused by the translator, rejected by an
  independent source-derived audit check.
- **Corpus, B + C-1** (same 4,474 protected roots and merged IR; consumer OK, audit OK, provenance
  bound): **525 Accepted / 1,596 Audited Pending / 2,266 Blocked / 87 Direct Failure** (modern 340 /
  987 / 1,140 / 37, Classic 185 / 609 / 1,126 / 50). Claims surviving the source-derived audit: 707 in
  A → 2,121. Transitions A → B + C-1: 258 newly supported, 1,189 false acceptances corrected, 687
  rejected, 27 collateral losses, **6 genuine regressions** (`refine_*`). B-only is diagnostic (its new
  support is mostly narrowed). Details: `reports/statement_only/ITERATION_LOG.md` entry 4.
- Not applied: any result-sort rule for `JLFP`/`FP`/`JLDP_policy` (unsupported by the current
  representation and rules).

**2026-10-14 — A′ (branch `task-a-prime`, on top of `task-c`; merged into `main` 2026-10-14).** Opaque data translated
with its body as Lean `opaque` constants, proof subterms as obligations (`docs/OPAQUE_DATA.md`). Corpus
(re-exported, 10,966 records; consumer, audit, provenance OK): 520 / 1,601 / 2,272 / 81; no claimed row
lost; protected pending rows needing an opaque value **1,588 → 6** (1,595 now wait only for proof tasks).
ITERATION_LOG entry 5.

**2026-10-14 — R2B-V (branch `task-r2bv`, on top of A′; approved rule; merged into `main` 2026-10-14).** A type-valued
definition declared at the sort of its value (`docs/UNIVERSE_FAMILY_C.md` §4): `JLFP`/`FP`/`JLDP_policy`
and 11 other protected definitions translated, job generic. Corpus (consumer, audit, provenance OK):
**673 / 2,175 / 1,520 / 106** (modern 446 / 1,276 / 745 / 37, Classic 227 / 899 / 775 / 69); 727 newly
supported, no claimed row lost. ITERATION_LOG entry 6.

**Current phase: statement-only translation (direction change 2026-10-11).** Rocq2Lean translates
the datatypes, definitions and theorem *statements* of Prosa v0.6 and Classic, plus what they need,
mechanically. It never translates a Rocq proof and never writes a Lean proof: proofs are tasks for a
separate Lean proving agent. Design: `docs/STATEMENT_ONLY_DESIGN.md`. Report:
`reports/statement_only/STATEMENT_ONLY_REPORT.md`.

**Statement-only results (`reports/statement_only/`) — HISTORICAL, affected by the
universe-specialization defect (found 2026-10-14).** The Accepted / Audited Pending totals below (and
569 / 2,014 / 1,865 / 26 for the protected interface at `7d91605`/A) were computed by a translator and
audit that let universe levels the source leaves free be fixed (mostly to 0), narrowing statements
and protected definitions (e.g. `∀ Job : Equality.type.{0,0}`). The source-derived generality check
of C-1 (`tools/audit.py` `check_statement_generality`) finds, on the A run, **1,364 protected
statements and 512 protected definitions/inductives** narrowed (701 of the statements were also
self-reported as defaulted). These totals are not faithful-coverage claims; see
`reports/statement_only/ITERATION_LOG.md` (entry 4) for the corrected measurement.
- **Closure:** 5,622 source declarations (proof-preserving: 10,588). 4,966 proof-only declarations
  are eliminated (47%); 4,348 proof subterms are extracted as obligations.
- **Corpus run** (all 4,474 protected roots, 9,970 records): consumer OK, independent audit OK.
  3,990 claimed rows all MATCH: 1,668 accepted and 2,322 pending on proof tasks.
- **Protected interface translated and audited:** modern 1,346 / 2,504 and Classic 1,237 / 1,970
  (statements and definitions, accepted or pending on proof tasks).
- **Proof tasks:** 2,277 (`PROOF_TASKS.jsonl`), ranked by the pending declarations they unblock.
  `eqnP` comes first (needed by 2,114).
- **CLI:** `export --mode statement`, `translate`, `validate` (`STATEMENT_VALIDATED`), `tasks`,
  `check-proof`.
- **Tests:** `scripts/test-statement` 29/29. It covers 6 type-correct statement mutations
  (kernel-accepted, audit-rejected), the irrelevant-proof-change control (byte-identical), and 6
  rejected check-proof submissions. `test-all` 18/18 (proof transport, unchanged).
- **Remaining blockers:**
  * `edivn_rec`/`modn_rec`: recursion through `subn`; needs a termination-obligation rule;
  * `JLFP`/`FP`/`JLDP_policy` universes;
  * ideal `processor_state` obligations;
  * three protected declarations that would need narrowing (`taskset_of`, `affinity`,
    `ArrivalCurvePrefix`);
  * MathComp `nmodule` HB structures.

  See `BLOCKER_REASSESSMENT.md`.

**P0 (historical, proof-transport): `INVENTORY_COMPLETE`, `P0_ACCEPTED`**
(`reports/prosa_inventory/P0_REPORT.md`).
- **Classic build gap closed** with the authorized RTS patch (applied exactly; only proof-block
  lines change). All 357 + 190 files are enumerated: 4,741 in-scope declarations, 4,474 protected.
- **Request-dependent failures fixed:** R3G no longer requires facts about template levels (fixes
  `isFinite.axioms_`), and the universe facts are indexed per export (no batch-only resource
  limits).
- **Explained:** `nary_congruence` is a genuine instance blocker, not request-dependent.
- **Public-interface protection** is enforced in export, translator, consumer, audit and verify
  (`INTERFACE_REJECTED`; `ArrivalCurvePrefix`).
- **Regression on implementation `9951effd`:** `test-all` 18/18, `test-p0` 26/26, `test-inventory`
  OK, `test-m6-prosa` OK, FinishTime gate PASS (closure 1,717), and a clean-checkout reproduction.

## M6 completion (summary)

**Milestone: M6 completion — `M6_FINISHTIME_COMPLETE`** (`reports/m6/M6_COMPLETION_REPORT.md`).
- All five FinishTime roots, including `completes_at_finish_time` (proved by `lia` in Prosa), are
  VERIFIED in one fresh run of the strict gate `scripts/m6-finishtime-gate`: closure 1717 (642
  definitions, 1005 theorems/opaque, 70 inductives), original proof terms, empty axiom sets,
  reproduced from a clean checkout.
- Validation boundary: 159 dependencies are statement specializations at Rocq-checked universe
  instances (never a requested root).
- Fresh holdouts after `m6-completion-freeze-1`: Prosa util 9/18 translated (8 VERIFIED as their own request; 1 refused by the R2B-P source obligation on `nary_congruence`), MathComp `div` 0/8
  (non-structural recursion through `subn`; MathComp universe shapes).
- M6.1/M6.2, M5, M4 met; M1–M3 `HARDENED_M1_M3_ACCEPTED` (historical gate, `6e85e3c`).

Toolchains unchanged (Lean 4.33.1, Rocq 9.3.0, MathComp 2.6.0, MetaRocq `c18395ad`; switch
`rocq930-mc`). Regression: `test-all` **18/18** (361 checks); `test-m6-prosa` OK.

## M6 completion (`reports/m6/M6_COMPLETION_REPORT.md`)

| Item | Status | Evidence |
|---|---|---|
| Five-root gate (export, translate, verify, currency) | PASS, closure 1717 | `reports/m6/finishtime_gate.json` |
| Clean-checkout reproduction | PASS | `reports/m6/clean_reproduction/` |
| Evidence archive | packaged (64 MB, 318 files) | `reports/m6/evidence/package.json` |
| Historical positives (behavior61, finishtime4, holdout13, holdout14) | all VERIFIED; holdout20 request 15/20 (was 13/20), not VERIFIED | `reports/m6/m6_prosa_results.json` |
| New rules (ι-generalized, mutual, ζ/δβ, functional fields, course-of-values, nested, cast repair, δ-inlining; R3↓, plain inductive levels, R2B-S, R2B-P source obligation) | each with an independent audit rule, positives, mutations | `test-m6`, `docs/` |
| Closure progress | 792 → 1716 accepted; 34 → 0 leaves | `reports/m6/completion_progress.json` |
| Fresh holdouts | Prosa 9/18 translated (8 VERIFIED), MathComp 0/8 | `reports/m6/holdout_completion_results.json` |

## M6 — Prosa v0.6 (`reports/m6/M6_REPORT.md`)

| Item | Status | Evidence |
|---|---|---|
| Source compatibility under Rocq 9.3 / MathComp 2.6 | PASS | 5 isolated patches, 10/357 files, all of Prosa builds (`compat/prosa-0.6`, `scripts/setup-prosa`) |
| Elaborated declarations vs the original environment (Rocq 9.0.1, MathComp 2.4) | PASS | `reports/m6/compat_comparison_finish_time.json`: behavior definitions identical; 1 statement differs because of MathComp's `eqfun` (documented) |
| M6.1/M6.2 behavior theorems (arrivals, service, completion) | PASS | 61 VERIFIED, closure 426 (`reports/m6/behavior61.json`) |
| M6.3 FinishTime | PASS (5/5 since M6 completion) | the four roots VERIFIED in M6 (closure 123); `completes_at_finish_time` VERIFIED by the M6 completion gate (closure 1717) |
| New rules | PASS | R6 polymorphic constants; universe rules R2⁺/R3G/R2F-c/R8 and the cumulativity tier; non-uniform parameters (convoy); accessibility lowering (MathComp `find_ex_minn`); all with independent audit rules (`test-m6`, 8 checks incl. 3 type-correct mutations that the kernel accepts and the audit rejects) |
| Fresh holdouts (after `m6-freeze-1`) | 13/20 Prosa, 14/14 MathComp | `reports/m6/holdout_results.json`; the 7 blocked Prosa roots fall in documented classes |
| No axioms, no reused proofs | PASS | consumer `collectAxioms` empty; only Prosa's own proof terms |

M6 blockers as of the M6 report; the `lia`/micromega closure is resolved by M6 completion. Still open:
- `max` universe constraints and MathComp universe shapes (`simpl_pred`, Prosa `JobReady`,
  `big_const_seq`, `big_morph`, `fintype`);
- `prod` at `Prop` (`leqif`);
- MathComp `div` (`edivn_rec`: recursion through `subn`).

## M5 — MathComp 2.6.0 / SSReflect (`reports/m5/M5_REPORT.md`)

| Item | Status | Evidence |
|---|---|---|
| eqType + reflection | PASS | 13 roots VERIFIED (closure 57); packed `Equality.type` preserved |
| Sequences | PASS | 15 roots VERIFIED (closure 93) |
| Finite sums | PASS | `big_nil`, `big_cons`, `mem_iota`, `mem_cat`, `big_cat`, `big_nat_recr`, `big_geq`, `big_ltn` VERIFIED |
| Supported declarations | listed | `reports/m5/supported_declarations.json` (167; 98 MathComp) |
| Fix-lowering soundness fix | PASS | `fixtures/fixref`; no earlier declaration changed |
| Fresh holdouts | 14/14 | `reports/m6/holdout_results.json` |
| Blockers | reported | `card_bool`/`card_ord`/`big_ord_recr` (fintype class universes); `big_const_seq` (proof-local fact); `seq.nth` (non-outermost match) |

## M4 — real Rocq standard-library declarations

| Item | Status | Evidence |
|---|---|---|
| Inductive universe support (template R5, R2T, proof-local R2B) | PASS | Corelib `list`, `option`, `prod`, `sum`, `sigT`, `bool` as fresh Lean inductives (`test-m4`) |
| Real theorems with original proofs | PASS | 16 Stdlib list theorems VERIFIED (closure 47); auditor: 721 typing-determined levels, 0 deferred |
| Real functions | PASS | 29 Stdlib/Corelib functions VERIFIED (closure 35) |
| Computation | PASS | 39/39 Rocq-vs-Lean cases agree, incl. `list/option/prod/bool_rect` |
| Negative tests | PASS | Prop instances, template metadata, forged bindings and levels, type-correct fix mutations |
| Fresh holdouts (after `m4-freeze-1` = `54c9e70`) | 14/16 (15/16 after the post-holdout fix) | `reports/m4/holdout_m4*.json` |
| Regressions | PASS | `test-all` 16/16 (310 checks); no M1–M3 coverage lost (`reports/m4/regression_vs_m3.json`) |

M4 blockers:
* Corelib `nth`: decreasing match not outermost.
* Setoid `Morphisms`: universe-polymorphic constants; `relation` relies on `Set < l`.

Paths are in the M4 report.


Updated only from test evidence (`scripts/test-*` on cityu-wsl). Statuses follow the prompt's vocabulary.

**Historical verdict (M1–M3): `HARDENED_M1_M3_ACCEPTED`.** `./scripts/acceptance` passes 6/6 gates
(`reports/acceptance.json`). Full account: `reports/HARDENING_REPORT.md`.

## Acceptance hardening (second pass, after reviewed commit `7adb40b`)

| Gate | Status | Evidence |
|---|---|---|
| Clean-checkout reproduction | PASS | `scripts/clean-rebuild`: fresh clone of `dbf7c2b`, build from scratch, `test-all` 15/15 suites, 286 checks, 0 failed (`reports/clean_rebuild/`). Toolchains used as installed, **not rebuilt** |
| In-place suite | PASS | `test-all` at `7faa5db`: 15/15, 286 checks (`reports/test_all.json`) |
| M1–M3 fixtures preserved | PASS | `fixtures/m1`, `m2`, `m3`, `bootstrap`, `holdout` byte-identical to `7adb40b`. Every positive stage VERIFIED (kernel-checked insertion, consumer incl. empty `collectAxioms`, independent audit) |
| Root and dependency coverage | PASS | `test-root-contract` 40: translator refuses invalid recorded requests; consumer `roots` + `coverage`; auditor; 14 new cases through `verify`/`translate` |
| Artifact integrity | PASS | `test-artifact-integrity` 37: toolchain content fingerprint (93 files) bound; `rocq2lean status` currency check (`STALE` / `NOT_VERIFIED`); stale-success and interruption cases. `test-cli-status` 30: `inspect` exits 2 with structured diagnostics for every known blocker |
| Universe fidelity | PASS | `test-universe-audit` 26: R3 against the native graph; defaulted levels only with a kernel-checked justification (R3′, consumer re-check); `Eq` and recursor-motive levels recomputed by the auditor (28/28 on M3, 121/121 on holdouts) and checked by the consumer; source-fact, MetaRocq-constraint and target-level mutations |
| Case/Fix fidelity | PASS | `test-lowering-audit` 32: 6 type-correct mutations kernel-accepted and audit-rejected, 4 of them also through `verify` on synchronized forged runs; classification in `reports/hardening/lowering_mutations.json` |
| Historical holdouts (regression) | PASS | `test-holdout`: 9 historical roots VERIFIED. `pilot-freeze-1` = `6a4054d` preserved |
| Fresh holdouts | PASS | `hardening-freeze-1` = `742b3a9` (annotated); 14 new roots written after it: 14/14 VERIFIED on the unchanged implementation (`reports/hardening/holdout2.json`) |
| No coverage lost | PASS | pilot clean clone vs hardened clean clone: identical roots and accepted sets in every historical stage (`reports/hardening/regression_comparison.json`) |
| Evidence package | PASS | `reports/evidence/rocq2lean-evidence-de0bfcd.tar.gz` (sha256 `b9f56842…792a7`): M3d chain (5 original induction proofs, closure 24) VERIFIED, 244 files with `SHA256SUMS`, logs |

Remaining blockers: the supported fragment is unchanged (see `docs/SUPPORT_PROFILE.md` and the
report's last section). The next narrow extension is still global/template levels in inductive
declarations (Corelib `list`/`prod`/`option`). The toolchains were not independently rebuilt.
Nothing has been pushed to the remote (`origin/main` is gone).

## Pilot stages (unchanged results, now rerun as regressions)

| Stage | Status | Evidence |
|---|---|---|
| Phase 0: toolchains | PASS | `scripts/doctor`: Lean v4.33.1 (`819816b2`), Rocq 9.3.0 / OCaml 4.14.2, locks in `toolchains.lock.json`, report `reports/environment.json` |
| Phase 0: Lean checked path | PASS | `lake build Smoke`: valid accepted, `Nat.zero : False` rejected by the kernel |
| Phase 0: MetaRocq | **METAROCQ_TEMPLATE_RUNNING** | MetaRocq `c18395ad` unpatched; gate `reports/phase0/metarocq_gate.log` |
| id_nat end-to-end | PASS | `scripts/test-smoke` (7/7) |
| M1 export & dependency validation | PASS | `scripts/test-m1` (24/24) |
| M2 expression translation | PASS | `scripts/test-m2` (14/14, incl. audit positive control) |
| M3a–d inductives, case/fix lowering, original induction proofs | PASS | `scripts/test-m3` (22/22): computation 78/78 agree; 15 definitional / 6 propositional laws (`reports/m3_laws.json`); 7 unsupported patterns rejected explicitly |
| Negative suite | PASS | `scripts/test-negative` 11/11 |

Pilot final report (historical): `reports/FINAL_REPORT.md`.

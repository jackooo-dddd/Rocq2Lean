# Status

**2026-10-14 — Task A complete; Tasks B and C-1 implemented on branches (see below).**
- **A** (`main`, `803d733` + provenance commit): pending-to-final assembly (`rocq2lean assemble`,
  `docs/ASSEMBLY.md`), proof-check integration tests on a synthetic fixture (`scripts/test-assembly`
  32/32), corpus provenance (`reports/statement_only/PROVENANCE.md`: 36/36 chunk round trips OK,
  union universe check 0 violated, corpus manifest bound and checked, `scripts/test-provenance` OK),
  documentation refreshed. Corpus coverage unchanged by design (569 / 2,014 / 1,865 / 26).
- **B** (branch `task-b`, `220a8c2`): termination lowering with explicit termination obligations and
  unfolding equations (`docs/TERMINATION.md`); `test-termination` 22/22, `test-all` 18/18.
- **C-1** (branch `task-c`, `5dcee42`): statements are never specialized by defaulted universe levels
  (701 protected statements were, in the baseline); fixes the ideal `processor_state` family on the
  probe; `JLFP`/`FP`/`JLDP_policy` diagnosed as a policy blocker (`docs/UNIVERSE_FAMILY_C.md`).
- Corpus coverage of B and C: **not yet measured** (`reports/statement_only/ITERATION_LOG.md`).
- Remote: GitHub `main` is at `7d91605`; the commits above are local (not pushed).

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

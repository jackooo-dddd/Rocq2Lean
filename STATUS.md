# Status

**Current phase: Prosa-only scope locked; full inventory `INVENTORY_PARTIAL`**
(`reports/prosa_inventory/FULL_INVENTORY_REPORT.md`, scope in `docs/SCOPE.md`).
- Scope: Prosa v0.6 (`414e6676`, 357 files incl. 14 CoqEAL refinements) + Classic (ProsaBuddy
  `f692cb74`, all 190 files), with the dependencies their declarations reach.
- Census from the compiled environment: P 2,707 declarations (2,440 public; all 2,439 RTS names
  present), C 1,985 declarations (1,870 public; the 49-file plan matches RTS's 525) + 562 module
  aliases. Combined closure 10,539 declarations (5,847 external).
- Gap: 3 Classic files do not compile without RTS's proof-script patch (not applied); their
  declarations are `UNKNOWN`.
- Coverage: 163 P declarations VERIFIED (87 as roots); 2,555 in-scope declarations have no known
  blocker; 2,137 are blocked by 9 mechanisms, chiefly MathComp proof-local universe levels
  (`PCanHasChoice`, `big_const_seq`) and recursion through `subn` (`edivn_rec`).
- Next tasks T1–T5 in `reports/prosa_inventory/blockers.json` (`recommended_tasks`).

Regenerate: `scripts/inventory-prosa`; tests: `scripts/test-inventory`. The translator is unchanged
(implementation tree `819383b9…`).

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

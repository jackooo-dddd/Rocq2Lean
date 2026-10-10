# Status

**Current milestone: M6 (Prosa v0.6).**
- M6.1 / M6.2: criteria met.
- M6.3: met for `finish_time`, `finished_at_finish_time`, `earliest_finish_time` and
  `response_time`. `completes_at_finish_time` is blocked by its `lia` certificate.
- M5 and M4: criteria met (`reports/m5/M5_REPORT.md`, `reports/m4/M4_REPORT.md`).
- M1–M3: `HARDENED_M1_M3_ACCEPTED` (historical gate, commit `6e85e3c`).

Toolchains are unchanged (Lean 4.33.1, Rocq 9.3.0, MetaRocq `c18395ad`). MathComp 2.6.0 is in the
dedicated switch `rocq930-mc` (`docs/ENVIRONMENT_M5.md`). Regression: `test-all` **18/18**.

## M6 — Prosa v0.6 (`reports/m6/M6_REPORT.md`)

| Item | Status | Evidence |
|---|---|---|
| Source compatibility under Rocq 9.3 / MathComp 2.6 | PASS | 5 isolated patches, 10/357 files, all of Prosa builds (`compat/prosa-0.6`, `scripts/setup-prosa`) |
| Elaborated declarations vs the original environment (Rocq 9.0.1, MathComp 2.4) | PASS | `reports/m6/compat_comparison_finish_time.json`: behavior definitions identical; 1 statement differs because of MathComp's `eqfun` (documented) |
| M6.1/M6.2 behavior theorems (arrivals, service, completion) | PASS | 61 VERIFIED, closure 426 (`reports/m6/behavior61.json`) |
| M6.3 FinishTime | PASS (4/5) | `finish_time`, `finished_at_finish_time`, `earliest_finish_time`, `response_time` VERIFIED, closure 123; `completes_at_finish_time` blocked (`lia`: `reports/m6/completes_at_finish_time_blockers.json`) |
| New rules | PASS | R6 polymorphic constants; universe rules R2⁺/R3G/R2F-c/R8 and the cumulativity tier; non-uniform parameters (convoy); accessibility lowering (MathComp `find_ex_minn`); all with independent audit rules (`test-m6`, 8 checks incl. 3 type-correct mutations that the kernel accepts and the audit rejects) |
| Fresh holdouts (after `m6-freeze-1`) | 13/20 Prosa, 14/14 MathComp | `reports/m6/holdout_results.json`; the 7 blocked Prosa roots fall in documented classes |
| No axioms, no reused proofs | PASS | consumer `collectAxioms` empty; only Prosa's own proof terms |

M6 blockers (paths in the report):
- the `lia`/micromega closure: mutual `Pos` fixpoints, non-outermost decreasing matches,
  `Ring_theory` universes;
- `max` universe constraints Lean's unifier cannot invert (`simpl_pred`, Prosa `JobReady`);
- `prod` at `Prop` (`leqif`).

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

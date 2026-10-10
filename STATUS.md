# Status

Updated only from test evidence (`scripts/test-*` on cityu-wsl). Statuses follow the prompt's vocabulary.

**Current verdict: `HARDENED_M1_M3_ACCEPTED`.** `./scripts/acceptance` passes 6/6 gates
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

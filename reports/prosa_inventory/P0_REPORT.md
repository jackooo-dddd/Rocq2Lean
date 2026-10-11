# P0: complete inventory, request stability, public-interface protection

Baseline reviewed: `1f33207`. Final implementation: commits `5b36e0c`, `7a5a2d7` (regression record `6ed7cb2`), implementation tree
`9951effd76a8cff36087d1672db46ea67ddc3963878b2459bec213baf2632dc0` (before P0: `819383b9…`).
Toolchains unchanged: Lean 4.33.1, Rocq 9.3.0, MathComp 2.6.0, MetaRocq `c18395ad`.

## Verdicts

| Verdict | Result |
|---|---|
| **INVENTORY_COMPLETE** | INVENTORY_COMPLETE: all 357 + 190 files compiled and enumerated; 4,741 in-scope declarations (4,358 public, 4,474 protected); 0 gaps |
| **P0_ACCEPTED** | P0_ACCEPTED: both request-dependent failures are fixed (`isFinite.axioms_`, batch-only resource limits) or explained by a validated source fact (`nary_congruence`); comparable-input tests pass; interface protection is enforced in export, translator, consumer, audit and verify; all historical positives still pass with no weakened interface or test |

## 1. Classic source-build gap closed

* **Authorized patch.** RTS `f23ca672` `Prosa-Shunqi/classic-prosa/rocq93-port/prosabuddy-classic-rocq93.patch`.
  * Git blob `08b74dc571a5fdb1a6b7a868db3ee76c3834c2c9`, verified before use.
* **How it was applied.** Applied by `inventory/build.py` with `patch -F0` (exact, no fuzz; a dry run
  first) to the isolated build copy `.work/classic-f692cb7-build`. The pristine snapshot
  `.work/classic-f692cb7` is untouched.
* **What changed.** Only `classic/analysis/global/jitter/bertogna_edf_theory.v`:
  * the two removed lines (one rewrite chain) become `by rewrite !ltn_add2r.`;
  * every changed line lies inside a `Proof … Qed` block, checked mechanically;
  * no definition, statement or assumption is edited;
  * sha256 `eaed1d7c…` → `4c3d0d5a…`. The record is in `.patches.json` and in `build.json` / `files.csv`
    (`compatibility_patch`).
* **Rebuild.** `make -k` rebuilt only the patched file and its two dependents
  (`bertogna_edf_comp.v`, `implementation/global/jitter/bertogna_edf_example.v`). The post-patch log
  is kept separately from the pre-patch one.
* **Provenance.** Their proof terms come from the compatibility-patched build, not from the
  historical environment. Pre-patch build, enumeration and merge records are kept in
  `.work/inventory/prepatch-1f33207/`; the pre-patch reports are in git at `1f33207`.
* **Result.** Modern 357/357 and Classic 190/190 files compile and are enumerated. Classic has 2,596
  entries: 2,034 declarations (1,918 public) and 562 module-alias entries. The census has no gaps.

## 2. Inventory evidence

* **Classic probe.** Pre-patch, kept: `runs/inv-probe-classic`.
  * 834 roots, closure 3,336; 2,992 translated, 314 blocked, 28 direct failures.
  * Confirmations: 6 were probe artifacts (translated in M6 runs).
  * 18 of the 25 resource-limit failures translate alone; all 18 confirmations VERIFIED_CURRENT,
    except 3 rejected by Rocq's R2B-P instance check (`eq_unzip1`, `eq_unzip2`,
    `nth_or_none_mem`).
  * `eqtype.Sub_spec` / `insub_spec` were re-confirmed as blockers.
  * The first confirmation attempt for 4 nested-module declarations failed because of a
    library-resolution bug in `probe.py`. It was fixed; that attempt is kept in
    `confirmations-failed-attempt1.jsonl`.
* **Modern probe.** Pre-P0: `runs/inv-probe-modern`; confirmations in `runs/inv-confirm-*`.
  Successful confirmations were continued through `verify` and `status`
  (`runs/inv-probe-*/verifications.jsonl`). Two of them first failed only because three verifies
  ran concurrently in one tree (exit 3, a tool failure); run alone they are VERIFIED_CURRENT.
  Verification now runs sequentially.
* **Source assumptions.** The four Classic `Admitted` facts in
  `classic/implementation/uni/basic/tdma_rta_example.v` stay explicit source assumptions (nature
  `assumption`, blocker category `source_assumption`). Every declaration reaching them inherits the
  blocker. They are not proved, removed, replaced, or counted as axiom-free results.
* **Dimensions kept apart.** Candidate support (preflight), translation, kernel acceptance,
  verification and currency stay separate in `coverage.jsonl`.

**Coverage after P0 (historical proof-transport metric, `coverage.jsonl`).** Evidence is bound to
the final implementation, so runs from the earlier implementation (`819383b9…`) are now
`STALE_EVIDENCE_ONLY`.

Current runs: the regression reruns (`m6-gate-finishtime5`, `m6p-*`) and the P0 tests (`p0t-*`).

| | Modern | Classic |
|---|---|---|
| VERIFIED as root / as dependency | 81 / 73 | 0 / 0 |
| stale evidence only | 42 | 24 |
| no known blocker / downstream / direct | 1,981 / 717 / 9 | 1,572 / 454 / 8 |

**Post-P0 probes stopped.** Their re-run was started and then stopped when the project changed
direction (statement-only translation, 2026-10-11). The finished part is kept as a historical
record: the modern probe `runs/inv-probe-p0-modern` (1,981 roots, closure 7,289: 4,596 translated,
2,635 blocked, 30 universe, 13 kernel, 12 unsupported) and a partial set of `inv-confirm-p0-*`.
No conclusion is drawn from the partial confirmations.

## 3. P0: request-dependent behaviour

### 3.1 `mathcomp.boot.fintype/isFinite.axioms_` (fixed)

**Paired reproducer.** One root (`mathcomp.boot.fintype.isFinite.axioms_`), the same exported
closure, different loaded libraries (`fixtures/p0/isfinite_*.manifest.json`):

| Request (before) | `finite_axiom` level parameters | defaulted | `isFinite.axioms_` | fact `eqtype.51 ≤ Datatypes.190` |
|---|---|---|---|---|
| `mathcomp.boot.fintype` loaded | `u_eqtype_58` | 1 | **KERNEL_REJECTED** (application type mismatch) | absent |
| the M6 gate's libraries loaded | `u_eqtype_51, u_eqtype_58` | 0 | TRANSLATED_AND_CHECKED | present |

Runs: `runs/p0-pre-isfinite-{fintype_only,gate_env}` (pre-fix).

**Diagnosis.** The two exports are byte-identical for every record involved, and the references
carry the same level parameters. The difference is in the universe facts: the exporter computes
them natively from the *loaded* environment's universe graph. In the larger environment, an
unrelated library added the global constraint `eqtype.51 ≤ Datatypes.190`; `Datatypes.190` is the
template level of `list`. R3G's implicit-level choice for `finite_axiom` required `51 ≤ l'` for every
level `l'` in the unification class, including the template level 190.

A template parameter is instantiated afresh at every use (R5), so no such fact is needed. The
obligation checker (`checkUniverseObligations`) already exempts template levels. Without the fact,
`eqtype.51` was defaulted instead of becoming a parameter, and `isFinite.axioms_` then applied
`finite_axiom` at a level it no longer quantified over.

This is a legitimate environment difference meeting a rule that should not depend on it. It is not
state leakage, not order dependence, and not unsoundness: both outputs were kernel-checked, and the
rejection was a kernel refusal, not an accepted wrong proof.

**Fix** (`Rocq2Lean/Emit.lean`, the three R3G pick conditions): a template level in the class
imposes no fact.

**After** (`runs/p0t-isfinite-*`): both requests are VERIFIED. `finite_axiom` has level parameters
`[u_eqtype_51, u_eqtype_58]` and `isFinite.axioms_` has `[u_fintype_24, u_fintype_26]` in both
environments, with alpha-equal statements.

### 3.2 `Corelib.ssr.ssreflect_rw.nary_congruence` (explained; not request-dependent)

* **Same translation everywhere.** Every current run translates it identically: body-only level
  `ssreflect_rw.131 := 0` (R2B-P, `in_type: false`), one parameter `u_ssreflect_rw_147`.
* **Same rejection everywhere.** Rocq rejects that instance (`CheckInstance … 131=Set`: TypeError)
  because the native graph has `Set < ssreflect_rw.131`. This happened in every request that
  reached verify (`m6h-translated9`, the `count_sort` confirmation). The other runs never reached
  the instance check: they were AUDIT_REJECTED earlier or had no manifest.
* **Earlier label was wrong.** The inventory had labelled it context-dependent because a translation
  succeeded elsewhere. A translation success does not contradict a later verify-stage instance
  rejection. `evidence_blockers.py` now counts an instance rejection as context-dependent only if the
  *same instance* (declaration and substitution) passed in another run.
* **Status.** It is a genuine universe/instance blocker: Lean's version of the body forces the level
  to 0, Rocq's needs it above Set.

### 3.3 Batch-only resource limits (fixed)

* **Symptom.** In the 2,629-declaration modern probe, 18 declarations hit the per-declaration
  heartbeat limit, although their whole closures translated identically to their single-root runs.
* **Cause.** Fact queries scanned the request-sized relation table: `UniverseFacts.rel` was a
  linear `find?`, and `entails` with offset ≥ 2 looped over all levels. The probe table has
  1,048,345 relations and 2,387 levels, so the cost of the same declaration grew with the request.
* **Fix** (`Rocq2Lean/IR.lean`, `Translate.lean`). The facts are indexed once per export: a map for
  `rel`, and a strict-successor table for `entails`. Same semantics.
* **After.** Re-translating the same probe input:

| | before | after |
|---|---|---|
| time | about 75 min | 714 s |
| RESOURCE_LIMIT | 18 | **0** |
| translated | 2,075 | 2,262 |

  Four Prosa failures that had been hidden behind those limits surfaced; see section 6.
  `RESOURCE_LIMIT` stays a separate outcome, and the limits themselves are unchanged
  (`maxRecDepth 8192`, heartbeats ×5 per declaration).

### 3.4 Comparable-input tests (`scripts/test-p0`, fresh processes)

* singleton `JobReady`, singleton `isFinite.axioms_`, combined, reordered, and combined plus an
  independent root (`prosa.util.list.rem_in`): all VERIFIED;
* every declaration present in two of these requests has the same status, the same level
  parameters, and alpha-equal statements (binder names ignored, kernel terms otherwise compared
  exactly);
* a legal alternative dependency order of one export (Kahn order with the reverse tie-break)
  translates to the same acceptance and the same interfaces.

## 4. P0: corpus-wide public-interface protection

### 4.1 Reproducer: `ArrivalCurvePrefix`

In the `concrete_job` request, the public definition
`prosa.implementation.definitions.extrapolated_arrival_curve.ArrivalCurvePrefix` was a dependency:

| | statement |
|---|---|
| source | `ArrivalCurvePrefix : Type@{ac.21} := duration * seq (duration * nat)`, native fact `Set < ac.21` |
| translation (before) | `ArrivalCurvePrefix : Type` (Lean `Sort 1`; R2B-S lowered `ac.21 := 0`) |

* **What R2B-S changes.** It lowered the *result sort of the defined type* below its source lower
  bound (`Set < ac.21`). That is a change of the declaration's own universe, which every user of the
  type observes. R2B-P instead fixes a level that occurs in the statement (typically in the type of
  a quantified parameter), narrowing which arguments a lemma accepts. Both narrow the interface, but
  differently.
* **Effect here.** Users of the lowered type broke. `concrete_job`'s kernel rejection
  (`reverse_coercion` at `Type (u+1)`) disappears once the lowering is refused.

### 4.2 Enforcement

| Component | Check |
|---|---|
| Protected set | `reports/prosa_inventory/protected_interface.json`: 4,474 declarations (2,504 P, 1,970 C: public declarations and record/class projections); sha256 `fcc71378…`, pinned in `tools/protected_interface.pin.json` (implementation tree) |
| `export` | binds the protected names present in the IR, the manifest digest and the policy into `contract.json`; refuses a missing, altered (≠ pin) or stale (scope lock / declarations changed) manifest |
| translator | reads the binding from the contract (`#rocq2lean_import … contract sha`); refuses R2B-S and in-type R2B-P for a protected declaration, as root or dependency: `INTERFACE_REJECTED`, dependents `BLOCKED_DEPENDENCY`; each row records `protected` |
| consumer | new detector `interface`: binding present; report binding equals the contract's; every row's `protected` flag equals membership; no accepted protected row specialized |
| audit | independent recomputation from the pinned manifest: digest, membership, flags, no specialized protected row (that relaxations are reported truthfully is checked by its universe checks) |
| verify | recomputes the binding from the pinned manifest; refuses tampered, omitted or stale contract data and translations not run under this contract's binding |

Non-protected dependencies keep the existing checked policy: R2B-P instances are re-checked by Rocq
at verify, and statement specializations are never allowed on requested roots.

### 4.3 Detector results (`scripts/test-p0`)

| Case | Result |
|---|---|
| positive: `JobReady` and its protected dependencies | VERIFIED; consumer and audit checked 20 protected declarations |
| positive: external specializations (`length_rev`, `in_rev`) | VERIFIED with 10 non-protected statement specializations |
| negative: `concrete_job` (protected dependency needs R2B-S) | `ArrivalCurvePrefix` INTERFACE_REJECTED, `concrete_job` BLOCKED_DEPENDENCY |
| negative: `ArrivalCurvePrefix` as the requested root | INTERFACE_REJECTED (same as dependency) |
| negative: forged report row (protected `JobType` with R2B-S) | audit and consumer reject (`interface`) |
| negative: contract binding tampered (one name removed) / omitted | audit and consumer reject; verify rejects the tampered run |
| negative: manifest altered / stale | refused by `tools/protection.py` |

The detector tests use the JobReady run and forged artifacts, so they do not depend on
`concrete_job` translating.

## 5. Regression and reproduction

All on implementation tree `9951effd…`, in fresh processes:

| Suite | Result |
|---|---|
| `scripts/test-all` | **18/18 PASS** (1,376 s); `reports/test_all.json` |
| `scripts/test-inventory` | OK |
| `scripts/test-p0` | OK, 26/26 checks |
| `scripts/test-m6-prosa` | OK: behavior61 (426), finishtime4 (123), holdout13 (411), holdout14 (132) VERIFIED; holdout20 15/20 translated, not verified, unchanged from before P0 (`leqif`, `big_const_seq`) |
| `scripts/m6-finishtime-gate` | **PASS**: five roots VERIFIED, closure 1,717 (`reports/m6/finishtime_gate.json`) |
| `scripts/p0-clean-reproduce` | fresh clone at `4862c7b`: `lake build` from an empty `.lake`, Prosa rebuilt, `test-p0` 26/26 and `test-inventory` OK (`reports/prosa_inventory/p0_clean_reproduction/`) |

One process note: during the first regression attempt, implementation files were changed while
`test-m6-prosa` was running. That attempt was stopped and the whole chain was re-run on the final
code; only the re-run counts.

## 6. Unresolved blockers and task order

**Still-open blockers of the proof-transport pipeline (historical).**

* MathComp proof-local universe levels: `PCanHasChoice`, `big_const_seq`, `seq_hasChoice`.
* Universe entailment at references: Prosa `FP_policy` / `JLFP_policy` / `JLDP_policy`,
  `eqtype.Sub_spec`, `big_morph`.
* `eqtype.insub_spec` (cast annotation).
* Recursion through `subn` (`edivn_rec`, `modn_rec`).
* Template `prod` at Prop (`leqif`, `pair_of_and`, `nat_of_add_pos`).
* `nary_congruence` R2B-P instance.
* CoqEAL parametricity lemmas.
* The four Classic `Admitted` facts.
* `ArrivalCurvePrefix`, now an honest `INTERFACE_REJECTED`.

**Task order superseded.** The T1–T5 order is not continued: on 2026-10-11 the project direction
changed to statement-only translation (Rocq datatypes, definitions and theorem statements; new proofs
by a Lean proving agent). These blockers are to be reassessed under that policy in
`reports/statement_only/BLOCKER_REASSESSMENT.md`; many of them occur only in source proof bodies.

## 7. Commands

```
scripts/inventory-prosa                      # full inventory (stages in run_log.json)
scripts/test-inventory                       # inventory tooling tests
scripts/test-p0                              # focused P0 tests (fresh CLI processes)
scripts/p0-clean-reproduce                   # the focused tests from a clean checkout
scripts/test-all; scripts/test-m6-prosa; scripts/m6-finishtime-gate
INVENTORY_PROBE_TAG=-p0 python3 -I inventory/probe.py build|translate|confirm modern|classic
INVENTORY_PROBE_TAG=-p0 python3 -I inventory/verify_confirmations.py modern|classic
python3 -I inventory/protection_manifest.py --pin
```

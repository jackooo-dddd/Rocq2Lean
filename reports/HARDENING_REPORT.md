# Acceptance hardening of M1–M3: report

**Verdict: `HARDENED_M1_M3_ACCEPTED`.** Computed by `./scripts/acceptance` (`reports/acceptance.json`),
which passes only if all six gates below pass. It is not asserted by hand.

| | |
|---|---|
| Last remotely reviewed commit | `7adb40b` |
| Historical freeze (preserved) | `pilot-freeze-1` → `6a4054d` (unchanged) |
| Hardening freeze (new, annotated) | `hardening-freeze-1` → `742b3a9` |
| Clean-checkout reproduction | fresh clone of `dbf7c2b`: build from scratch, `test-all` **15/15 PASS, 286 checks, 0 failed** (530 s) |
| In-place reproduction | `7faa5db`: `test-all` **15/15 PASS, 286 checks** |
| Toolchains | Lean v4.33.1, Rocq 9.3.0 (opam `rocq930`), MetaRocq Template `c18395ad` unpatched: **unchanged** |
| Toolchain independently rebuilt? | **No.** Both toolchains were used as installed. `doctor` checks them against `toolchains.lock.json`, and every run now binds the content digests of the binaries it used (93 files). This does not show that those binaries were built from the locked sources. |

The translator was not restarted, and nothing was added for MathComp or Prosa. The supported
fragment (`docs/SUPPORT_PROFILE.md`) is unchanged: this pass changes only what may be **accepted**,
not what is translated.

## Starting point (reproduced before any change)

The 13 commits after `7adb40b` (`7b3adf2`…`e1a8fde`, hardening P0/P1 from an earlier session) were
kept as they were. Their result was reproduced first: `test-all` at `e1a8fde` gave **14/14 PASS**,
committed as `7fe8fa4`. Its last recorded `test-root-contract` failure had been fixed by `e1a8fde`
but never rerun; rerunning it gave `OK`. Before that earlier work, the baseline at `7adb40b` reproduced
a real hole: a report whose roots were emptied and relabelled still verified
(`reports/hardening/baseline/`). That earlier work closed it, and the cases below extend that fix.

## What this pass changed

### 1. Root and dependency coverage

The original request is now authoritative at every stage: snapshot → IR roots record → translator →
report → consumer → auditor.

* **Translator** (`Rocq2Lean/Command.lean`, `rootContractProblem`):
  * It refuses an IR whose recorded request is empty, contains a duplicate spelling, resolves two
    spellings to one declaration, or names a non-exported declaration. The result is
    `ROOT_CONTRACT_REJECTED`; the report records that status, and no translation manifest is written.
  * Report schema 0.3 adds a top-level `status` (`OK` / `ROOTS_NOT_TRANSLATED` /
    `ROOT_CONTRACT_REJECTED`). Each root record carries `{requested, name, status}`, and
    `DUPLICATE_RESULTS` / `MISSING_FROM_RESULTS` are explicit statuses.
* **`translate` CLI:** checks the report's roots against the contract of the same run.
* **Consumer:** a new `roots` detector. The report status must be `OK`, the root records must equal
  the contract roots in order (spelling and resolved declaration), and each status must equal its
  result row's status. This is in addition to the existing `coverage` detector, which requires
  exactly one row per exported declaration, every root and every declaration of the required closure
  accepted, and at least one accepted declaration.
* **Auditor:** compares requested spellings and the report status.

**Rejections through the public CLI** (`test-root-contract`, 40 checks). Each case is checked for the
intended consumer detector and message, not just for a non-zero exit. In every `verify` case, the
mutated report was re-synchronized into the translation manifest first.

| Case | Where | Detector |
|---|---|---|
| report roots emptied (results intact) | `verify` | `roots` |
| one root record omitted | `verify` | `roots` |
| root record says success, result row says `UNSUPPORTED_FEATURE` | `verify` | `coverage` |
| root record respelled / retargeted / status forged | `verify` | `roots` |
| report status forged | `verify` | `roots` |
| duplicate result row for a root | `verify` | `coverage` |
| zero accepted declarations, statuses consistently relabelled | `verify` | `coverage` ("no accepted declaration") |
| contract **and** snapshot request emptied consistently | `verify` | `coverage` ("no accepted declaration") |
| IR roots record empty / duplicated / same resolution / unknown name | `translate` | `ROOT_CONTRACT_REJECTED`, exit 2, no manifest |

That is 14 new cases. They come in addition to the 16 standalone-auditor rejection cases, the 5
`export` request cases and the 3 earlier `verify` cases that were already there.

### 2. Artifact integrity and failure handling

* **Toolchain binding by content.** The snapshot (schema 3), the translation manifest and
  `verify.json` record the SHA-256 of the `lean`, `lake` and `libleanshared.so` (kernel) binaries,
  the `rocq` binary, and the MetaRocq Template plugins and theories (93 files). If any of these
  differs at export or translation time, `verify` rejects the run.
* **`rocq2lean status --run RUN`** (new, read-only). It recomputes every digest the verdict is bound
  to and answers `VERIFIED_CURRENT` (exit 0) or `STALE` / `NOT_VERIFIED` (exit 2). A `VERIFIED` file
  therefore never counts as current once a source, IR, report, module, implementation or toolchain
  file has changed.
* **Preflight 2 / `inspect`.** Every statically visible blocker is now detected (mutual fix,
  non-direct recursive call, changed parameter before the decreasing argument, `match` on a
  nested/mutual inductive or one with functional fields or let-bound constructor arguments, global
  levels in inductives, relaxed source checking), with:
  * the blocked declaration and the dependency path to it;
  * the reasons, each with the node path where it occurs;
  * exit 2 when any requested root is blocked.

  It agrees with the translator on every positive and negative fixture.
* `test-cli-status` no longer depends on a run directory left behind by an earlier session. That
  dependency would have failed in a clean checkout.

**New cases.**
* `test-artifact-integrity` (37 checks):
  * a run exported or translated under different toolchain binaries is rejected;
  * `verify.json` binds the fingerprint;
  * `status`: a fresh run is current; it becomes `STALE` after a source edit (naming the file) and
    current again once the exact source is restored; `STALE` after a module change or a deleted
    artifact; `NOT_VERIFIED` after a failed re-verification; and `status` never writes anything.
* `test-cli-status` (30 checks): each of the 7 M3 negative roots is blocked with its reason and node
  path; a blocker reached through a dependency (`uses_ax → ax`); relaxed checking; a candidate in the
  same request.

The existing stale-success and interruption cases (kill during the consumer, kill at start,
concurrent writer) still pass.

### 3. Universe fidelity

* **Defaulted levels need a justification (R3′).** A level left unassigned by Lean's unifier is set
  to 0 only if the kernel accepts the declaration with that level as a fresh universe parameter,
  i.e. the declaration is valid for every value of the level (`justifyResiduals`). Otherwise the
  declaration is `UNIVERSE_REJECTED`.
  * The report records the generic declaration.
  * The auditor checks that this generic declaration instantiates at 0 to exactly the reported one.
  * The consumer (`residual_levels`) re-checks it in the kernel in a fresh process.
  * The new fixture `fixtures/universes/UnivResidual.v` contains a genuinely unconstrained reference.
* **Typing-determined levels are checked, not counted (R4).** The auditor recomputes, from the
  audited target terms, the universe argument of every `Eq`, `Eq.refl` and `Eq.rec` occurrence and
  the motive level of every large recursor application (`InstanceLevels`). The consumer checks every
  occurrence with Lean's inference (`instance_levels`). On the M3 `mirror_mirror`/`addR_RS` closure
  the auditor determined 28 of 28; on the fresh holdouts, 121 with none deferred. The consumer counts
  distinct subterms (120 there).
* The existing R3 check (coherence and no raising against the natively re-checked universe graph)
  and the existing fact mutations are unchanged.

**New cases** (`test-universe-audit`, 26 checks):
* justified residual (positive control);
* a forged justification that is invalid for some level: the consumer's kernel re-check rejects it.
  The auditor's syntactic check alone accepts it, so the kernel re-check is the necessary gate.
* a removed justification record, and one that does not instantiate to the accepted declaration:
  rejected by consumer and auditor;
* `Eq` level raised, recursor motive level raised (`RNat.rec` in `addR`): rejected by the kernel and
  by the auditor's `instance_levels`;
* an invented MetaRocq constraint (`ub < ua`): rejected by the native round trip (not entailed);
* 3 Lean unit checks of `justifyResiduals` (`tests/smoke/UniverseRules.lean`).

### 4. Case/Fix fidelity

The auditor already reconstructed recursor identity and levels, motive and minor binder types (from
the kernel recursor type, modulo β), parameters, the motive body, minor bodies with recursive-result
mapping, the major premise, trailing arguments, and fix parameters, indices and motive. This pass
adds **type-correct** mutations: the kernel accepts them, so only the audit can catch them. Each one
is now also driven through `rocq2lean verify` on a *synchronized forged run* (`tests/lib.forge_run`),
in which the generated module is rebuilt from the mutated report by the kernel, simulating a buggy
translator.

| Mutation | Declaration | Kernel | Standalone audit | Full `verify` (definition root) | Under the computation lemma |
|---|---|---|---|---|---|
| swapped minor premises | `neg2` (new `B2`) | accepted | `structure` | consumer OK, audit rejects, exit 2 | kernel rejects dependent proof |
| match uses its recursive result | `pred_r` | accepted | `structure` | consumer OK, audit rejects, exit 2 | kernel rejects dependent proof |
| decreasing argument ↔ trailing argument | `addR` | accepted | `structure` | consumer OK, audit rejects, exit 2 | kernel rejects dependent proof |
| recursive-call argument changed | `addAcc` | accepted | `structure` | consumer OK, audit rejects, exit 2 | kernel rejects dependent proof |
| recursive-result order (existing) | `mirrorR` | accepted | `structure` | — | — |
| trailing-argument order (existing) | `swapacc` | accepted | `structure` | — | — |

The full classification, including kernel-rejected and intentionally equivalent mutations, is in
`reports/hardening/lowering_mutations.json` (23 entries). An unmutated forged run verifies, which is
the positive control for the forging path.

A `match`'s indices are the one item still handled by an *obligation* rather than reconstructed:
Rocq does not store them. The consumer's `rec_indices` check requires them to equal the indices of
the major premise's type at every recursor application. Any other value is kernel-rejected or
definitionally equal (`case-index-different`: kernel rejection; `case-index-beta-equivalent`:
equivalent).

## Acceptance criteria → evidence

| Criterion | Evidence |
|---|---|
| M1–M3 positive fixtures keep their statements and proofs, and pass checked translation, independent audit and axiom checks | `fixtures/m1`, `m2`, `m3`, `bootstrap` and `holdout` are byte-identical to `7adb40b` (gate `fixtures_preserved`). `test-m1` 24/24, `test-m2` 14/14, `test-m3` 22/22: every positive stage VERIFIED (kernel insertion through `addChecked`, consumer incl. `collectAxioms = ∅`, structural/universe/instance audit). No axioms, `sorry`, unchecked insertion or replacement proofs (`test-assumptions` 7/7) |
| New negative tests reject each defect for the intended reason; valid controls pass; public CLI and full pipeline | sections 1–4. Detectors and messages are asserted, and each suite has positive controls |
| Source-constraint and target-level mutations detected; Case/Fix computation equations still valid | section 3. `test-m3`: computation 78/78 agree, 15 definitional / 6 propositional laws |
| Historical holdouts as regressions; `pilot-freeze-1` preserved; new freeze before new holdouts | `test-holdout` (9 historical roots, regression role) PASS. `pilot-freeze-1` = `6a4054d`. `hardening-freeze-1` = `742b3a9` (annotated); holdouts first committed in `139cd6e`, after it. `test-holdout2` checks the implementation is identical to the freeze |
| Clean-checkout reproduction in fresh processes | `reports/clean_rebuild/` (`scripts/clean-rebuild`): fresh `git clone`, `lake build Rocq2Lean Smoke` from scratch, `test-all` with every suite in its own process |
| One complete nontrivial M3 evidence chain with hashes and logs | `reports/evidence/rocq2lean-evidence-de0bfcd.tar.gz` (sha256 `b9f56842cf2b93ac5dd06b05fd481b87b1ad2a6a937994a57387b22f35f792a7`, 244 files, `SHA256SUMS` inside) |

## Fresh holdouts (unseen inputs, frozen implementation)

`fixtures/holdout2/Holdout2.v` was written after the freeze and compiled with `rocq` before it was
committed. It contains:
* Corelib `nat` arithmetic by induction;
* a three-constructor parameterized inductive with two recursive fields;
* an indexed family `Fin` with index generalization and an index-dependent result;
* nested matches;
* `discriminate` and `injection`;
* an indexed Prop predicate with induction on its proofs;
* accumulator recursion;
* a Section variable;
* a `Defined` lemma and a `let`.

**Result: 14/14 roots `TRANSLATED_AND_CHECKED`; the run is VERIFIED and `status` says current.**
* Required closure: 47 declarations (45 translated, 2 bootstrap).
* Generated inductives: `Shape`, `Fin`, `Tri`, `Ev`, `L`, Corelib `True` and `False`.
* Corelib `nat_ind`, `eq_ind`, `eq_ind_r`, `eq_sym`, `f_equal`, `not`, `False_ind` and `Nat.add` were
  translated generically.
* Preflight classified all 14 roots as candidates.

Details: `reports/hardening/holdout2.json`. No implementation file changed after the freeze.

## Coverage differences

* **Before → after** (`reports/hardening/regression_comparison.json`): the pilot's clean clone
  (`61cecf1`, `pilot-freeze-1` implementation) against the hardened clean clone (`dbf7c2b`). Every
  historical stage has the same roots and the same accepted declarations (smoke 2, M1 12, M2 20,
  M3a 4, M3b 16, M3c 21, M3d 22, holdout 40, M3 computation 95). Nothing was lost or relabelled.
* **Newly accepted inputs:** the 14 fresh holdout roots (closure 47) and `UnivResidual` (one
  justified default).
* **Newly rejected:** only forged or ill-formed artifacts (sections 1–4). No genuine source
  declaration that verified before is rejected now.

## Exact commands

```sh
# on cityu-wsl, ~/research/Rocq2Lean
./scripts/test-all                      # in place (reports/test_all.json)
./scripts/clean-rebuild                 # fresh clone + build + test-all (reports/clean_rebuild/)
python3 -I tests/hardening/regression_compare.py ~/research/r2l-clean ~/research/r2l-clean-dbf7c2be21cb \
        reports/hardening/regression_comparison.json
./scripts/package-evidence              # reports/evidence/
./scripts/acceptance                    # reports/acceptance.json; exit 0 iff HARDENED_M1_M3_ACCEPTED
# one chain by hand
./scripts/rocq2lean inspect   --manifest fixtures/m3/manifest.json --roots M3.M3Proofs.mirror_mirror
./scripts/rocq2lean export    --manifest fixtures/m3/manifest.json --roots M3.M3Proofs.mirror_mirror --out RUN
./scripts/rocq2lean translate --input RUN/source.ndjson --out RUN
./scripts/rocq2lean verify    --run RUN
./scripts/rocq2lean status    --run RUN
```

Suite results of the clean rebuild (checks passed): doctor ✓, smoke 7, m1 24, m2 14, m3 22,
negative 11, holdout 5, root-contract 40, artifact-integrity 37, universe-audit 26, lowering-audit
32, source-metadata 10, cli-status 30, assumptions 7, holdout2 21. Failed checks: 0.

## Changed files (this pass, `e1a8fde..HEAD`)

* **Implementation:**
  * `Rocq2Lean/Command.lean` (request validation, report 0.3)
  * `Rocq2Lean/Verify.lean` (`roots`, `residual_levels`, `instance_levels`)
  * `Rocq2Lean/Emit.lean` (`mkConstDecl`, `justifyResiduals`, residual record)
  * `Rocq2Lean/Kernel.lean` (`checkOnly`)
  * `Rocq2Lean/Translate.lean` (generic residual variant; deprecations)
  * `tools/rocq2lean.py` (toolchain fingerprint, `status`, roots check in `translate`, inspect diagnostics)
  * `tools/audit.py` (requested-spelling and status checks, `InstanceLevels`, `check_residuals`)
  * `tools/preflight.py` (static blockers with paths)
* **Tests:**
  * `tests/hardening/check_root_contract.py`, `check_artifact_integrity.py`, `check_cli_status.py`,
    `check_universe_audit.py`, `check_lowering_audit.py`
  * `tests/lib.py` (`forge_run`)
  * `tests/smoke/UniverseRules.lean`
  * `tests/holdout2/` (new), `tests/acceptance.py` (new)
* **Fixtures:** `fixtures/universes/UnivResidual.v` (new), `fixtures/lowering/Lower.v` (+`B2`,
  `neg2`), `fixtures/holdout2/` (new, after the freeze). No M1–M3 fixture changed.
* **Scripts:** `scripts/test-holdout2`, `acceptance`, `clean-rebuild` (new); `package-evidence`
  (self-contained); `test-all` (+holdout2).
* **Docs:** `ACCEPTANCE_INVARIANTS.md`, `TRUST.md`, `UNIVERSE_TRANSLATION.md`, `SUPPORT_PROFILE.md`,
  `REPRODUCE.md`.

Commits: `7fe8fa4`, `8430101`, `fdcf38f`, `2c73492`, `afb53bf`, `742b3a9` (freeze), `139cd6e`,
`dbf7c2b`, `7faa5db`, `de0bfcd`, `20a2663`, and the report commit.

## Remaining blockers and limitations (not hidden by the verdict)

* **Fragment.** The fragment is unchanged and blockers are rejected explicitly: mutual or non-direct
  recursion, changed parameters, nested/mutual inductive elimination, coinductives, `SProp`,
  universe polymorphism, primitives.
* **Inductive universe levels.** Global or template levels in **inductive** declarations are not
  generalized, so Corelib `list`/`prod`/`option`/`ex` are still blocked. This remains the next
  extension.
* **Strict inclusion.** A declaration that relies on a strict inclusion between its own levels
  (`Type@{ub} : Type@{uc}`) is rejected honestly by the kernel (R2).
* **Untrusted-but-unrederived parts:**
  * MetaRocq's *term* structure is validated by the independent round trip, not re-derived natively.
  * The auditor ignores binder names and binder info (documented equivalences).
  * `match` indices are a consumer obligation, not an auditor reconstruction.
* **Threat boundary.** Digests detect change inside one workspace and are not signatures. The
  toolchain fingerprint binds the binaries used, not their provenance. The toolchains were not
  rebuilt.
* **Field caveat.** In `reports/clean_rebuild/clean_rebuild.json`, the field `lake_build_from_scratch`
  is computed after the build, so it does not itself prove a cold build. The cold build follows from
  the fresh clone, `.lake/` being git-ignored, and `lake-build.log`, where every module is `Built`
  and none `Replayed` (18 jobs).
* **Not pushed.** The work is committed on `main` in `~/research/Rocq2Lean` on cityu-wsl. Its
  upstream `origin/main` shows as gone, and nothing has been pushed to `jackooo-dddd/Rocq2Lean`.

# Acceptance invariants

Statement mode (current direction): `rocq2lean validate` applies G1, G3, G6 (axiom-free library), G7
and the interface gate to every row the translator claims, with the statement-mode detectors and the
statement audit (`docs/STATEMENT_ONLY_DESIGN.md` §8, `reports/statement_only/VALIDATION_REPORT.md`);
roots need not all be translated, and unclaimed rows are reported, not certified. `rocq2lean assemble`
adds the assembly gates of `docs/ASSEMBLY.md` (claimed submissions verified and hash-bound; validated
rows reproduced identically; final theorems exactly their template applied to their prerequisites'
theorems; assembled rows audited with proved tasks as constants; axioms reported per target, within the
allowance). Tests: `scripts/test-statement`, `scripts/test-assembly`. The rest of this file describes
the proof-transport `verify` gate (historical, still tested by `scripts/test-all`).

`rocq2lean verify --run RUN` publishes `verify.json` with `status: VERIFIED` **only if every
invariant below holds**; otherwise it publishes the failure status (atomically) and exits 2.
Each invariant names the component that enforces it and the test that exercises it.

## G1 — Source anchoring
| Invariant | Enforced by | Tested by |
|---|---|---|
| The request is non-empty and duplicate-free after one documented normalization (strip whitespace); raw and normalized requests are recorded | `rocq2lean.py: check_request` | test-root-contract |
| Every root resolves to a constant or an inductive (constructor roots rejected); no two roots resolve to the same declaration | `tools/contract.py` | test-root-contract |
| The IR passed the independent round trip: bodies (`RtEq.v`), opacity, recomputed dependency edges, native metadata (`Rocq2Lean NativeMeta`), native universe facts (`Rocq2Lean CheckRelation`, every ordered pair) | `tools/roundtrip.py` | test-m1, test-source-metadata, test-universe-audit |
| The coverage contract (`contract.json`: run id, IR digest, request, roots, required closure) is bound to the snapshot; manifest, sources, libraries, IR, round-trip result, toolchain lock, **toolchain binaries** (content digests of `lean`, `lake`, `libleanshared`, `rocq`, MetaRocq Template plugins and theories) and implementation tree are unchanged since export | `verify` | test-artifact-integrity |
| The translator refuses an IR whose recorded request is empty, duplicated, resolves two spellings to one declaration or names a non-exported declaration (`ROOT_CONTRACT_REJECTED`, no translation manifest) | `#rocq2lean_import` (`rootContractProblem`) | test-root-contract |

## G2 — Root and closure coverage (contract-driven, never report-driven)
| Invariant | Enforced by | Tested by |
|---|---|---|
| Exactly one result row per exported declaration; no rows for unexported declarations | consumer `coverage`; audit `coverage` | test-root-contract |
| Every requested root is `TRANSLATED_AND_CHECKED`; the report's status is `OK` and its root records (requested spelling, resolved declaration, status) equal the contract's roots in order and the result rows | consumer `coverage` + `roots`, audit, translate CLI | test-root-contract (review counterexamples; 14 cases through `verify` and `translate`) |
| Every declaration of the required closure (recomputed independently by the auditor from the source terms) is `TRANSLATED_AND_CHECKED` or a verified bootstrap rule | consumer, audit | test-root-contract |
| Summary counts are recomputed; at least one declaration is accepted | audit | test-root-contract |
| Extra exported declarations outside the closure are classified `extra_not_required` and never counted | audit | — (none in current fixtures) |

## G3 — Kernel checking and readback
| Invariant | Enforced by | Tested by |
|---|---|---|
| Every accepted declaration was inserted with `Environment.addDeclCore (doCheck := true)`; `debug.skipKernelTC` refused | `Rocq2Lean/Kernel.lean` | test-smoke |
| The IR read by the translator has the contract's SHA-256 (checked in Lean) and the report carries it and the run id | `#rocq2lean_import`, `Sha256.lean` (NIST vectors) | test-artifact-integrity |
| A separate Lean process imports the module and finds each accepted target with the reported kind, universe parameters, type, value / constructors; not unsafe/partial | consumer `presence/kind/levels/type/value/ctors/safety` | test-root-contract, test-assumptions |
| Every constant referenced by an accepted target is an accepted target of the run, a bootstrap target, or a kernel-generated constructor/recursor of one | consumer `target_deps` | test-assumptions |
| Every defaulted universe level is justified: the generic declaration recorded in the report is kernel-accepted here and instantiates at 0 to the imported one | consumer `residual_levels` | test-universe-audit |
| (Evidence, not a gate) the report alone replays into a fresh environment through the kernel | `tools/replay.py` | test-lowering-audit, test-universe-audit |

Importing an `.olean` is a readback, not a re-typecheck from scratch; kernel checking happened at
insertion, and a clean rebuild (`scripts/test-all` in a fresh clone) is separate evidence.

## G4 — Universe interpretation
Rules R0–R4 of `docs/UNIVERSE_TRANSLATION.md`: native facts re-checked (G1), MetaRocq's own
constraints entailed by them; every universe argument at every reference to a generalized constant
satisfies coherence / no-raising (R3), checked by the translator (`UNIVERSE_REJECTED`) and
independently by the auditor (`universe`); defaulted levels only with a kernel-checked
justification (R3′: translator, auditor `universe`, consumer `residual_levels`); typing-determined
levels of `Eq`/`Eq.refl`/`Eq.rec` and of large recursor motives recomputed by the auditor
(`instance_levels`, deferred count reported) and checked at every occurrence by the consumer
(`instance_levels`). Solver diagnostics recorded. Tested by test-universe-audit and
`tests/smoke/UniverseRules.lean`.

## G5 — Case/Fix fidelity
The auditor compares, for every lowered `match`/`fix`: recursor identity and universe-argument
count (kernel metadata), parameters, motive binder types and motive body, every minor binder type
(fields, recursive results, `Q`) reconstructed from the kernel recursor type (modulo β and binder
names), minor bodies with recursive calls mapped to their recursive results, the major premise,
trailing arguments, and for `fix` the parameters/indices from the decreasing argument's source
type. Indices of a `match` (not stored by Rocq) are the obligation `rec_indices` checked by the
consumer at every recursor application. Erased casts were validated (`isDefEq`) before erasure.
Tested by test-lowering-audit (mutations classified by kernel replay): type-correct mutations
(recursive-result order, trailing-argument order, swapped minors, a match using its recursive
result, decreasing argument swapped with a trailing one, a changed recursive-call argument) are
kernel-accepted and audit-rejected, and four of them are also driven through `rocq2lean verify`
on synchronized forged runs (module rebuilt from the mutated report by the kernel): the consumer
agrees with the report and the structural audit rejects.

## G6 — Assumptions
Every accepted declaration has an empty transitive axiom set (`collectAxioms`), standard Lean
axioms included. Tested in isolation (synchronized forged module) by test-assumptions.

## G7 — Artifact freshness and publication
Each phase locks the run (`RUN_BUSY` for a second writer) and invalidates all downstream
artifacts before any other work; `verify.json` is written atomically; a failure publishes its
status; an interrupted run publishes nothing; all bound hashes are recomputed after the checks
and must equal those read before. Tested by test-artifact-integrity.

## G8 — Currency of a published result
`rocq2lean status --run RUN` (read-only) recomputes every digest `verify.json` is bound to and
answers `VERIFIED_CURRENT` (exit 0) only if all are unchanged; otherwise `STALE` or `NOT_VERIFIED`
(exit 2). Tested by test-artifact-integrity (source edited and restored, module changed, artifact
deleted, failed re-verification).

## CLI
`0` success (for `inspect`/`preflight`: every root is a candidate); `2` rejection or known
blocker (status printed; `inspect` prints structured diagnostics: blocked declaration, dependency
path, reasons, node paths); `3` invalid input or tool failure. Tested by test-cli-status (every M3
negative root, a blocker reached through a dependency, relaxed source checking).

## Threat boundary
Hashes detect changes relative to an anchored request inside one workspace. They do not
authenticate a workspace in which an adversary replaces sources, tools *and* every recorded
digest; no signing is claimed.

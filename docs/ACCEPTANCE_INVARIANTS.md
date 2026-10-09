# Acceptance invariants

`rocq2lean verify --run RUN` publishes `verify.json` with `status: VERIFIED` **only if every
invariant below holds**; otherwise it publishes the failure status (atomically) and exits 2.
Each invariant names the component that enforces it and the test that exercises it.

## G1 — Source anchoring
| Invariant | Enforced by | Tested by |
|---|---|---|
| The request is non-empty and duplicate-free after one documented normalization (strip whitespace); raw and normalized requests are recorded | `rocq2lean.py: check_request` | test-root-contract |
| Every root resolves to a constant or an inductive (constructor roots rejected); no two roots resolve to the same declaration | `tools/contract.py` | test-root-contract |
| The IR passed the independent round trip: bodies (`RtEq.v`), opacity, recomputed dependency edges, native metadata (`Rocq2Lean NativeMeta`), native universe facts (`Rocq2Lean CheckRelation`, every ordered pair) | `tools/roundtrip.py` | test-m1, test-source-metadata, test-universe-audit |
| The coverage contract (`contract.json`: run id, IR digest, request, roots, required closure) is bound to the snapshot; manifest, sources, libraries, IR, round-trip result, toolchain lock and implementation tree are unchanged since export | `verify` | test-artifact-integrity |

## G2 — Root and closure coverage (contract-driven, never report-driven)
| Invariant | Enforced by | Tested by |
|---|---|---|
| Exactly one result row per exported declaration; no rows for unexported declarations | consumer `coverage`; audit `coverage` | test-root-contract |
| Every requested root is `TRANSLATED_AND_CHECKED`; the report's root records agree with the contract and with the result rows | consumer, audit | test-root-contract (review counterexamples) |
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
| (Evidence, not a gate) the report alone replays into a fresh environment through the kernel | `tools/replay.py` | test-lowering-audit, test-universe-audit |

Importing an `.olean` is a readback, not a re-typecheck from scratch; kernel checking happened at
insertion, and a clean rebuild (`scripts/test-all` in a fresh clone) is separate evidence.

## G4 — Universe interpretation
Rules R0–R4 of `docs/UNIVERSE_TRANSLATION.md`: native facts re-checked (G1); every universe
argument at every reference satisfies coherence / no-raising (R3), checked by the translator
(`UNIVERSE_REJECTED`) and independently by the auditor (`universe`); defaults and solver
diagnostics recorded. Tested by test-universe-audit and `tests/smoke/UniverseRules.lean`.

## G5 — Case/Fix fidelity
The auditor compares, for every lowered `match`/`fix`: recursor identity and universe-argument
count (kernel metadata), parameters, motive binder types and motive body, every minor binder type
(fields, recursive results, `Q`) reconstructed from the kernel recursor type (modulo β and binder
names), minor bodies with recursive calls mapped to their recursive results, the major premise,
trailing arguments, and for `fix` the parameters/indices from the decreasing argument's source
type. Indices of a `match` (not stored by Rocq) are the obligation `rec_indices` checked by the
consumer at every recursor application. Erased casts were validated (`isDefEq`) before erasure.
Tested by test-lowering-audit (mutations classified by kernel replay).

## G6 — Assumptions
Every accepted declaration has an empty transitive axiom set (`collectAxioms`), standard Lean
axioms included. Tested in isolation (synchronized forged module) by test-assumptions.

## G7 — Artifact freshness and publication
Each phase locks the run (`RUN_BUSY` for a second writer) and invalidates all downstream
artifacts before any other work; `verify.json` is written atomically; a failure publishes its
status; an interrupted run publishes nothing; all bound hashes are recomputed after the checks
and must equal those read before. Tested by test-artifact-integrity.

## CLI
`0` success (for `inspect`/`preflight`: every root is a candidate); `2` rejection or known
blocker (status printed); `3` invalid input or tool failure. Tested by test-cli-status.

## Threat boundary
Hashes detect changes relative to an anchored request inside one workspace. They do not
authenticate a workspace in which an adversary replaces sources, tools *and* every recorded
digest; no signing is claimed.

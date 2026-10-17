# Proposal 2: a per-declaration universe solver

Status: **plan adopted 2026-10-17** (user). Nothing is implemented. Stages A → D, each recorded (changes,
tests, coverage, timing) and reviewed before the next. Companion: `docs/ULIFT_PROPOSAL.md` (proposal 1).

## 1. Goal

Replace the repeated universe-assignment search of the tier ladder (`it`, `cu`, `lo`, `un`, `jo`, … variants,
re-elaborated per attempt) by joint constraint solving for one declaration and its references, using the
already-translated signatures of its dependencies. No whole-library optimization at first.

The acceptance policy does not change. Structural and representation rules stay as they are: R-SPLIT,
R-CARRIER, R2B-V, P, Q-a, T, E, termination lowering, δ-inlining, P3. The solver chooses only among
assignments some existing tier could produce; it introduces no splitting, lifting, specialization or
assumption. **No lift in this proposal** (that is proposal 1).

## 2. Measured motivation (S17)

| Part of translation time | Seconds | Share |
|---|---|---|
| first attempt of each declaration | 5,253 | 32% |
| universe-only tiers | 2,742 | 17% |
| term-changing tiers (`p3`, `ph`, `pl`, `de`, `eq`), with universe variants (`p3` ×3, `p3,ph` ×4) | 8,373 | 51% |

* Speed: the solver helps where one extraction serves several universe variants of the same term. Upper
  bound about 40–45% of attempt time, minus solver overhead. S21 also shows time concentrated in few large HB
  declarations (one took 881 s), so attempts must be profiled by phase before claiming gains.
* Coverage hypothesis: 160 of S17's 245 direct failures are R2B "proof-local level solved by typing, native
  fact violated". The greedy unifier picked one solution; another may satisfy the facts. Where none exists in
  the encoding, the certificate names the cumulativity use, which is proposal 1's input.

## 3. Variable classes (each keeps its existing rule)

| Class | Rule |
|---|---|
| own levels `u_l` | rigid parameters |
| R2F readings `ι l` | determined by the source facts |
| implicit levels (R3G, R3G-F) | new parameters |
| proof-local levels (R2B) | assignable; native facts must hold under the solution; minimal model if unconstrained |
| template levels (R5) | determined by the argument; exempt from R3 |
| `Eq` / motive levels (R4, R8) | determined by typing |
| residual levels (R3′) | defaults that need the kernel justification |
| R-SPLIT / R-CARRIER copies | fixed by representation |

`imax` and Prop sorts are handled explicitly. A satisfying integer assignment is not enough: generated
declarations must type-check for all remaining parameters. Rocq facts justify mappings and readings; they never
become assumptions available to Lean's kernel.

## 4. Encoding and certificates

* Level expressions normalize to `max(c, u_i + k_i)`. With offsets bounded by K (part of the stated
  encoding), a metavariable is a vector of per-parameter offsets, and an equality that must hold for every
  parameter value is a componentwise comparison of normal forms: a small finite problem.
* Preference order, chosen to reproduce the ladder: (1) required generality (hard); (2) the earliest tier that
  would accept (strict before cumulativity); (3) fewest identifications; (4) fewest defaults; (5) a fixed
  tie-break in source-level order. More parameters is not by itself more faithful, and no unique most-general
  solution is assumed.
* Every solution is labelled with the existing rule (tier) that justifies it, so the current per-rule audit
  checks apply unchanged.
* Outcomes: SOLVED (with a witness), **UNSAT_FOR_ENCODING** only with an independently checked certificate —
  a derivation chain (typing forces `x = y`; a fact needs `x < y`, or generality needs `x` free) checked by a
  small independent Python checker — and **UNKNOWN** for unsupported forms, incomplete extraction, timeouts or
  exhausted bounded search. An unsat core alone is not a certificate; infeasibility in the encoding does not
  mean no translation exists.
* Placement: solver in Lean inside the translator (native); witness and certificate checker in Python on the
  audit side (two independent implementations, as elsewhere).

## 5. Stages

| Stage | Work | Acceptance |
|---|---|---|
| **A. Extraction (shadow mode)** | Generate constraints from the target term the translator builds (a level-only type inference over the term, metavariables as symbols; Lean core's `isLevelDefEq` has no hook and assigns eagerly). Capture typing equalities, source-level mappings, R3 reference conditions, coherence and generality obligations, each with source declaration and term position. Profile each attempt by phase (term build, `Meta.check`, kernel). No translation change. | (a) Accepted assignments satisfy the extracted system. (b) The converse: other assignments satisfying the system are kernel-accepted; a kernel rejection is a reported extraction gap. (c) An independent checker rejects forged assignments: protected-level pinning, unjustified identification, disallowed reference arguments. (d) Agreement rate between the solver's answer and the tier that won, over all accepted declarations. |
| **B. Solver** | Symbolic solving for the choices of `it`/`un`/`lo`/`jo` within their eligibility conditions; representation and dependency signatures fixed; occurrence-level metavariables solved jointly; deterministic witnesses. Behind a feature flag, ladder kept as fallback. | Every previously claimed row byte-identical (differences only on rows that failed before); kernel, consumer and audit pass. Measured: solver time, fallback rate, kernel checks, end-to-end time on retry-heavy cases (not just attempt counts). |
| **C. HB frontier** | The GEL/ELF frontier **re-derived from S21** (Stage 6 changed it) with the dependencies needed to reproduce it. Each failure classified: legal assignment found / certified conflict / unsupported form / timeout. No representation change to unblock a case. | Newly supported declarations and downstream protected roots with audited evidence; each certified conflict explained by its typing constraint and policy obligation. Shapes A and C (copies, forced binder levels) are expected to yield mostly certified conflicts — proposal 1's input, not a failure. |
| **D. Full corpus** | Same 4,474 protected roots and all claimed rows; compare with S21 and with the frozen pre-change implementation; all statement suites, `test-all`, consumer, audit, provenance, `test-p0` request independence; two runs for determinism. | No protected root or claimed row lost; no invalid acceptance; all gates pass; changed outputs accepted only with verified correspondence and preserved generality. Report coverage, runtime, solver overhead, fallback rate, representative diagnostics. |

## 6. Invariants

* Request independence (the P0 lesson): constraints come only from the declaration's own closure, never from
  facts of whatever libraries a request loads.
* Determinism: identical output across runs.
* No source proofs, no generated corpus proofs, no axioms or `sorry`, no lift. Old audit checks stay during the
  prototype.

## 7. Process and order with proposal 1

Baseline S21 with Stage 6 merged. Branch from `main` after that merge; merge `main` into the branch before any
squash. Commit on the branch; merge into `main` and push only with approval. Suggested order: A → B here, then
proposal 1's Phase 1 using these certificates, then C → D here together with proposal 1's measurement.

# Proposal 1: a general Type-to-Type lift for Rocq cumulativity (rule U)

Status: **plan adopted 2026-10-17** (user). Nothing is implemented. The rule itself is adopted only after
Phase 1 (diagnosis and design, `docs/ULIFT.md`) is reviewed and approved, as for rules P, Q, T and E.
Companion: `docs/UNIVERSE_SOLVER_PROPOSAL.md` (proposal 2), whose certified conflicts are this rule's input.

## 1. Problem

Rocq types `A : Type@{i}` at `Type@{j}` whenever `i ≤ j` (cumulativity). Lean has no cumulativity: a term is
well typed only at its exact universe, so the translation must *equate* levels that Rocq only *orders*. When
that equation violates a source fact or the generality requirement, the declaration is refused. Today each
recurring shape has its own rule or tier (R3↑, R2B-P, R2B-S, R3↓, R-SPLIT, R-CARRIER copies, rule E, …).

Measured on S17 (245 direct failures, 205 unclaimed protected roots):

| Failing check (from the final message) | Direct failures |
|---|---|
| proof-local level solved by typing, native fact violated (R2B) | 160 |
| coherence on a shared level (upper bound) | ≤ 31 |
| kernel type mismatch | 13 |
| defaulted level not justified (R3′) | 11 |
| no raising (R3) not entailed | 9 |
| other (course-of-values, binder levels, narrowing, …) | 21 |

Rule U is meant to be the one reusable mechanism for the cumulativity part of this, replacing future
case-by-case universe rules.

## 2. The rule (to be fixed in Phase 1)

Where every existing tier fails *because* Lean requires a level equality at a point where Rocq used
`Type@{i} ≤ Type@{j}`, insert an explicit lift at that point: `ULift.{r,s} A : Type (max s r)` (or `PULift`,
see §5) with `ULift.up` / `ULift.down` at the boundary of the lifted occurrence.

Lifts come in kinds with different soundness arguments. **Only the first kind is in scope.**

| Kind | Example | Correspondence | Scope |
|---|---|---|---|
| **Value lift** — a type used as a value at a larger sort; `up`/`down` at the boundary; the declaration's *type* is the source image | REFERENCE_RAISING: keep `c` at the source level `i`, lift its result to `j` | generic: `down (up x) ≡ x` (projection), `up (down y) ≡ y` (structure η) | **in scope** |
| Carrier lift through a type former | COUPLED_BINDER_LEVELS: `list_R (ULift A) (ULift B)` | needs a commutation lemma per type former (a corpus proof) | blocked; counted |
| Lift of a structure carrier | HB `Zmodule.type`, `Equality.type` instances (GEL frontier) | every operation and axiom field must be transported; axiom fields are proofs | blocked; counted |
| Sort annotation in a statement | `@eq (… → Type@{j}) X Y` | not a lift | rule E |

A context that cannot be transported with value lifts stays blocked. The translator writes no proofs: a
transport that would need one is reported, or becomes a proof task, never generated.

## 3. Boundaries

* Unprotected library declarations only (MathComp, CoqEAL, Corelib). Protected declarations — Prosa **and**
  Classic — are never lifted, narrowed or changed.
* A protected statement can keep its text while its meaning changes through an unprotected definition it
  unfolds. Therefore a lift that changes an unprotected declaration's *type* is refused when that declaration is
  in a protected statement's statement closure or conversion dependence (`CONVERSION_DEPENDENCE.json`).
  Type-preserving value lifts inside unprotected bodies are allowed anywhere.
* Last tier only: applied to a declaration that every existing tier rejected, gated on a diagnosed
  cumulativity failure, with its own budget. Every previously claimed row stays byte-identical.
* No axioms, no `sorry`, no Mathlib in the translator or the auditor.

## 4. Correspondence obligations (Mathlib-free, axiom-free)

* **U1** `A ≃ ULift A` with both round trips definitional.
* **U2** a value lift leaves the declaration's type equal to the source image.
* **U3** levels: the lift is no-raising — `i ≤ j` entailed by the source graph — and its target is exactly
  `j`'s image (`max s r` normalizes to it).
* **U4** no lift in a protected declaration's type, statement closure or conversion closure.
* **U5** no generated proof; every needed transport is a reported proof task or the row stays blocked.

Generic lemmas in `tests/statement/proofs/ulift_correspondence.lean`, as for rule P's C1–C5.

## 5. Implementation sketch (Phase 2, after approval)

* Reuse rule P's architecture (value lift, term-level `up`/`down` at casts, application arguments, the value
  against its declared type, `match` scrutinees).
* **Option to decide in Phase 1:** reuse `PULift.{r,s} (α : Sort s) : Sort (max s r 1)` for Type as well, so
  rule P's consumer allowlist (`docs/TRUST.md`), audit stripping (`strip_prop_lift`, `peel_lift_coercion`) and
  proofs extend, instead of adding a second primitive.
* Report fields per row: lifted occurrences, their source levels `i ≤ j`, their kind.
* Independent audit: strip lifts with the level check of U3, require every lift to be reported, check U4
  against the recomputed closures.

## 6. Tests

Fixture with real shapes (one REFERENCE_RAISING member, one GEL frontier member, one CoqEAL obligation) and
forged-row negative controls, each audit-rejected: wrong level; raising (`i ≤ j` not entailed); a lift in a
protected statement; an unreported lift; a lift of a Prop (rule P's domain); a lift of a type former's argument;
a type-changing lift without a report. All existing statement suites and `test-all` unchanged.

## 7. Phases and measurement

1. **Diagnosis and design** (no translator change): for each member of SOLUTION_FACT_VIOLATED (144 roots),
   REFERENCE_RAISING (83) and COUPLED_BINDER_LEVELS (71), and the GEL/order frontier re-derived from S21,
   locate the cumulativity use (term position, `i ≤ j`) and classify it by the kinds of §2. Proposal 2's
   certificates give these directly when available. Output: `docs/ULIFT.md` with counts per kind and the
   roots each kind could unblock alone. **Stop for approval.**
2. **Implementation** of value lifts only, with U1–U5, audit and tests.
3. **Measurement:** targeted fixtures, statement suites, `test-all`, full corpus against S21 (Stage 6
   merged): newly supported declarations and roots, attribution by ablation, remaining blockers by kind,
   regressions (must be 0), audit and consumer results, translation time per tier.

Expected effect (unproven): mostly REFERENCE_RAISING; part of SOLUTION_FACT_VIOLATED; little of
COUPLED_BINDER_LEVELS and of the GEL frontier (carrier lifts). Phase 1 measures this.

## 8. Process

Branch from `main` after Stage 6 is merged; merge `main` into the branch before any squash (the squash of a
stale branch tree deleted ITERATION_LOG entries 12–13). Commit on the branch; no merge into `main` and no push
without approval. ITERATION_LOG entry per phase.

# R-OCC: per-occurrence levels for body-only levels of a definition

Status: **approved 2026-10-18** (a last tier; corpus measurement in `reports/statement_only/ITERATION_LOG.md`,
entry 18).

## 1. The failure

A *body-only* level of a definition is a global level that occurs in the definition's value and not in its
type (rule R2B; "proof-local"). Rocq types every occurrence `Type@{m}` of such a level by cumulativity: each use
only needs `l ≤ m` for the level `l` it holds, so one `m` above all of them serves every occurrence.

The translation reads the level as one level metavariable for the whole declaration. Lean has no cumulativity,
so each occurrence must *equal* the level it holds, and one metavariable cannot equal several different levels.
Unification then identifies those levels, or fails.

* CoqEAL `refines_apply` (and `refines_abstr`): the proof rewrites three relations with `eq_rect_r` at the type
  `∀ m n, Type@{38671}`: `hrespectful … R R'` (level `max (38756, 38757, …)`), `R` (`38758`) and `R'` (`38763`).
  The one metavariable for 38671 identified the statement's relation levels 38758 and 38763 with
  `max (38756, 38757)`; the defaulted residuals were then kernel-rejected. 48 and 30 protected roots have these two
  among their blockers, 10 of them only these two.
* Classic `powerset`: the level 24 of the inner `seq` is forced to `0` by one occurrence, but `Set < 24` in the
  source.

## 2. The rule

On a last tier for definitions (statements have no translated value), after every other tier failed:

1. **Copies.** Every sort occurrence `Type@{m}` of a body-only level `m` in the value gets a fresh level
   metavariable (a *copy* of `m`), solved by Lean's unifier like any other. References to declarations that share
   `m` keep the declaration's one variable for `m` (coherence by construction is unchanged).
   R2B-V result-sort levels are excluded: the declared result sort is read from the value.
2. **Defaults.** A copy left free defaults as `m` does (its minimal model, R2B/R3′). The level `m` itself, when all
   of its occurrences are copies, is its minimal model over the current values of the other levels (type levels,
   solved body-only levels, and the parameter `u_a` of a lower bound `a` that is a parameter of the declaration
   without being one of its explicit levels: `powerset`'s `eqtype.51`, an R3G implicit level).
3. **Check.** Every copy `σ` satisfies the *upper-bound* facts of `m`: `σ + k ≤ b` for each native fact `m ≤ b`
   (`k = 0`) or `m < b` (`k = 1`), `b` read as its solution when solved and as itself otherwise. The level `m` keeps
   R2B's check of all its facts.
4. **Report.** The row carries the diagnostic `body-occ` (`universe_diagnostics`).

The tier tries the plain ladder variants with and without per-instance prerequisite hypotheses (P3: a pending
dependency used at several now independent occurrences needs one hypothesis per instance), and the R-CARRIER
no-split variant for unprotected declarations.

## 3. Correspondence

* **The statement is unchanged.** Copies occur only in the value; every level of the type is a parameter or
  solved exactly as on the other tiers, and the generality and binder-independence checks apply as before.
* **Each copy is a reading of its occurrence.** Rocq checked the occurrence at `m` with the held level `l ≤ m`;
  the copy is `l` (what Lean's typing needs there). The upper-bound facts of `m` hold for the copy, since the copy
  stands for a level at most `m`, and they are checked. Lower-bound facts of `m` (`a ≤ m` from other occurrences)
  are not facts about this occurrence and are not required of the copy, the same reading as R-SPLIT's copies.
* **The value is kernel-checked** at the copies, and the audit re-derives the acceptance of every copied sort.

## 4. Independent audit

`tools/audit.py` (`body_copy_ok`), for reports with `body-occ` rows: a target sort `Sort (σ+1)` at a source sort
`Type@{m}` of a body-only level `m` (one summand, offset 0, not a motive level) is accepted when the reported
solution of `m` does not match it and σ is a level over the source levels' parameters satisfying every native
upper-bound fact of `m` (every one, not only those among the declaration's levels: stricter than the translator).

## 5. Scope

A last tier: only declarations that fail every other tier are retried, so no accepted row and no dependant of one
changes. Protected definitions use it like any other tier; their statements are never specialized by it.

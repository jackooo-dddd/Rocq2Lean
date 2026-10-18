# Rules of 2026-10-18: carrier pins, level identification, the Set floor, convoys, and their companions

Status: **approved 2026-10-18** (C-PIN and L-IDENT explicitly; the rest under the user's standing approval of the
same day, "add reasonable rules, no need to ask"). Each rule is a *last tier* or a retry after a refusal: only
declarations that fail every earlier tier are retried, so no accepted row and no dependant of one changes. Each is
reported in the row (`universe_diagnostics`) and re-derived by the independent audit (`tools/audit.py`). While
measured one by one (incremental runs from B2, `ITERATION_LOG.md` entry 19) each sits behind a switch
`R2L_RULE_*`; the switches are removed when the rules are adopted together.

## 1. C-PIN: carrier pins (`R2L_RULE_CARRIER_PIN`)

**Shape.** A structure instance packs a concrete carrier (`int : Set`, `'I_n : Set`) at a monomorphic level `c`
that the source leaves free above the carrier's level; Lean has no cumulativity, so the reference fixes `c` to the
carrier's level `k`, and the generality check refused the statement ("the level of `c` is free in the source but
its argument is `k`").

**Rule.** At a reference in a statement, a closed argument `k` for a level `l` free in the source is accepted when
the source graph does not force `l` above `k` (with R-SET's reading of `Set < l`, §3). For a **protected** statement
only at a constant that is a *term* (its type does not end in a sort: a concrete instance such as
`fintype_ordinal__canonical__eqtype_Equality`): no binder ranges over such a constant, so no quantification range is
narrowed (P0). Pins at type formers (`Equality.type`, `concrete_job`) of protected statements stay refused.

**Correspondence.** The Lean statement is the Rocq statement at a model of the source graph in which the instance's
level is `k`; for a closed instance the statement's content does not depend on the universe the instance is packed
in. Reported `carrier-pin: <constant>`; the audit accepts exactly the reported pins and re-checks the condition.

**C-PIN-M (`R2L_RULE_CPIN_MODEL`).** The same at a non-closed argument σ: accepted when σ, read with the reference's
other arguments, satisfies every native fact between `l` and the referenced constant's other levels (Set facts by
§3), i.e. the reference is the constant at a model of its own levels' facts (`Builders_62_T__canonical__Order_Preorder`
at `preorder.119 :=` its class reading). Any constant of an unprotected statement; term constants of a protected one.
Audit: `pin_model_ok`.

## 2. L-IDENT: level identification in unprotected statements (`R2L_RULE_LEVEL_IDENT`)

The binder-independence check refuses a statement whose translation forces `b₁ ≤ b₂` between two of its binder
levels without the source entailing it. For an **unprotected** statement the identification is accepted when the
source does not force `b₂ < b₁` (the statement is then read in a model of the source graph where `b₁ ≤ b₂`).
Reported `level-ident: b₁ <= b₂`; the audit (`check_binder_independence`) accepts exactly the reported pairs and
re-checks them. Protected statements: unchanged.

## 3. R-SET: Rocq's structural Set floor (`R2L_RULE_SET_FLOOR`)

Rocq places every named universe level strictly above `Set` by construction (`Set : Type@{l}` for every `l`); all
1,207 levels of the corpus export carry `Set < l`. Lean has no such floor (universe parameters are instantiated at
0 everywhere). For a level that no **named** level forces strictly up (no fact `a < l` with `a ≠ Set`), the fact
`Set < l` is read as `Set ≤ l`:

* a body-only level's solution may be 0 (Classic `concrete_taskset`: `eqtype.51`);
* a carrier pin (§1) may be at 0 (`ssrint`'s `choice.333`, Classic `ssrbool.1169`).

Levels with a named strict lower bound (`eqtype.58`, the class level of `Equality.type`, 303 of them) are unaffected.
The kernel still checks every term: a term that needs `Set : Type@{l}` is rejected there. Reported `set-floor: l`;
audit: `NAMED_STRICT`, `SETFLOOR`.

## 4. R-COPYDIAG: copied facts on the diagonal (`R2L_RULE_COPY_DIAG`)

R-CARRIER / R-SPLIT give a source level one copy per independent operand (`choice.299__c0`, `__c1`), each with the
level's facts. A solved level `m` read through one operand's copies (`preorder.119 := max (299__c0, …)`) fails the
copied fact of another (`299__c1 ≤ 119`). In the source all copies are one level; on that diagonal the facts hold,
and the copies only add generality beyond the source. When the check of a solved level fails on a copied fact, it
is re-checked with every copy read as its source level. Reported `copy-diag: m`; the audit re-derives it.

## 5. R-P3RES: residual levels with per-instance hypotheses (`R2L_RULE_P3_RESID`)

The P3 tier (one prerequisite hypothesis per instance) refused declarations with residual levels. They are now kept
as parameters, kernel-justified at every value as any residual; the generic version recorded for the residual check
is collapsed with the same kept binders and duplicate map (`collapseHypsBy`), so the consumer and the audit compare
one declaration.

## 6. R-CONVOY: match convoys before the structural lowering (`R2L_RULE_CONVOY`)

Paramcoq's parametricity lemmas (`map_R`, `filter_R`, …) recurse through a convoy: `let K := cons_R … s_R in
(λ s1' s2' s_R', match s_R' …) _ _ K`, whose recursive call is on a field of `K`, i.e. on `s_R`. Rocq's guard sees it
by reduction. When the structural lowering fails on a call that is not a direct field, the body is βζι-reduced at
convoys (a `let` bound to a constructor application inlined, an applied λ β-reduced, a `match` on a constructor
application ι-reduced; all definitional) and the structural lowering retried, before the course-of-values and
accessibility lowerings. The audit compares a fixpoint against the reduced source when the direct comparison fails
(`convoy_reduce`, an independent copy). Measured alone from B2: +9 protected roots, 0 regressions.

## 7. R-PGATE: rule P for relation mismatches inside a residual check (`R2L_RULE_P_GATE`)

Rule P's tier (approved, `docs/PROP_LIFT.md`) is also tried when a universe-rejected row's residual-default check
failed on a kernel application mismatch at `… → Prop` (CoqEAL `Rnat_div_eucl` obligations: `prod_R` given the
δ-unfolded `Rnat`). The η-lift of a λ-relation is β-reduced (`fun xs => PULift (b[xs])`), the form the audit compares.

## 8. Candidates measured, not (yet) adopted

* S-FREE (`R2L_RULE_SHARED_FREE`): one metavariable per non-own source level at every reference (stage C).
* R-OCC + rule P (`R2L_RULE_OCC_LIFT`).
* Full-budget retry of budget-aborted attempts (`R2L_RETRY_ABORTED`, solver stage B).
* R-COVWF (`R2L_RULE_COV_WF`): ineffective (the accessibility lowering does not take indexed inductives either).

Their per-rule numbers are in entry 19.

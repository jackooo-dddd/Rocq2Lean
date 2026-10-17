# Rule E: equalities of convertible terms stated at a cumulative universe

Status: **adopted** (proposed 2026-10-16, approved 2026-10-17; ITERATION_LOG entry 16). Implementation:
`eqLowerMark` and the marked-conclusion case of `trans` (`Rocq2Lean/Translate.lean`), the statement tier
(`Rocq2Lean/Emit.lean`), the consumer's E1 re-check `checkEqLowered` (`Rocq2Lean/Verify.lean`), the audit's
shape recomputation and `eq_lowered_type` marker (`tools/audit.py`). Test: `scripts/test-eq-lowering`.

**Implementation choices (within the approved rule).** Only the statement's *conclusion* (after its
products) is lowered, which is the shape of all four CoqEAL obligations and is simple to re-check. E1 is
discharged **without writing any proof**: the translator checks the operands' convertibility (`isDefEq`), and
the consumer re-checks it independently in its own Lean process; no `rfl` term enters the library (Rocq2Lean
writes no corpus proofs).

## 1. Measured frontier

CoqEAL's core refinement lemmas `refines_abstr` and `refines_apply` are blocked by four obligations of the
same shape. In S18 they affect **49 of the 205 unclaimed protected roots**, and 7 are blocked by them alone
(the rest also wait on other CoqEAL blockers: course-of-values `param.*_R`, residual defaults).

```
refines_abstr__rocq2lean_obligation_1 :
  ∀ (A : Type@{38996}) (B : Type@{38997}) … (R : A → B → Type@{38998}) …,
    @eq (A → B → Type@{38671}) (refines A B R) R
```

(`refines_abstr` obligation 2 and `refines_apply` obligations 2 and 3: identical, with their own levels.)

## 2. Why it cannot be translated today

* `refines A B R` unfolds definitionally to `R` (CoqEAL's `refines` is a class whose only field is the
  relation), so the statement is a reflexivity: Rocq proves it by `eq_refl`.
* It is stated at `A → B → Type@{38671}` (`refines`' own level) while `R` lives at `Type@{38998}`, with
  `38998 ≤ 38996 ≤ 38671` in the source graph: Rocq types `R` at the larger universe by cumulativity.
* Lean has no cumulativity: `@eq (A → B → Type u) X Y` is well-typed only when `X` and `Y` have exactly that
  type. Typing forces `38998 := u_38671`, which violates the source fact `38998 ≤ 38996` (R2S), correctly.
  Every variant (R2F-c, R3↓, per-occurrence coherence, P3) fails for this reason.
* The only well-typed Lean statement uses the operands' universe:
  `@eq (A → B → Type u_38998) (refines A B R) R`. Writing it changes the sort argument of `eq` in a statement,
  which is a lowering of a statement's sort — the general form of which (Q-b) is not adopted.

## 3. The proposed rule E (narrow)

At an application `@eq T a b` in a statement, the type argument `T` (a product ending in a sort written in the
source) is replaced by the operands' own type, **only when `a` and `b` are convertible** (the kernel accepts
`@rfl _ a : a = b` at the lowered type; the audit recomputes the shape from the source: same `eq` head, the
type argument a sort-ended product whose sort is the only difference, operands unchanged). Reported per row
(`eq_lowered`), never on a protected declaration's statement without listing it.

## 4. Why it is sound: equivalence

* When `a` and `b` are convertible, both the source proposition `@eq T a b` and the lowered `@eq T' a b` are
  provable by reflexivity, so they are equivalent (both true) — the same argument as Q-a (every instance of a
  phantom check holds).
* The obligation statements in question are exactly of this form (each is closed by `eq_refl` in Rocq).
* A non-convertible equality is never lowered: there, equality at a larger universe and at the operands'
  universe need not coincide, and that general case (Q-b-like) stays refused.

## 5. Obligations and controls (planned)

| | Obligation | Discharge |
|---|---|---|
| E1 | Convertibility of the operands | the kernel checks `rfl` at the lowered type (a synthetic check per row) |
| E2 | Shape | the audit recomputes: only `eq`'s type argument differs, by its final sort, operands identical |
| E3 | Equivalence | a synthetic Lean lemma: for convertible `a b`, `@eq T a b` and `@eq T' a b` are both inhabited by `rfl` |
| E4 | Protection | rows listed (`eq_lowered`); the rule is not applied to protected statements unless approved separately |

Negative controls: a lowered equality whose operands are not convertible (kernel rejects `rfl`, row
refused); a lowered type argument that changes more than the final sort (audit-rejected); `eq_lowered` on a
row without such an equality (audit-rejected).

## 6. Decision

Approved 2026-10-17: lowering `eq`'s type argument to the operands' universe for equalities of **convertible**
terms in unprotected statements, with E1–E4. Expected effect: CoqEAL's `refines_abstr` /
`refines_apply` obligations, unblocking up to 49 protected roots together with the remaining CoqEAL work
(7 by this rule alone).

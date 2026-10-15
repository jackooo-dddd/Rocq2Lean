# Rule P: lifting a proposition used as a type (Prop ≤ Type cumulativity)

Status: **adopted** (approved 2026-10-15, stage 5; ITERATION_LOG entry 15). Implementation:
`Rocq2Lean/Translate.lean` (`liftCoerce`, `liftCoerceValue`, `coerceArgs`, the cast and `match` sites),
`Rocq2Lean/Emit.lean` (the rule-P tier, `liftChain`), consumer allow-list (`Rocq2Lean/Verify.lean`),
independent audit (`tools/audit.py`: `strip_prop_lift`, `peel_lift_coercion`, `peel_eta`, the
`prop_lift_unfold` recomputation, the C5 listing). Test: `scripts/test-prop-lift`.

## 1. The failure

CoqEAL `refinements.hrel.fun_hrel` (KERNEL_OTHER; 17 protected roots blocked by it alone, 68 affected at S8):

```
Definition fun_hrel A B (f : B -> A) : A -> B -> Type@{1062} := fun a b => f b = a.
```

* The value `f b = a : Prop` inhabits `Type@{1062}` only through Rocq's cumulativity `Prop ≤ Type`.
* Lean has no such cumulativity. `Prop` is not below `Type u`, so the translation is ill-typed: the
  kernel reports a declaration type mismatch, `… → Prop` against `… → Type u_1062`.
* R2B-V (result sort from the value) refuses it explicitly, because the value is a proposition.
* Declaring `fun_hrel` at `Prop` would break every use. CoqEAL's `refines` takes relations
  `A → B → Type`.

## 2. The rule

Where the source uses a proposition `P : Prop` at a type `Type@{l}`, the translation inserts Lean's core
lift `PULift.{l+1, 0} ⟦P⟧ : Sort (l+1)`, which is exactly `Type u_l`. `PULift` is a structure of Lean's
prelude: no axiom, no new constant of ours (the consumer allows `PULift`, `PULift.up`, `PULift.down`
as construction primitives, docs/TRUST.md).

The rule is a **last tier**: it is tried only after the existing ladder failed, with a kernel or universe
rejection or a translation failure of the two shapes the lift explains ("cast annotation is not
convertible", "scrutinee type is not an application of …"). It runs with each of the ladder's variants
(R2F-c, cumulativity, R3↓, per-occurrence coherence). Nothing that translates without it changes.

### 2.1 Value lift (`prop_lift = k`)

A definition declared at `∀ Γ, Type@{l}` whose value is a proposition has its value lifted:
`fun Γ => PULift.{u_l+1, 0} P`. The row reports `prop_lift` = the number of binders (after pending
hypotheses). Example: `fun_hrel := fun A B f a b => PULift (f b = a)`.

### 2.2 Term level (`prop_lift_coercions = n`)

Type-directed, only where the kernel would otherwise see a lifted type against the proposition:

* `e : P` used at `PULift.{r,0} P` (a cast, an application argument, the value against its declared
  type) becomes `PULift.up e`;
* `e : PULift.{r,0} P` used at the proposition `P` becomes `PULift.down e`;
* a `match` whose scrutinee has a lifted type (`h : Rnat a b` matched as the equation it lifts) matches
  `PULift.down h`;
* η-transport: a function used at a function type that differs only by lifts in its domains or codomain
  (an η-reduced proof body, `eq_SnPos_to_nPred := o` with `o`'s statement the proposition) is
  η-expanded with its arguments and result coerced: `fun xs => PULift.up (o (PULift.down x) …)`.

`up`/`down` are only inserted at `PULift.{_, 0}`: the lifted term is a proposition.

### 2.3 Statements with a lifted codomain (`prop_lift_unfold = [c₁, …, cₙ]`)

The exporter states an obligation at the type its position *expects*. For a proof used at `Rnat a b`
(`Rnat := fun_hrel nat N nat_of_bin`), the statement `∀ Γ, Rnat a b` is a `Type` in Lean, not a `Prop`.
Such an **unprotected** statement is stated as its proposition: the head-δ chain of its codomain, from
the head constant to the lifted definition (`[Rnat, fun_hrel]`), is δβ-inlined in the statement (Rocq
conversion: the same proposition), so the codomain is the source proposition `nat_of_bin b = a`. Its
uses get `PULift.up` (2.2). Protected statements are never unfolded (refused by the translator,
rejected by the audit).

## 3. Correspondence obligations

| | Obligation | How it is discharged |
|---|---|---|
| C1 | **Equivalence of the lift.** `PULift P ≃ P`: `down (up h) ≡ h` (ι) and `up (down x) ≡ x` (structure η), both definitional. | `tests/statement/proofs/prop_lift_correspondence.lean` (`toProp_ofProp`, `ofProp_toProp`, `nonempty_iff`), axiom-free, checked by `test-prop-lift`. |
| C2 | **Transport.** Each lifted position is the source's proposition transported along C1: a lifted type occurs exactly where the source has a proposition at a `Type`, `up`/`down` exactly at the uses whose types mismatch by the lift, and an unfolded statement is Rocq-convertible to its source. | Per row, by the audit (independent of the translator): it strips the value lift only at the reported depth where the source type is a `Type` sort and at that sort's image level (`strip_prop_lift`); peels `up`/`down` only in a row reporting coercions, only at `PULift.{_, 0}` (`peel_lift_coercion`); accepts η only as `fun xs => c (f a… c x…)` with the head compared under the extra binders (`peel_eta`); recomputes an unfolding's head chain from the source and compares the statement with the chain inlined. The kernel checks the typing. On the fixture: `frel_eq`, `frel_iff`, `R_iff`, `r2_obligation_lifted`, `r1_down`, `r2_value`, `dmatch_value`. |
| C3 | **No new collapse.** `PULift P` is a subsingleton (its single field is a proof; Lean's definitional proof irrelevance), the identification the translation already makes for every Rocq `Prop`. | `lift_subsingleton`, `prop_subsingleton`; docs/TRUST.md. |
| C4 | **Universe level.** `PULift.{l+1,0} P : Sort (l+1)` is exactly the source's `Type@{l}`; the level stays a parameter (no specialization), checked like any argument; a lifted relation states the same proposition at every level. | `liftAt_eq`, `R_level_indep`; the existing universe checks; audit: the lift's level is the image of the source sort. |
| C5 | **Protected interfaces.** A lifted position in a protected declaration is a range equivalent to the source's (C1), never a narrowed one. | The audit lists every claimed protected row with a value lift or coercions (`prop_lift_protected` in `audit.json`); a protected statement with an unfolded codomain is rejected. |

## 4. Negative controls (`scripts/test-prop-lift`)

Forged rows, each rejected:

* the value lift at a wrong level (kernel and audit);
* a lift depth short of the source's `Type` (audit);
* a lift on a definition whose source type ends in no sort, i.e. no cumulativity there (audit);
* the lift of a type, `PULift.{_, 0} Nat` (kernel);
* a coercion in a row that reports none (kernel-accepted, audit-rejected);
* a coercion at a non-Prop universe (kernel and audit);
* an unfolding that is not the source's head chain, and one reported on a definition (audit);
* unit controls on η peeling (swapped or missing arguments refused) and on coercion peeling.

## 5. Scope and measured effect

The fixture `fixtures/stmt/plift` (synthetic, CoqEAL's shapes) exercises every case above. On the
corpus, the targets are CoqEAL's refinement relations (`fun_hrel`, `Rnat`, the `refine_*` instances of
Prosa's `implementation.refinements`) and the PROP_TYPE_CUMULATIVITY members. The measured gains are in
ITERATION_LOG entry 15. Remaining members of the chain that rule P does not address (universe solving of
`refines`' proof-local level, CoqEAL's course-of-values `*_R` fixpoints, residual defaults) are booked
there as separate frontiers.

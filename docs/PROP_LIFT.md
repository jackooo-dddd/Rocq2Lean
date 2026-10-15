# Proposal (NOT adopted): rule P, lifting a proposition used as a type (Prop ≤ Type cumulativity)

Status: **proposal awaiting approval** (2026-10-15). Nothing here is implemented. This is a new semantic
representation policy, so it needs an explicit decision.

## 1. The failure

CoqEAL `refinements.hrel.fun_hrel` (KERNEL_OTHER; 17 protected roots blocked by it alone, 68 affected):

```
Definition fun_hrel A B (f : B -> A) : A -> B -> Type@{1062} := fun a b => f b = a.
```

* The value `f b = a : Prop` inhabits `Type@{1062}` only through Rocq's cumulativity `Prop ≤ Type`.
* Lean has no such cumulativity. `Prop` is not below `Type u`, so the translation is ill-typed: the
  kernel reports a declaration type mismatch, `… → Prop` against `… → Type u_1062`.
* R2B-V (result sort from the value) refuses it explicitly, because the value is a proposition.
* Declaring `fun_hrel` at `Prop` would break every use. CoqEAL's `refines` takes relations
  `A → B → Type`.

## 2. The proposed rule P

Where the source uses a proposition `P : Prop` at a type `Type@{l}` (Prop ≤ Type cumulativity), the
translation inserts Lean's core lift `PULift.{l+1, 0} ⟦P⟧ : Sort (l+1)`, which is exactly `Type u_l`.
* `PULift` is a structure of Lean's core library: no axiom, no new constant of ours.
* At the term level, along the same positions:
  * a proof `h : ⟦P⟧` used as an inhabitant of the lifted type becomes `PULift.up h`;
  * an inhabitant `x` of the lifted type used as a proof becomes `PULift.down x`.
* The insertion is type-directed: only where the kernel would otherwise see `Prop` against `Type u`.
  It is applied as a last tier, so nothing that translates today changes.

For `fun_hrel`: `fun a b => PULift.{u_1062+1, 0} (f b = a)`, at its declared type. Uses such as
`refines (fun_hrel f)` are then unchanged.

## 3. Semantic correspondence obligations (to be proved or checked before adoption)

| | Obligation | How it would be discharged |
|---|---|---|
| C1 | **Equivalence of the lift.** For every `P : Prop`, `PULift P ≃ P`: `down (up h) ≡ h` (ι) and `up (down x) ≡ x` (structure η), both definitional. | A synthetic, axiom-free Lean proof in `tests/statement/proofs/`, as for R-SPLIT and R-CARRIER. |
| C2 | **Transport of statements.** A translated declaration with lifted positions is the source declaration transported along C1: every lifted type occurrence is matched by `up`/`down` exactly at the uses of its inhabitants, so the target statement is equivalent to the untransported one. | Checked per row. The audit restates the insertion from the source: it accepts `PULift ⟦t⟧` only where the source has `t` at that position, and `up`/`down` only around the matching terms. The kernel checks the typing. |
| C3 | **No new collapse.** `PULift P` is definitionally a subsingleton in Lean (η plus proof irrelevance of `P`). That is the same identification the existing translation already makes for every Rocq `Prop` (Lean's definitional proof irrelevance). | No new discrepancy; recorded in `docs/TRUST.md`. |
| C4 | **Universe level.** `PULift.{l+1,0} P : Sort (l+1)` is exactly the source's `Type@{l}`. The level `l` stays a parameter (no specialization) and is R3-checked like any argument. | The existing universe checks, unchanged. |
| C5 | **Protected interfaces.** A lifted type in a protected binder range is a range equivalent to the source's (C1), not narrowed. | The audit records each lifted position in the row (`prop_lifts`). The protection report lists them, so a protected interface that changed shape is visible. |

## 4. What the audit would have to verify independently

* Each reported lift position is a source subterm whose expected sort at that position is a `Type`.
  The audit cannot infer types. So the position is recomputed from the source structure (the
  declared sort of the binder or result that the term inhabits), and the propositional nature of the
  lifted term is left to the kernel. A lift of a non-proposition would be ill-typed at `PULift.{_, 0}`.
* `up` / `down` occur only at uses of variables of the lifted types, and every such use is
  transported. This keeps the transport complete (C2).
* Negative controls:
  * a lift inserted where the source has no cumulativity (audit-rejected);
  * a missing `down` at a use (kernel- or audit-rejected);
  * a lift at a wrong level (R3-rejected);
  * a forged lift of a type (kernel-rejected at `PULift.{_, 0}`).

## 5. Scope and expected effect

* **Measured:** `fun_hrel` (17 roots alone, about 20 more with other obligations of the CoqEAL
  refinement chain).
* **Possibly affected:** the other PROP_TYPE_CUMULATIVITY members (`CMorphisms.respectful`,
  `iffT_Reflexive`, `subrelation_proper`; 1 root alone, 82 affected). Several of them are actually
  `reverse_coercion` mismatches in HB `axioms_` blocks, which stage 4's δβ-inlining may already fix;
  this will be re-measured after stage 4.

## 6. Decision requested

Approve or reject rule P as a semantic representation policy: `PULift` insertion for
`Prop ≤ Type` cumulativity, with the obligations C1–C5. If approved, it would be implemented on its
own branch with the C1 proof, the audit copy and the negative controls above, and measured on the full
corpus before merging.

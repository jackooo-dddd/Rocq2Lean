# Trust boundary

**Claim supported:** for a `VERIFIED` run, the requested roots and their whole required
dependency closure were translated from these exact exported Rocq 9.3.0 declarations (with their
original proof terms) into Lean v4.33.1 declarations that the Lean kernel accepted, and the
accepted terms satisfy the documented translation rules as checked by an independent auditor
and a fresh-process consumer (`docs/ACCEPTANCE_INVARIANTS.md`). This is an engineering audit,
not a verified compiler; passing fixtures prove nothing beyond them.

## Components

| Component | Role | Why its output is not simply trusted |
|---|---|---|
| Rocq 9.3.0 kernel and universe graph | source of truth (terms, opacity, metadata, universe relations) | — |
| MetaRocq Template quoter (`c18395ad`, unpatched) | turns kernel terms into the serialized AST | round trip against a fresh quotation; native recomputation of metadata and universes (the quoter's *term* structure is not re-derived natively) |
| `rocq/exporter` | serializes the AST and native facts | independent decoder + `RtEq.v`; native `NativeMeta` / `CheckRelation` in a fresh process |
| `tools/contract.py` | coverage contract from the validated IR | the auditor recomputes the closure independently and compares |
| `Rocq2Lean/*.lean` translator | proposes `Expr`/`Declaration`s, solves universe levels | kernel; consumer; independent auditor (structure, universes, lowering); replay |
| Lean v4.33.1 kernel (`lean_add_decl`) | type checking | the only acceptance authority for typing |
| `Rocq2Lean/Verify.lean` consumer | fresh-process readback, coverage, target dependencies, axioms, recursor-index obligation | separate process and module; contract-driven |
| `tools/audit.py` | independent structural / universe / lowering audit | separate implementation and rule tables; uses only source IR, contract, report and kernel recursor metadata |
| `tools/roundtrip.py`, `RtEq.v` | independent IR decoding and comparison | separate implementation |

## Insertion path

Only `Rocq2Lean.addChecked` adds declarations: `Environment.addDeclCore … (doCheck := true)`;
`debug.skipKernelTC` is refused; `addDeclWithoutChecking`, `sorryAx`, generated axioms and
`unsafe`/`partial` target declarations are never produced (the consumer checks safety and the
transitive axiom set). `Lean.addDecl` is not used. The translator's own `partial def`s are
implementation code, not translated mathematics.

## Universe solving

References to generalized constants get fresh level metavariables, assigned by Lean's checker
and unifier (levels only). Solver failures are recorded (`universe_diagnostics`); a residual
level is defaulted to 0 only when the kernel accepts the declaration with that level as a fresh
parameter (R3′, re-checked by the consumer); and **every** resulting argument must satisfy rule R3
(`docs/UNIVERSE_TRANSLATION.md`), checked by the translator and independently by the auditor.
Typing-determined levels (`Eq` template level, large-recursor motive level) are recomputed by the
auditor and checked at every occurrence by the consumer (R4).

## Universe interpretation added in M4 (standard-library inductives and proofs)

* **Template inductives (R5).** The binding of template levels to parameters is read from the Rocq
  kernel's own `template_universes` record (exported natively and re-checked by the fresh-process
  round trip), not inferred from MetaRocq's quotation. Translated at the template defaults' quality
  Type; Prop instances are rejected. Instance levels are forced by the Lean kernel and recomputed by
  the auditor and the consumer.
* **Proof-local levels (R2B).** Body-only levels are solved, not generalized; the solution must
  satisfy the native facts (translator and auditor independently). This changes no statement: only
  levels invisible in the type are solved.
* **Term structure.** Binder construction never β-reduces (`bindFVars`): an independent-audit
  failure exposed that Lean's `mkLambdaFVars`/`instantiateMVars` β-reduce binder types mentioning
  universe metavariables; the translator no longer uses them on translated terms.
* **Fixpoints with changed leading arguments.** The generalized set `G` is decided from the source
  syntax by the translator and recomputed independently by the auditor; binder types, `G`
  arguments and recursive-result applications are compared.

## Lowering of `match` and `fix`

The auditor reconstructs everything it can (G5 of the invariants). Remaining determined-by-typing
fields: the indices of a `match`'s major premise (Rocq does not store them; the consumer checks
at every recursor application that they equal the indices of the major's type, which is the
kernel typing obligation made explicit; indices do not occur in the recursor's ι-reduct), the
motive's universe level and `Eq`'s template level (unique solutions without cumulativity; now
also recomputed by the auditor and checked by the consumer, R4), and erased cast annotations (validated by `isDefEq` before erasure; a cast carries no term content).

## M6 constructions

* **Construction primitives.** The accessibility lowering uses Lean prelude inductives `Acc`,
  `PSigma`, `Exists`, `Or` and `False`, and the convoy lowering uses `Eq` (with their constructors
  and recursors). The consumer's dependency check admits exactly this fixed list in addition to the
  run's accepted closure and the bootstrap targets. They are kernel-defined inductive types; the
  axiom detector still runs on every target, and none is involved in any axiom.
* **What the auditor does not compare** in an accessibility-lowered fixpoint: the carrier `C`, the
  call-graph relation `R`, the well-foundedness proof and the call certificates. `C` is forced by
  the major premise's type; `R` is a proposition and the others are proofs, so none can change
  what is computed. The auditor compares the major premise, the passed-on arguments, the motive
  (the source fixpoint type) and the minor premise's body (the source body, recursive calls as
  `ih ⟨j, a⟩ _ G Q`). A type-correct mutation of the computed result is kernel-accepted and
  audit-rejected (`test-m6`).
* **Convoy lowering.** The auditor checks the shape (parameters, the non-uniform argument, the
  `Eq.refl` convoy, the cast pattern of the return clause, each branch body under its `refl`
  λ, the fields passed on). The inner `Eq.rec` motives only affect typing.
* **Universe rules R6, R2⁺, R3G, R2F-c, R8 and the cumulativity tier**: each has an independent
  copy in the auditor (`docs/UNIVERSE_TRANSLATION.md`). The cumulativity tier is applied only to
  rows the strict rules reject, and is reported per row.
* **Binder names.** Macro scopes are erased from binder names in every translated term (hygienic
  names inherited from Lean's own declarations do not survive the report's string round trip).
  Binder names carry no meaning, and the auditor does not compare them.
* **Native `nparams_rec`.** It is exported from the kernel's `mind_nparams_rec` and re-checked by the
  fresh-process round trip, like the other native fields.

## Assumptions

Success admits no source axioms and no target axioms, including Lean's standard axioms.

## Bootstrap

`nat ↦ Nat`, `eq ↦ Eq`: exact source signatures, target shape and constructor adapter checks,
re-run every translation; bootstrap declarations cannot be requested as roots. No definition or
theorem is ever mapped.

## Source proof usage

Translating the original source proofs is the purpose of the project; the Prosa correspondence
rule `source_theorem_dependency = false` does not apply.

## Threat boundary

Digests detect change relative to an anchored request within one workspace; they do not
authenticate a workspace where an adversary can replace sources, tools and all recorded digests.
The toolchain fingerprint binds the binaries that were *used*; it does not show that those
binaries were built from the locked sources (the toolchains were installed, not rebuilt).

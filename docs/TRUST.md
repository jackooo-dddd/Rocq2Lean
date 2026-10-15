# Trust boundary

**Statement-only claim (current direction).** For a `STATEMENT_VALIDATED` run, every row the
translator claims was kernel-checked at insertion; a fresh Lean process re-read it against the report
(kind, type, value, levels, constructors; no axiom, `theorem`, `opaque` or `sorry` in the library); the
independent audit restated it from the source record (statement view, recomputed prerequisites,
hypothesis telescope, term-by-term comparison, universe rules); and no protected declaration was
specialized. An accepted proposition definition is *not* a proved theorem; a pending artifact is checked
under hypotheses for its unproved prerequisites and is *not* the final public interface; rows the
translator did not claim are reported, not certified. Assembly (`docs/ASSEMBLY.md`) adds final
declarations only from verified, hash-bound submissions, and reports the axioms they bring.

The corpus run (`runs/st-corpus*`) is validated by the same consumer and audit; its source anchoring
is supplied by the per-chunk snapshots, round trips and the corpus manifest
(`reports/statement_only/PROVENANCE.md`), which are retrospective revalidation evidence.

The rest of this file describes the historical proof-transport pipeline (M1–M6, P0), which is kept as
regression evidence.

**Claim supported (proof transport, historical):** for a `VERIFIED` run, the requested roots and their whole required
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
| `Rocq2Lean/*.lean` translator | proposes `Expr`/`Declaration`s, solves universe levels | kernel; consumer; independent auditor (structure, universes, lowering); replay. Since entry 14 it runs as native code (`precompileModules`, loaded with `--load-dynlib`): the same program as interpreted, byte-identical reports on the measured subsets; the build digest covers the native library |
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
  `PSigma`, `Exists`, `Or` and `False`, the convoy lowering uses `Eq`, and the mutual fixpoint
  and course-of-values lowerings use `PProd` and `PUnit` (with their constructors and recursors), and
  rule P (docs/PROP_LIFT.md) uses the prelude structure `PULift` with `PULift.up` and `PULift.down`
  (a proposition lifted to a type; `PULift P` is a subsingleton, the identification Lean already makes
  for every proof, so no new collapse). The consumer's dependency check
  admits exactly this fixed list in addition to the run's accepted closure and the bootstrap
  targets. They are kernel-defined inductive types; the axiom detector still runs on every target,
  and none is involved in any axiom.
* **Accessibility lowering: what is reconstructed and what is argued.** For
  `Acc.rec C R motive intro major wf G Q` the auditor (`check_fix_acc`) checks:
  - *carrier* `C`: rebuilt from the source — `PSigma (λ i : U, I params i)` with level arguments
    `[_, 0]` (a `Prop` family), the index type checked against the decreasing argument's index
    binder and the family body against the decreasing argument's type; or that type itself when it
    has no index;
  - *major premise*: `⟨index, x⟩` (or `x`), the generalized and passed-on arguments, the motive
    (the source fixpoint type), and the minor premise's body (the source body, each recursive call
    as `ih ⟨j, a⟩ cert G' Q'` with `a` compared to the source call's decreasing argument);
  - *call relation* `R`: its shape is one disjunct per source recursive call site (counted on the
    source), each `∃ ctx, y = ⟨j_c, a_c⟩` with `y` the relation's first binder.
  What is *argued*, not reconstructed: the bodies `a_c` inside `R`, the well-foundedness proof `wf`
  and the certificates. Argument (scoped to this lowering): `R` occurs only in the binder types of
  `Acc.rec`'s minor premise and in proofs; the value computed by `Acc.rec` on `intro` is `intro x h
  (λ y r, rec y (h y r))`, and the minor's body (audited against the source) uses the recursive
  result only at the audited call arguments. A different `R` can therefore only make the target
  ill-typed (the certificates must prove `R ⟨j_c, a_c⟩ s` for the audited `a_c`), never change a
  computed value. Executable checks (`test-m6`): replacing `R` by the empty relation is rejected by
  the kernel; a type-correct mutation of the computed result is kernel-accepted and audit-rejected;
  Rocq and Lean compute the same values on 4 inputs (`compute_m6`); the lowering unfolds on an
  open accessibility proof by reflexivity (`search_step0`).
* **ι-generalized fixpoints.** The auditor compares each minor premise with the *whole* source body,
  the decreasing argument denoting `C_k params fields` (an environment entry carrying an ι marker);
  a source `match` on it is compared through branch `k` only, with that branch's binders mapped to
  the minor's fields. ι-reduction is definitional in both systems; the dropped return clause only
  types the match. Mutation: minors of two constructors swapped (type-correct, kernel-accepted,
  audit-rejected).
* **Mutual fixpoints.** The auditor reconstructs the `PProd` motive component by component from the
  functions' source types, the projection chain selecting the defined function, each `PProd.mk`
  component against the corresponding function's branch, and each cross-function call's
  projection. The `PProd.mk` type arguments are forced by kernel typing. Mutations: the wrong
  component as the definition, and a call redirected to the other function (both type-correct,
  kernel-accepted, audit-rejected).
* **ζ of recursive lets; functional recursive fields.** The auditor re-derives the ζ-step on the
  source IR with its own substitution (`zeta_fix_lets`) and compares the inlined calls; a call on an
  applied functional field `g zs` must become `ih zs` with `zs` compared. Mutations: a changed
  generalized argument of an inlined call, and a changed argument of a functional field (both
  type-correct, kernel-accepted, audit-rejected).
* **Course-of-values recursion.** The auditor checks the motive `PProd (M x) (Below x)` (`M` against
  the source fixpoint type; `Below` is the recursor over the motive's argument with the same
  parameters), each minor's first component against the source branch, its second component as the
  chain of the minor's recursive results in field order ending in `PUnit.unit`, each convoyed match
  (`… z r_z`, the passed result being the scrutinee's known result), and each recursive call as the
  first component of the result of the subterm it is on (the canonical projection path for a field
  of a convoyed match). `Below`'s minors and the convoy's domain are forced by kernel typing given
  these audited values. Mutation: a call reading another field's result (type-correct,
  kernel-accepted, audit-rejected).
* **Cast repair (proofs only).** A Rocq cast whose conversion needs a fixpoint to unfold at open
  arguments (Ring_polynom `norm_aux_PEadd`: `norm_aux (PEadd pe1 pe2)` against its unfolded body) is
  not definitional for the recursor-based lowerings (Lean has no primitive fixpoint). When the cast's
  type is a proposition, the translated source proof `c` is transported along case analysis on free
  variables of that type until both sides are definitionally equal:
  `I.rec (λ v, A v → T v) (λ fs ihs h, h | nested) v c`. This is a generated proof implementing the
  lowering's unfolding equation (as Lean's own equation lemmas do), not a replacement proof: the
  auditor requires the recursor's motive level 0 (a proposition), every minor to end in the
  transported proof `h` or a nested repair of it, and audits `c` against the source. A cast on data
  is never repaired.
* **Nested inductives (trivial auxiliary eliminations).** For a single-type nested inductive (Stdlib
  `ZMicromega.ZArithProof`, nesting `list ZArithProof`), Lean's recursor takes one more motive per
  auxiliary type and minors for the auxiliary constructors. A plain match or a structural fixpoint
  that does not recurse through the nesting supplies `λ …, PUnit` and `λ …, PUnit.unit`; the auditor
  checks exactly these shapes, removes them, and audits the rest as for an ordinary inductive (nested
  fields have a recursive result in Lean, and are counted as such).
* **Recursor binder types modulo δ.** The auditor compares the motive's and minors' binder types with
  the kernel recursor's modulo β, binder names and the unfolding of accepted transparent definitions
  (their audited target values; `PolC Z` against `Pol Z`). These types are forced by kernel typing in
  any case.
* **δ-inlining of `Set`-motive constants (a last tier).** Rocq's `Prop ≤ Set` lets
  `well_founded_induction (P : A → Set)` take a `Prop`-valued family; Lean's `Type` does not contain
  `Prop`. A declaration that every other tier rejects is retried with the applications of transparent
  monomorphic constants that have a `Set`-family binder replaced by their source bodies (δβ,
  definitional): the body of `well_founded_induction` is the R8-generic `well_founded_induction_type`.
  The inlined constants are reported (`delta_inlined`); the auditor checks each is such a constant and
  re-derives the inlining on the source before comparing.
* **Convoy lowering.** The auditor checks the shape (parameters, the non-uniform argument, the
  `Eq.refl` convoy, the cast pattern of the return clause, each branch body under its `refl`
  λ, the fields passed on). The inner `Eq.rec` motives only affect typing.
* **Universe rules R6, R2⁺, R3G, R2F-c, R8 and the cumulativity tier**: each has an independent
  copy in the auditor (`docs/UNIVERSE_TRANSLATION.md`). The cumulativity tier is applied only to
  rows the strict rules reject, and is reported per row. **R2B-P has a source obligation** checked
  at verify: for every reported level `m := σ`, Rocq's kernel re-checks the source declaration at
  the instance `m := σ` (`Rocq2Lean CheckInstance`, a fresh `rocq compile`); a failure rejects the
  run. R3↑'s correspondence rule is documented in `docs/UNIVERSE_TRANSLATION.md`.
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

Proof transport (historical): translating the original source proofs was the purpose of that
pipeline. Statement mode: original proofs are never translated; the exporter drops proof bodies and
extracts proof subterms of kept terms as obligations (`docs/STATEMENT_ONLY_DESIGN.md`).

## Public-interface protection (P0)

The protected public interface is every public Prosa v0.6 / Classic declaration and record/class
projection of the pinned inventory (`reports/prosa_inventory/protected_interface.json`, 4,474
declarations; its SHA-256 is pinned in `tools/protected_interface.pin.json`, part of the
implementation tree). Policy: a protected declaration keeps its full source statement whether it is a
requested root or a dependency — no R2B-S result-sort lowering and no R2B-P specialization of a
statement level (there is no approved representation change). Non-protected dependencies keep the
existing checked policy (R2B-P instances re-checked by Rocq at verify).

Enforcement, end to end:

* `export` binds the protected names present in the export (with the manifest digest and policy) into
  the coverage contract, and refuses a missing, altered (digest ≠ pin) or stale (inventory changed)
  manifest;
* the translator (`#rocq2lean_import … contract sha`) reads the binding from the contract and refuses
  a specialization of a protected declaration (`INTERFACE_REJECTED`; dependents are
  `BLOCKED_DEPENDENCY`); each result row records `protected`;
* the fresh-process consumer (`interface` detector) and the independent audit recompute the binding
  from the contract / the pinned manifest and reject any accepted protected row with a specialized
  statement or a protection flag that differs from the binding;
* `verify` recomputes the binding from the pinned manifest and refuses a run whose contract binding is
  missing, tampered or stale, or whose translation did not run under that binding.

Translate-only runs (no contract) carry `protection: null` and cannot be verified.

## Threat boundary

Digests detect change relative to an anchored request within one workspace; they do not
authenticate a workspace where an adversary can replace sources, tools and all recorded digests.
The toolchain fingerprint binds the binaries that were *used*; it does not show that those
binaries were built from the locked sources (the toolchains were installed, not rebuilt).

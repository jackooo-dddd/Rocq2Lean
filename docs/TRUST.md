# Trust boundary

**Claim supported:** "this implementation translated these exported Rocq 9.3.0 declarations
(with their original proof terms) into Lean v4.33.1 declarations that the Lean kernel accepted,
and the accepted terms are structurally the images of the source terms under the documented
rules." It is *not* a verified compiler and passing fixtures prove nothing beyond them.

## What is trusted

| Component | Role | Why it is not simply trusted for fidelity |
|---|---|---|
| Rocq 9.3.0 kernel | produced and checked the source | source of truth |
| MetaRocq Template quoter (`c18395ad`, unpatched) | turns kernel terms into the AST we serialize | Phase 0 probes; M1 round-trip check against the original environment |
| `rocq/exporter` | serializes the AST, no transformation | strict parser; independent decoder/round-trip (M1) |
| `Rocq2Lean/*.lean` translator | builds `Expr`/`Declaration` | output re-checked by the kernel *and* by the independent audit |
| Lean v4.33.1 kernel (`lean_add_decl`) | type checking | the only acceptance authority |
| `tools/audit.py` | independent structural audit | separate implementation and rule table |
| `tools/roundtrip.py` + `rocq/roundtrip/RtEq.v` | independent IR decoder and structural comparison in the original Rocq environment | separate implementation; Gallina comparator compares every field |

## Insertion path

Only `Rocq2Lean.addChecked` adds declarations: `Environment.addDeclCore … (doCheck := true)`.
It refuses to run with `debug.skipKernelTC`. `addDeclWithoutChecking`, `sorryAx`, generated
axioms and `unsafe`/`partial` target declarations are never used. `Lean.addDecl` is not used
(under the module system it may export theorems as axioms). The translator itself uses
ordinary `partial def` recursion; this is implementation code, not translated mathematics.

## Universe solving

References to declarations with generalized universe parameters receive fresh level
metavariables; `solveLevels` runs Lean's `Meta.check` and unifies the value's type with the
declared type to assign them (remaining ones are set to `0`). This only chooses universe
levels — it never changes a term — and its result is re-checked by the kernel. The audit
requires the right *number* of universe arguments but does not compare their values.

## Lowering of `match` and `fix`

The lowered terms are new syntax (recursor applications), so the audit compares them against
the source through explicit rules (`tools/audit.py` docstring): parameters, motive bodies (for
`match`), minor bodies, the major premise and the decreasing/trailing arguments are compared;
motive binder types, the major's indices and the `fix` motive are forced by kernel typing of the
recursor and of the (audited) declared type and are not compared.

## Assumptions

The success profile admits no source axioms and no target axioms; the consumer check reports
the transitive axiom set of every accepted declaration (`collectAxioms`), including Lean's
standard axioms, and fails if it is non-empty.

## Bootstrap

`nat ↦ Nat` and `eq ↦ Eq` are the only untranslated source declarations. They are justified by
exact source signatures, target shape checks and constructor adapter checks (definitional
equality of translated constructor types), re-run every time. No definition or theorem is
ever mapped.

## Source proof usage

The pipeline deliberately translates the original source proof of each root; it does not and
should not satisfy the Prosa correspondence-project rule `source_theorem_dependency = false`.

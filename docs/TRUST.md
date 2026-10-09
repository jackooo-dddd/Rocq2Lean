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

## Insertion path

Only `Rocq2Lean.addChecked` adds declarations: `Environment.addDeclCore … (doCheck := true)`.
It refuses to run with `debug.skipKernelTC`. `addDeclWithoutChecking`, `sorryAx`, generated
axioms and `unsafe`/`partial` target declarations are never used. `Lean.addDecl` is not used
(under the module system it may export theorems as axioms). The translator itself uses
ordinary `partial def` recursion; this is implementation code, not translated mathematics.

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

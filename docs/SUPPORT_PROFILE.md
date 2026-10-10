# Support profile (hardened pilot)

"Candidate supported" (`tools/preflight.py`, `rocq2lean inspect`) means *no known blocker*,
decided from the elaborated terms — not a guarantee of success. Preflight detects statically every
blocker listed under "Rejected explicitly" that is visible in the syntax (including the `match`/
`fix` shape conditions: mutual or non-structural recursion, a changed parameter before the
decreasing argument, a recursive call not on a direct recursive field, `match` on a mutual/nested
inductive or one with functional fields or let-bound constructor arguments, global levels in
inductives, relaxed source checking) and reports, per root, the blocked declaration, the
dependency path to it, the reasons and the node path of each reason; `inspect` exits 2 when any
requested root is blocked. Only conditions that need typing (large elimination of a Prop-only
inductive, kernel universe failures) are detected by the translator alone.

## Supported

| Feature | Rule (implementation) |
|---|---|
| Closed global constants after Section discharge | `transparent` → `def` (regular hints); `opaque_present` → `theorem` if the type is a `Prop`, else `opaque` (kernel-checked value, never unfolded) — `Emit.processConstant` |
| `rel`, `prod`, `lam`, `let`, `app`, `const` | structural; every `let` kept; binders closed by plain de Bruijn abstraction (`bindFVars`), never β-reducing a source redex (M4) — `Translate.trans` |
| `cast` | annotation translated and checked convertible (`isDefEq`), then erased |
| Sorts | `Prop ↦ Sort 0`; `Type@{Set+n} ↦ Sort (n+1)`; `max` componentwise |
| Global monomorphic levels in constants | rules R0–R5 of `docs/UNIVERSE_TRANSLATION.md`: the levels of the constant's *type* become parameters `u_<name>` (R2); levels occurring only in the body are proof-local, solved by Lean's unifier and checked against the native facts (R2B, M4); reference arguments solved by Lean's unifier and checked against the native universe graph (coherence, no raising); a level left unconstrained is defaulted to 0 only with a kernel-checked justification (R3′); typing-determined levels (`Eq`, recursor motives) recomputed independently (R4). A declaration relying on a strict inclusion between its own levels (`Type@{ub} : Type@{uc}`) is rejected by the kernel (documented). |
| Bootstrap inductives | `nat ↦ Nat`, `eq ↦ Eq` (exact source signature, target shape and constructor adapter checks, every run); `eq`'s template universe from its first argument |
| New inductives (M3a) | single-body, monomorphic, non-coinductive, no primitive projections; parameters/indices/constructor order preserved; `Declaration.inductDecl` through `addChecked`; kernel generates constructors and `I.rec`. Nested inductives are accepted by the Lean kernel (but see `match`/`fix`). |
| Inductives with global levels (M4) | source global levels of the block become universe parameters (R2T). **Template inductives** (Corelib `list`, `option`, `prod`, …): every template level must be bound by exactly one parameter of sort `Type@{l}` per the kernel's own `template_universes` record (exported natively, round-trip checked); references instantiate it from the argument (R5); quality-polymorphic parameters (`prod`: "can be instantiated to Prop") are translated at the template defaults' quality Type and a Prop instance is rejected explicitly. **Non-template** inductives with global levels obey R3 at references like constants. Verified: Corelib `list`, `option`, `prod`, `bool` (tests/m4). |
| `match` (M3b) | lowered to the kernel recursor `I.rec`: dependent motive built in the recursor's motive telescope from the source return clause; minors bind exactly the constructor fields (kernel rule `nfields`) and the recursive results (ignored); indices taken from the scrutinee's inferred type |
| `fix` (M3c) | a single structural fixpoint whose body is a `match` on its decreasing argument (`rarg` from the source): `λ P x Q, I.rec params (λ idx x, ∀ G Q, T) minors idx x G Q`; arguments after `x` may change (function-valued motive); index variables of `x` are generalized; **leading arguments that recursive calls change** (`G`, decided from the source syntax; no kept type may depend on them) are generalized too (M4: Corelib `seq`, Stdlib `nth_error`); recursive calls on direct recursive fields become the matching recursive results. A field is recursive only if its type is the inductive at the same parameters (M4: `concat`). |

## Rejected explicitly

| Feature | Status |
|---|---|
| Mutual `fix`; recursion on non-direct subterms; a changed leading argument on which a kept type depends; `fix` whose body is not a match on the decreasing argument (e.g. Corelib `nth`, which matches `n` before the decreasing `l`); functional recursive fields | `UNSUPPORTED_FEATURE` |
| `match`/`fix` on mutual or nested inductives (recursor with several motives) | `UNSUPPORTED_FEATURE` |
| Constructors with `let`-bound arguments in `match` | `UNSUPPORTED_FEATURE` |
| Elimination into `Type` of an inductive that Lean only eliminates into `Prop` | `UNSUPPORTED_FEATURE` |
| Mutual inductive blocks, coinductives, primitive records | `UNSUPPORTED_FEATURE` |
| `cofix`, primitive int/float/string/array, symbols, primitive projections | `UNSUPPORTED_FEATURE` |
| `SProp`, irrelevant binders | `UNSUPPORTED_FEATURE` |
| Universe-polymorphic declarations, universe instances | `UNSUPPORTED_FEATURE` |
| Template inductives whose template levels are not each bound by one parameter of sort `Type@{l}`; a template inductive instantiated at quality Prop | `UNSUPPORTED_FEATURE` |
| Declarations relying on `Set < l` for their own typing (e.g. Corelib `relation`: `A → A → Prop` checked against `Type@{max(l,Set)}` by cumulativity) | `KERNEL_REJECTED` (R2, documented) |
| Section variables, existential variables | `UNSUPPORTED_FEATURE` |
| Genuine source assumptions, unavailable bodies | `BLOCKED_SOURCE_BODY` |
| Constructor roots, duplicate or aliased roots, empty requests | `ROOT_CONTRACT_REJECTED` |
| A reference whose universe argument violates rule R3 | `UNIVERSE_REJECTED` |
| Relaxed source checking (guard/positivity/universes/eliminations off, impredicative Set, UIP) | `AUDIT_REJECTED` |
| Failed dependency | `BLOCKED_DEPENDENCY` (dependency recorded) |

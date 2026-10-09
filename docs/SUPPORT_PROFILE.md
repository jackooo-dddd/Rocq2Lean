# Support profile (hardened pilot)

"Candidate supported" (`tools/preflight.py`) means *no known blocker*, decided from the
elaborated terms — not a guarantee of success. Shape restrictions on `match`/`fix` are only
checked during translation.

## Supported

| Feature | Rule (implementation) |
|---|---|
| Closed global constants after Section discharge | `transparent` → `def` (regular hints); `opaque_present` → `theorem` if the type is a `Prop`, else `opaque` (kernel-checked value, never unfolded) — `Emit.processConstant` |
| `rel`, `prod`, `lam`, `let`, `app`, `const` | structural; every `let` kept (`usedLetOnly := false`) — `Translate.trans` |
| `cast` | annotation translated and checked convertible (`isDefEq`), then erased |
| Sorts | `Prop ↦ Sort 0`; `Type@{Set+n} ↦ Sort (n+1)`; `max` componentwise |
| Global monomorphic levels in constants | rules R0–R4 of `docs/UNIVERSE_TRANSLATION.md`: per-declaration parameters `u_<name>`; reference arguments solved by Lean's unifier and checked against the native universe graph (coherence, no raising); defaults recorded. A declaration relying on a strict inclusion between its own levels (`Type@{ub} : Type@{uc}`) is rejected by the kernel (documented). |
| Bootstrap inductives | `nat ↦ Nat`, `eq ↦ Eq` (exact source signature, target shape and constructor adapter checks, every run); `eq`'s template universe from its first argument |
| New inductives (M3a) | single-body, monomorphic, non-coinductive, no primitive projections; parameters/indices/constructor order preserved; `Declaration.inductDecl` through `addChecked`; kernel generates constructors and `I.rec`. Nested inductives are accepted by the Lean kernel (but see `match`/`fix`). |
| `match` (M3b) | lowered to the kernel recursor `I.rec`: dependent motive built in the recursor's motive telescope from the source return clause; minors bind exactly the constructor fields (kernel rule `nfields`) and the recursive results (ignored); indices taken from the scrutinee's inferred type |
| `fix` (M3c) | a single structural fixpoint whose body is a `match` on its decreasing argument (`rarg` from the source): `λ P x Q, I.rec params (λ idx x, ∀ Q, T) minors idx x Q`; arguments after `x` may change (function-valued motive); index variables of `x` are generalized; recursive calls on direct recursive fields become the matching recursive results |

## Rejected explicitly

| Feature | Status |
|---|---|
| Mutual `fix`; recursion on non-direct subterms; changing a parameter before the decreasing argument; `fix` whose body is not a match on the decreasing argument; functional recursive fields | `UNSUPPORTED_FEATURE` |
| `match`/`fix` on mutual or nested inductives (recursor with several motives) | `UNSUPPORTED_FEATURE` |
| Constructors with `let`-bound arguments in `match` | `UNSUPPORTED_FEATURE` |
| Elimination into `Type` of an inductive that Lean only eliminates into `Prop` | `UNSUPPORTED_FEATURE` |
| Mutual inductive blocks, coinductives, primitive records | `UNSUPPORTED_FEATURE` |
| `cofix`, primitive int/float/string/array, symbols, primitive projections | `UNSUPPORTED_FEATURE` |
| `SProp`, irrelevant binders | `UNSUPPORTED_FEATURE` |
| Universe-polymorphic declarations, universe instances | `UNSUPPORTED_FEATURE` |
| Global levels in inductive declarations | `UNSUPPORTED_FEATURE` |
| Section variables, existential variables | `UNSUPPORTED_FEATURE` |
| Genuine source assumptions, unavailable bodies | `BLOCKED_SOURCE_BODY` |
| Constructor roots, duplicate or aliased roots, empty requests | `ROOT_CONTRACT_REJECTED` |
| A reference whose universe argument violates rule R3 | `UNIVERSE_REJECTED` |
| Relaxed source checking (guard/positivity/universes/eliminations off, impredicative Set, UIP) | `AUDIT_REJECTED` |
| Failed dependency | `BLOCKED_DEPENDENCY` (dependency recorded) |

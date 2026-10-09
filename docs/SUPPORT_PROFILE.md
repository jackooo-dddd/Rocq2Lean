# Support profile (current build)

"Candidate supported" (`tools/preflight.py`) means *no known blocker*, decided from the
elaborated terms — not a guarantee of success.

## Supported

| Feature | Rule |
|---|---|
| Closed global constants after Section discharge, monomorphic | `constant/transparent` → `def` (regular hints); `constant/opaque_present` → `theorem` if the type is a `Prop`, else `opaque` (value kernel-checked, never unfolded) |
| `rel`, `prod`, `lam`, `let`, `app`, `const` | structural; `let` is always kept |
| `cast` | annotation translated and checked convertible in Lean, then erased |
| Sorts | `Prop ↦ Sort 0`; `Type@{Set+n} ↦ Sort (n+1)`; `max` componentwise |
| Bootstrap inductives | `nat ↦ Nat`, `eq ↦ Eq` (see `Rocq2Lean/Bootstrap.lean`): exact source signature, target shape and constructor adapter checks on every run |
| Template universe of `eq` | rule `templateFromArg 0`: `Eq.{u}` with `u` the sort level of the first argument's type (Lean `getLevel`) |

## Rejected explicitly

| Feature | Status |
|---|---|
| `case`, `fix`, `proj` | `UNSUPPORTED_FEATURE` (M3b/M3c) |
| New inductive declarations | `UNSUPPORTED_FEATURE` (M3a) |
| `cofix`, primitive int/float/string/array, symbols | `UNSUPPORTED_FEATURE` |
| `SProp`, irrelevant binders | `UNSUPPORTED_FEATURE` |
| Global monomorphic universe levels, polymorphic universes/instances | `UNSUPPORTED_FEATURE` |
| Section variables (`var`), existential variables (`evar`) | `UNSUPPORTED_FEATURE` |
| Genuine source assumptions, unavailable bodies | `BLOCKED_SOURCE_BODY` |
| Source declared with relaxed checking (guard/positivity/universes/eliminations off, impredicative Set, UIP) | `AUDIT_REJECTED` |
| A dependency that failed | `BLOCKED_DEPENDENCY` (dependency recorded) |

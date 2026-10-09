# Universe translation (supported fragment and checked obligations)

## R0 — Source universe context

* **Levels.** `Set`, global monomorphic levels (named or anonymous; names are Rocq's
  `Univ.Level.to_string`, as quoted by MetaRocq), and — for template inductives — the template
  default levels (`template_defaults`), which is the instance MetaRocq quotes.
* **Relations.** For the levels occurring in the exported declarations (plus `Set`) the exporter
  records, for every ordered pair `(a, b)`, Rocq's *native* relation
  (`UGraph.check_leq` on the loaded environment): `lt` (`a + 1 ≤ b`), `le` (`a ≤ b`), or none.
  This is the IR line `universe_facts` (schema `rocq2lean-ir/0.2`). Orientation: `{"l": a, "rel":
  "lt", "r": b}` means `a < b`. Equality is `le` in both directions.
* **Scope.** The graph is restricted to the levels of the export (the dependency-relevant
  graph). Relations through levels outside the export are *included*, because they are
  computed by closure in the full native graph, not reconstructed from local constraints.
* **MetaRocq's own record** (`universes`: levels and constraints, `le` with offset 0/1 or `eq`)
  is kept in the IR and checked to be entailed by the native facts.
* **Private universes.** Monomorphic opaque proofs in Rocq 9.3 have no private universes
  (`PrivateMonomorphic ()`); their levels are global and covered above. Polymorphic private
  contexts (`PrivatePolymorphic`) belong to universe-polymorphic constants, which are rejected.
  Each constant records `native.private_universes`.
* **Validation (source anchoring).** `tools/roundtrip.py` re-checks every ordered pair in a fresh
  Rocq process with the plugin command `Rocq2Lean CheckRelation` (names resolved through the
  graph's own domain), checks MetaRocq's constraints are entailed, and checks that every level
  named in the exported terms has facts.

## R1 — Sort interpretation

`Prop ↦ Sort 0`; `Type@{Set + n} ↦ Sort (n+1)`; `Type@{l + n} ↦ Sort (u_l + n + 1)` for a global
level `l`; `max` componentwise. `SProp` and universe-polymorphic levels are rejected.
`u_l` is the Lean universe parameter `u_` + `l` with `.` replaced by `_`.

## R2 — Declaration generalization (restriction argument)

A constant whose type or body mentions global levels `l₁ … lₖ` becomes a Lean declaration with
universe parameters `u_{l₁} … u_{lₖ}` (sorted). The Lean kernel checks it for **all** values of
the parameters, which is stronger than the source (checked at fixed levels). The source
declaration is recovered as the instance `u_{lᵢ} := ρ(lᵢ)` for any model `ρ` of the native facts
(for instance the minimal one: `ρ(Set) = 0` and longest strict paths); under that instance R1
maps every source sort exactly to the target sort. Consequently a source declaration that
*relies* on a strict relation between its own levels (e.g. `Type@{ub} : Type@{uc}` with
`ub < uc`) is not expressible generically and is rejected by the kernel — this is reported, not
patched (no lifts, no level axioms). Generated inductives must not mention global levels
(rejected otherwise).

## R3 — Reference instantiation (checked by translator and auditor)

A reference from declaration `d` to a generalized constant `c` carries one target level `σ`
per parameter `u_l` of `c`. Levels are chosen by Lean's unifier (`Meta.check` and unification of
the value's type with the declared type); unconstrained ones are set to `0` and *counted*
(`universe_level_defaults`); solver failures are recorded (`universe_diagnostics`). Whatever
their origin, every `σ` must satisfy:

* **Coherence.** If `l` is also a level of `d`, then `σ ≡ u_l` (after level normalization).
  The same source level is the same target level in both declarations.
* **No raising.** Otherwise write `σ = max(c, u_{m₁} + k₁, …)` (normal form; every `uᵢ` must
  be a parameter of `d`). Require `Set + c ≤ l` and `mᵢ + kᵢ ≤ l` to be **entailed** by the native
  facts (offset 0 needs `≤`, 1 needs `<`, larger offsets need chains of `<`). The target may use
  `c` at a level no higher than the source did; this is exactly the use Rocq's cumulativity
  allows (`A : Type@{m}` passed where `Type@{l}` is expected requires `m ≤ l`).

A violation is `UNIVERSE_REJECTED` in the translator and a `universe` problem in the auditor,
which reimplements the rule (`tools/audit.py: Facts, check_universe_args`). Levels are compared
through the normal form `max(c, uᵢ + kᵢ)` with dominated constants dropped (`max u u ≡ u`,
`max 0 u ≡ u`, `(max u v)+1 ≡ max (u+1) (v+1)`); this is symbolic, not sampled.

## R4 — Template inductive `eq ↦ Eq.{u}`

The argument is the sort level of the first argument's type. In Lean `@Eq.{u} A` is well typed
only when `A : Sort u` exactly (no cumulativity), so `u` is uniquely determined by the kernel-
checked term; the auditor checks there is exactly one universe argument. Recursors of
inductives that eliminate into any sort take the motive's level first; it is likewise
determined by the motive's type.

## Coverage (tests)

`scripts/test-universe-audit`: related levels (`ua ≤ ub`), shared-level coherence, repeated
references, references at `Set`, composition through two generalized constants, a lemma; target
level raised with the same argument count (rejected by kernel and audit), an incoherent
foreign parameter (rejected), equivalent spellings (accepted by both), dropped / invented
source facts (native re-check and auditor), strict inclusion (honest kernel rejection).
`tests/smoke/UniverseRules.lean`: 12 unit checks of R3 in the Lean implementation.

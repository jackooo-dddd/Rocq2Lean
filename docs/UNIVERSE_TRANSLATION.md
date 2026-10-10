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

## R2B — Proof-local levels (M4)

A global level that occurs in a constant's body but **not** in its type is not generalized (clients
never see it): it becomes a level metavariable, solved by Lean's unifier with the rest of the
declaration. Every native fact between such a level and `Set`, a type level or another proof-local
level must hold with each proof-local level read as its solution (summand-wise entailment in the
native graph) — checked by the translator (`checkBodyLevel`, `UNIVERSE_REJECTED`) and independently
by the auditor (`check_body_levels`), which also checks that the reported proof-local set is exactly
the source's. If unconstrained, the solution is the level's **minimal model** (`Set < m` gives 1,
`l ≤ m` gives `u_l`, `l < m` gives `u_l + 1`), recorded with a kernel justification (R3′). Typical
source: the `f_equal` tactic leaves `@eq Type@{m} A A` with `A : Type@{l}` in a proof term, typed in
Rocq by cumulativity (`l ≤ m`); the solution is `σ(m) = u_l`. R3 coherence: an argument for a
proof-local level of the referring declaration must equal its solution.

## R2T — Inductives with global levels (M4)

The global levels of an inductive block (arity and constructor types) become universe parameters
of the generated Lean inductive, in sorted order, and the constructors refer to the inductive at
exactly those parameters. Non-template inductives obey R3 at references (type and constructors).

## R5 — Template inductives (M4)

Rocq 9.3 represents template polymorphism as an abstracted universe context with a default instance
(`template_defaults`, substituted by MetaRocq into the quoted terms) and, per parameter, the sort
binding a template level (`template_param_arguments`). The exporter records this natively
(`native.template_info`), checked by the round trip. Rule: each template level `l` is bound by exactly
one parameter of sort `Type@{l}` (offset 0); every global level of the block is a template level.
At a reference (type, constructor or recursor) the target argument `σ` for `l` is determined by the
argument `A` of that parameter: `A : Sort (σ+1)` — exactly Rocq's template instantiation (the level
is substituted by the argument's level, without R3's no-raising condition). The kernel forces it;
the auditor recomputes it (`InstanceLevels`, from the *source* template record, deferred count
reported) and the consumer checks every occurrence (`instance_levels`). Parameters that also bind a
sort quality (`prod`: "can be instantiated to Prop") are translated at the template defaults'
quality Type; an argument that is a proposition is rejected explicitly (`UNSUPPORTED_FEATURE`).

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

## R3′ — Defaulted (residual) levels

A level metavariable that Lean's unifier leaves unassigned is not determined by typing. It is set
to `0` only with a **justification**: the translator re-submits the declaration with every such
level as a fresh universe parameter `u_residual_i` to the kernel (`justifyResiduals`, without
installing it); acceptance means the declaration is well typed for *every* value of those levels,
so the default chooses nothing. Otherwise the declaration is `UNIVERSE_REJECTED`. The report
records the generic declaration (`universe_residuals`); the auditor checks that it instantiates at
`0` to exactly the reported declaration, and the consumer re-checks it in the kernel in a fresh
process (`residual_levels`). The defaulted arguments must in addition satisfy R3 like any other.
Fixture: `fixtures/universes/UnivResidual.v`.

## R4 — Template inductive `eq ↦ Eq.{u}`

The argument is the sort level of the first argument's type. In Lean `@Eq.{u} A` is well typed
only when `A : Sort u` exactly (no cumulativity), so `u` is uniquely determined by the kernel-
checked term. Recursors of inductives that eliminate into any sort take the motive's level
first; it is likewise determined by the motive's type. These levels are **checked, not only
counted**: the auditor recomputes them from the audited target terms (`InstanceLevels`: the sort
of `A`'s type for `Eq`/`Eq.refl`/`Eq.rec`, the sort of the motive's codomain for large
recursors), using the report's audited types and an independent copy of the bootstrap types;
occurrences its small inference cannot determine are counted as deferred. The consumer checks
every occurrence with Lean's inference in a fresh process (`instance_levels`).

## Coverage (tests, additions of the second hardening pass)

`scripts/test-universe-audit` also covers: a justified residual level (positive control); a forged
justification that is not valid for every level (consumer kernel re-check rejects; the auditor's
syntactic check alone would accept it), a removed justification record and one that does not
instantiate to the accepted declaration (consumer and auditor); a raised `Eq` level and a raised
recursor motive level (kernel and auditor `instance_levels`); an invented MetaRocq constraint (native
round trip: not entailed). `tests/smoke/UniverseRules.lean` adds unit checks of `justifyResiduals`.

## Coverage (tests)

`scripts/test-universe-audit`: related levels (`ua ≤ ub`), shared-level coherence, repeated
references, references at `Set`, composition through two generalized constants, a lemma; target
level raised with the same argument count (rejected by kernel and audit), an incoherent
foreign parameter (rejected), equivalent spellings (accepted by both), dropped / invented
source facts (native re-check and auditor), strict inclusion (honest kernel rejection).
`tests/smoke/UniverseRules.lean`: 12 unit checks of R3 in the Lean implementation.

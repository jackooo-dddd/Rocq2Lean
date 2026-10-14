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
  contexts (`PrivatePolymorphic`) belong to universe-polymorphic constants (R6, M6).
  Each constant records `native.private_universes`.
* **Validation (source anchoring).** `tools/roundtrip.py` re-checks every ordered pair in a fresh
  Rocq process with the plugin command `Rocq2Lean CheckRelation` (names resolved through the
  graph's own domain), checks MetaRocq's constraints are entailed, and checks that every level
  named in the exported terms has facts.

## R1 — Sort interpretation

`Prop ↦ Sort 0`; `Type@{Set + n} ↦ Sort (n+1)`; `Type@{l + n} ↦ Sort (u_l + n + 1)` for a global
level `l`; `max` componentwise. `SProp` is rejected; universe variables of polymorphic constants follow R6.
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

## M6 extensions (MathComp/Prosa closures)

Each rule is applied by the translator and checked independently by the auditor
(`tools/audit.py`). A declaration accepted under the earlier rules is never translated
differently: R2⁺ and R2F-c are retries after a rejection.

**R6. Universe-polymorphic constants.**
- *Parameters.* The `k` universe variables of a polymorphic constant become its first Lean
  universe parameters `v_0 … v_{k-1}`, and `Type@{var i + n} ↦ Sort (v_i + n + 1)`.
- *References.* A reference carries the source instance level by level: `Set ↦ 0`,
  `var i ↦ v_i`, and a global level ↦ the referring declaration's own level for it. These
  arguments are not R3 obligations; the auditor checks that they are exactly the image of the
  source instance.
- *Constraints.* Rocq's constraints among the variables are not transported. The kernel checks
  the body for every value of the parameters. This can reject a body that needs a constraint
  (fixture `plift`, which needs `u < v` with cumulativity); it never accepts an ill-typed one.
- *Not covered.* Universe-polymorphic inductives remain unsupported.
- *Report and fixture.* `universe_poly_params`; fixture `fixtures/poly`.

**R2⁺. Fact reduction (retry).** A summand `Set + k` of an algebraic universe is dropped when
another summand `l + j` is at least as large under the native facts: `k ≤ j`, or
`Set + (k − j) ≤ l` entailed.
- *Why the universes are equal.* In Rocq both universes are the same. Lean types `Prop` at
  `Sort 1`, while Rocq types it at `Type@{Set+1}`.
- *Example.* `relation : Type@{l} → Type@{max(Set+1, l)}` with `Set < l` becomes
  `Sort (u+1) → Sort (u+1)`, which `A → A → Prop` meets, and `relation Prop` /
  `relation nat` remain instantiable at `u := 0`.
- *Report.* `sort_fact_reduced`; the auditor recomputes the reduction from the facts.

**R3G. Implicit levels.** A universe argument still free in the declaration's type, at a
reference to a declaration whose parameter stands for source level `l`, is `l` itself (Rocq
references monomorphic declarations at their own levels).
- *Effect.* It becomes the parameter `u_l` instead of being fixed at a default. Previously such a
  level was kept only when the generic declaration was valid for every value; now the kernel
  checks it generically.
- *Example.* MathComp's `finite_axiom` mentions `Equality.type@{51,58}` only through the
  reference; with 51 and 58 fixed at 0 it could not be applied to `T : Type@{24}` in `isFinite`.
- *Choice within a class.* When unification identified several references in one metavariable,
  `l` is chosen below every other level of the class (`l ≤ l'` entailed), so R3 holds for all
  of them. Every argument for `l` (type and body) must still be free and becomes `u_l`
  (coherence).
- *Report and audit.* `implicit_levels`. The auditor checks that each implicit level is absent
  from the source sorts and occurs as the argument of a reference for that level.
- *P0: template levels in the class.* A template level in the class (a template inductive's level
  parameter, R5) imposes nothing: Rocq instantiates a template parameter afresh at each use, so no
  fact `l ≤ l'` is required for it, exactly as `checkUniverseObligations` exempts template levels from
  R3. Requiring one made the choice depend on whatever global constraints the request's loaded
  libraries happened to add (e.g. `eqtype.51 ≤ Datatypes.190` from an unrelated library), so
  `fintype.finite_axiom` lost a parameter in small requests and `fintype/isFinite.axioms_` was then
  kernel-rejected (`reports/prosa_inventory/P0_REPORT.md`).
- *P0: indexed facts.* `UniverseFacts.rel` and `entails` use a map and a strict-successor table
  built once per export, so a query no longer scans the request-sized relation table and a
  declaration's cost does not grow with the size of the request.

**R2F-c. Fact interpretation of a constant's own levels (retry).**
- *Own levels.* The explicit type levels, plus the implicit levels of free metavariables of the
  type or the body, are read as in R2F: `ι l = max (u_l, ι m + k …)` over the native facts
  `m (+1) ≤ l` among them. Every own fact then holds for every value of the parameters, and at
  `u := ρ`, for any model `ρ` of the facts, `ι` is `ρ`. R2's restriction argument is unchanged.
- *Coherence.* An argument for an own level must be `ι l`.
- *Example.* `prosa.behavior.job.JobType := eqType` is `Equality.type@{51,58}` at
  `Type@{58}`, with `51 < 58`. With `ι 58 = max (u58, u51+1)`, its sort is the declared one for
  every value, with no defaulted level.
- *Report and audit.* `level_interp`; the auditor recomputes `ι` (`own_level_interp`).
- *Fix to inductives.* The same coherence obligation now applies to R2F inductives. Previously
  the translator checked their shared levels against `u_l` while referring through `ι l`, a
  latent inconsistency.

**Cumulativity tier (R3↑, R2B-P, R2B-S, R3↓).** Lean has no cumulativity; Rocq's typing uses it in
four recurring ways. Each is a separately scoped rule with its own obligation, applied only to a
declaration that every strict tier rejected, and reported per row.
- *When it applies.* Only to a declaration that every strict tier rejected (R2, R2⁺, R2F-c).
  Such a row is reported as `universe_cumulativity: true`. For every other declaration R3 and R2B
  are unchanged: the unit checks in `tests/smoke/UniverseRules.lean` still reject `u_b` for `a` when
  only `a ≤ b` holds.
- *R3↑ (upward lifting) — correspondence rule.* In R3, a summand that is the referring declaration's
  own level `m`, with effective offset 0, may stand for the referenced level `l` when `l ≤ m` is
  entailed by the native facts. Rocq typed the reference `c@{l}` and used its value at `m` by upward
  cumulativity (subtyping, no term change); Lean instantiates the same definition at `m`. Obligations
  (translator and auditor, independently): the summand is an own level with offset 0, `l ≤ m` is
  entailed, nothing else in the argument raises; the kernel checks `c` for every value of its
  parameters, and the referring declaration in full. Positive: MathComp
  `Monoid.isLaw/isComLaw.phant_axioms` (no other relaxation); negative: a forged unrelated argument
  is audit-rejected (`test-m6`).
- *R2B-P (`Set < m` read as `Set ≤ m`) — source obligation.* Lean types `Prop` at `Sort 1`, the image
  of `Set`, so a solved level `m` may need the native fact `Set < m` read as `Set ≤ m`. The rule is
  restricted to what can be validated: for every such level (reported in `r2bp_levels`), `verify`
  maps the solution back to a Rocq level (`0 ↦ Set`, `u_l ↦ l`) and has Rocq's kernel re-check the
  source declaration at that instance (`Rocq2Lean CheckInstance`, a fresh `rocq compile`; type,
  body, and body type ≤ declared type). Any failure rejects the run. Positive: `uses_n` (the fact is
  imposed by another declaration). Negative: `prop_in_m` (its own typing needs `Set < m`).
- *Statement specializations.* When such a level occurs in the declaration's *type* (`in_type`), the
  Lean statement is the source statement at the checked instance — a specialization. Example: the
  `Corelib.Classes.Morphisms` obligations `∀ A : Type@{77}, … respectful A Prop …`, where
  `respectful`'s single level must hold both `A` and `Prop` (Rocq: `77 ≤ 21`, `Set < 21` by
  cumulativity; Lean: one level, which `Prop` forces to 0). Allowed for dependencies only, each with
  Rocq's INSTANCE_OK; `verify` refuses a requested root whose statement would be specialized, so
  root statements are never weakened. The auditor requires every relaxed level of the type to be
  reported as `in_type`.
- *R2B-S (result-sort lowering).* A level that occurs in the source type only as the declaration's
  own result sort (`c : ∀ xs, Type@{…l…}`, `l` in no binder type) — a type definition — is set to its
  value's level, reading `Set < l` (from `l`'s global declaration) as `Set ≤ l`: the type it defines
  does not depend on its sort level, and every use is kernel-checked at that level. No instance check
  (the dependencies keep `l`): Stdlib `ZMicromega.ZWitness := Psatz Z`. Positive `up_nat`; negative
  `up_binder` (the level also in a binder type: not R2B-S, and its instance fails). Applicability is
  re-derived by the auditor from the source type (`only_in_result_sort`).
- *Rule R (coherence modulo an R2F reading; docs/COHERENCE_READINGS.md).* An argument
  `max (u_l, s₁, …)` for a shared level `l`, every other summand passing R3, equals `l` at every model
  of the source facts and satisfies coherence (not for motive-level or proof-local levels). Translator
  `checkInstantiation`, audit `check_universe_args`; controls in `scripts/test-coherence`.
- *R3↓ (downward instantiation).* A reference whose argument lives below a level shared with the
  referring declaration (`PolC@{l} Z` with `Z : Set ≤ Type@{l}`; `Box@{l} nat` in a field of an
  inductive at `l`) takes a fresh level, solved by Lean's unifier at the argument's level; the
  argument must not raise (`Set + c ≤ l`, `m + k ≤ l` entailed), exactly as for a level of another
  declaration. Last tiers for constants, a third attempt for inductives; reported
  (`universe_lowered`). Positive: `proof` in `fixtures/cumul`, Stdlib `ZMicromega.ZArithProof`;
  negative: a forged unrelated argument is audit-rejected.
- *Bounded solver for postponed `max` constraints* (the R3↓ tiers only). Lean leaves
  `max(As) = max(Bs)` with a free metavariable unsolved. After removing the common offset, a bare
  metavariable `?v` of one side that does not occur on the other gets the candidates `max(Bs ∖ As)`,
  `0`, then each summand of `Bs`; a candidate is kept only when Lean's level unification accepts the
  constraint with nothing postponed. Assignments are recorded in `universe_diagnostics`
  (`solver: ?v := …`); a constraint left is classified as *unsatisfiable* (a parameter summand of one
  side is covered by no summand of the other) or *solver limitation*. Every solution is then subject
  to the R3 obligations and the kernel. Positive: Stdlib `Ring_theory.IDmorph`.
- *Plain levels of inductives.* A non-template inductive is first translated with independent
  universe parameters (`plain_levels`), then, if the kernel rejects that, with the R2F fact
  interpretation. The interpretation bakes in facts between the block's levels that only uses
  elsewhere impose (Stdlib `Ring_theory.ring_morph`: `C ≥ R` from `IDmorph`'s `C := R`), which made
  `RingMicromega.SORaddon` (independent `R`, `C`) unsatisfiable; the plain form is strictly more
  general. The auditor reads a plain row's sorts and coherence without the interpretation.
- *What stays rejected.* A raised offset, unrelated levels, a root whose statement would be
  specialized, a relaxed level whose Rocq instance is rejected; the kernel checks every declaration in
  full.

**R8. Motive levels admit `Prop`.**
- *Which levels.* A level that occurs in a constant's type only as the codomain sort `Type@{l}`
  (one summand, offset 0) of a binder type with at least one argument, as in
  `K : R1 → R2 → Type@{l}`.
- *Translation.* Such a level is a sort level: `Type@{l + n} ↦ Sort (u_l + n)`, admitting `Prop`.
  Rocq instantiates such motives with `Prop`-valued families by cumulativity (MathComp `eq_bigr`
  calls `big_rec2` with `fun a b => b = a`).
- *Order.* It is tried first. It is strictly more general (`u := v+1` gives the R2 form), and it
  is kept only if the kernel accepts the body for every value, including `u = 0`.
- *R3 offsets.* A motive-level parameter is one above the image of its source level, so R3 uses
  an effective offset `k + [own motive level] − [referenced motive level]`, and the argument `0`
  (`Prop`) is always admissible for it.
- *Report and audit.* `admitting_levels`; the auditor recomputes the motive levels from the
  source type.

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

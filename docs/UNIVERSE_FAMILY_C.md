# Task C: the `Equality.type` / `JobType` universe family

Scope (plan, 2026-10-13): the protected Prosa declarations blocked by universe rejections at
references to MathComp's `Equality.type` through Prosa's `JobType`/`TaskType`: `JLFP_policy`,
`FP_policy`, `JLDP_policy` (604 protected declarations blocked, 373 only by them, all modern), the
ideal `processor_state` obligations (280, 184 only), Classic `jlfp_instantiation`-style definitions.
Constraint: a rule with its own independent copy in the auditor, and **no narrowing of protected
declarations**.

## 1. The two mechanisms (diagnosis, measured on `runs/st-corpus-A` and the probe `fixtures/stmt/c`)

### 1a. `processor_state`: a statement specialized by defaulting its implicit levels (fixed for `opt_eqP` by C-1; `processor_state` itself stays refused, §2)

`ProcessorState`-based definitions need `option_eqType Job` (MathComp's canonical `eqType` on
`option`) for `Job : JobType`. In the translation:

    opt_eqP.type                       : ∀ T : Equality.type.{0,0}, eq_axiom.{0} (option.{0} (sort T)) …
    HB_unnamed_factory_40.{v}          : ∀ T : Equality.type.{0,0}, …
    Datatypes_option__canonical__eqtype_Equality.{v} : Equality.type.{0,0} → Equality.type.{0,v}

while Prosa's `Job : JobType.{u₅₁,u₅₈}` is generic, so the kernel rejects `option_eqType Job`
(`processor_state__rocq2lean_obligation_{1,2}`: "argument has type JobType but function has type
Equality.type → Equality.type"; residual levels not justified).

Cause: the opaque-data interface `opt_eqP.type` (a *statement* row: its declared type is a sort, its
statement is its value) was translated with **no universe parameters**: its two levels (MathComp
`eqtype.51`/`eqtype.58`, reached only through references — the statement mentions no sort) were
**defaulted to 0** (`universe_level_defaults: 2`). R3G — which turns such implicit reference levels
into parameters named after the referenced source level — read only the declared *type* of the row
(`Prop` / a sort for a statement row) and never saw them. This contradicts the design rule that a
statement is never specialized by defaulting a level (`STATEMENT_ONLY_DESIGN.md` §6), and the
specialization propagated to every MathComp declaration built from `opt_eqP` (`option`'s canonical
`eqType` only accepts `Set`-level carriers), so Prosa's generic jobs cannot use them.

Rule C-1 (R3G for statements): for a statement row, implicit reference levels are read in the
statement (the row's value). The audit's existing independent R3G check applies unchanged: every
reported implicit level must be the argument of a reference for that source level, and R3 holds for
every argument (`tools/audit.py`, `own_partition_full`, `check_universe_args`). No narrowing: the
change makes statements *more* general (parameters instead of 0).

### 1b. `JLFP_policy`/`FP_policy`/`JLDP_policy`: Lean has no cumulativity (policy blocker)

    Definition JLFP_policy (Job : JobType) := rel Job.     (* Prosa *)

Source levels: `JobType := Equality.type@{51,58}` (`51 < 58`), `Equality.sort Job : Type@{51}`,
`rel@{ssrbool.1105} : Type@{1105} → Type@{1105}`, native facts `51 ≤ 1105`, `1105 ≤ 58` (and **not**
`1105 < 58`, re-checked natively in the common environment of all 432 modules: `le`). Rocq types
`rel (sort Job)` by **cumulativity** `Type@{51} ≤ Type@{1105}`, and JLFP_policy's type is
`JobType → Type@{max(Set, 1105, 1171)}` — its result sort is `rel`'s level, not the job's.

Lean has no cumulativity: `rel.{w} (sort Job)` forces `w = (level of sort Job)`. Under the current
representation and rules, every translation does one of:

1. **lift the job** (`JobType` at `51 ↦ 1105`, rule R3↑): `JobType`'s level `58` is read as
   `max(51+1, 58)` (R2F, from `51 < 58`), so the lifted instance needs `1105 + 1 ≤ 58`, which the
   source graph does not entail (`1105 = 58` is consistent): **raising** — refused by R3, correctly;
2. **lower `rel`** to the job's level (`rel.{u₅₁}`, R3 allows it: `51 ≤ 1105`): then JLFP_policy's own
   result sort `Type@{1105}` must be solved to `Type@{51}` — **R2B-S on a protected declaration's
   statement** (result-sort lowering), refused by the interface protection (P0, Q5: no unapproved
   narrowing).

So the policy family is **unsupported by the current representation and rules**; it is not shown
that no Lean translation exists (an explicit lifting, e.g. `ULift` of the carrier, or a different
encoding of the result sort, would be a representation change, not covered by the current rules). It
stays blocked under the current contract (decision 2026-10-14).

Requirements for any future result-sort normalization or explicit lifting (none is applied): a
**general** representation rule (stated for every declaration it covers, not a name-specific
exception for these three definitions); a source/target interface analysis (which statements and
uses change, what the Lean declaration's type promises compared with the source's); an independent
validation (an audit copy of the rule and negative controls); and downstream-use tests (dependents
of the changed declarations kernel-checked and audited, including uses at nonzero universes).

## 2. The C-1 repair: no specialization at a level the source leaves free (2026-10-14)

C-1 (§1a) made R3G read a statement row's statement. Measuring it showed that the defect class is
wider than the self-reported defaults: a level can also be **fixed without being defaulted**, by
unification with an already specialized declaration (a hypothesis typed by the specialized
`opt_eqP.type.{}` pins `Job : Equality.type.{0,0}` in a definition) or, for a definition, by its
value (no cumulativity). The audit had accepted these: R3 forbids raising, and a closed level below
the source level is not raising.

Rule (translator, `Rocq2Lean/Emit.lean` `freeLevelPin`; independent copy in `tools/audit.py`
`check_statement_generality`): for a reference `c.{σ…} a₁ … aₙ` and a source level `l` of `c` that is
not a level of the declaration, `l` is **free** when the native graph does not force `l ≤ Set` and
no applied argument determines it (`c`'s parameter for `l` occurs in no applied binder's domain;
a pending artifact's hypothesis binders do not count, their levels being the translator's choice;
type arguments fixed by sibling arguments, `@Eq A a b`, are not inspected). A free level whose
argument is not its own parameter specializes the declaration. Refused / rejected:

* in **every statement** (proof task, opaque-data interface), anywhere in it (hypothesis telescope
  peeled);
* in the **binder domains** (quantification ranges) of **protected** definitions and inductives
  (P0: no narrowing of the protected interface);
* reported as a diagnostic, not a rejection, for non-protected definitions (their value may fix the
  level: `nat`'s canonical `countType` is at level 0 in Lean; library definitions may be instantiated
  below the source, as R3↓; their effect on protected declarations is checked there).

The audit uses only the source, the native facts and the target terms — no self-reported
`universe_level_defaults` or residual record.

Correction: the ideal `processor_state` is **refused**, not fixed. With `opt_eqP` generic, its
translation still has `Job : JobType.{0,_}`: `ProcessorState`'s core-finType level is read as
`max(u₁₀₁, u₅₁)` (R2F, `51 ≤ 101`), and the ideal model's core is `unit`'s finType at level 0, which
forces Job to level 0 — a narrowing of a protected definition. (The earlier statement that C-1
"unblocks the ideal processor_state family with generic jobs" was wrong: its rows were claimed with
`Job` at level 0, which neither check caught then.) Its two obligations and the generic MathComp
prerequisites (`opt_eqP`, `option`'s eqType) do translate.

Tests (`scripts/test-universe-c`): narrowed targets with every self-reported trace removed — `opt_eqP`
at `Equality.type.{0,0}`, `.{0,1}` (a nonzero closed level R3 admits: only the generality obligation
rejects it) and `.{2,2}` (raising: R3 rejects it), and the protected `job_cost` at its `Job` binder —
are kernel-accepted and audit-rejected; a positive control instantiates the generic translations at
universes 2..5 through the kernel (and uses the statement at an `Equality.type.{3,4}`) and fails
against the narrowed module.

## 3. Status

* C-1 and its repair: measured on the corpus, `reports/statement_only/ITERATION_LOG.md` (entry 4).
* 1b (`JLFP`/`FP`/`JLDP_policy`): handled by the approved rule R2B-V (§4, 2026-10-14); entry 6.

## 4. Rule R2B-V: a type-valued definition declared at the sort of its value (approved 2026-10-14)

**Rule.** For a *definition* (never a statement, proof task or opaque-data interface) whose source type
is `∀ Γ, Sort s`, the levels that occur in the source only in the result sort `s` may be replaced by the
sort of the translated value: the Lean declaration is `∀ ⟦Γ⟧, Sort σ` with `σ` the sort of
`⟦body⟧ Γ` (`fun Γ ↦ ⟦body⟧`), each replaced level `l` solved to a level `σ_l` that is a **lowering**:
every summand `g + k` of `σ_l` has `g + k ≤ l` in the native facts (`g` a parameter's source level),
every constant `k` has `Set + k ≤ l`. A replaced level that no longer occurs anywhere is recorded at 0
(a lowering). It is a general rule — stated for every declaration it covers — tried as the last tier of
the translation ladder (only when every other tier fails, so no accepted translation changes), in
statement mode only. Reported per row: `result_sort_inherited: true`, `sort_lowered_levels`.

**Why it is needed.** Rocq types `rel (sort Job)` at `rel`'s level by cumulativity
(`Type@{51} ≤ Type@{1105}`), so `JLFP_policy : JobType → Type@{1105}`; Lean has no cumulativity, so
the declaration either raises the job to `rel`'s level (R3 refuses) or is declared at the job's level.

**Source/target interface analysis.**
* Unchanged: every binder (quantification range) — the C generality check still applies to the
  protected definition's binder domains (`Job : JobType.{u51, ι58}` stays generic); the value (term by
  term, audited); every reference (R3 on each argument; `rel` lowered to the job's level, R3↓).
* Changed: only the declared result sort: `JLFP_policy.{u51,u58} Job : Type u51` instead of
  Rocq's `Type@{1105}` (with `51 ≤ 1105` native). The Lean type is exactly the type of the value; Rocq's
  declared sort was an upper bound reached by cumulativity.
* Consequence for uses: a use of the definition that needs it *at* the larger universe (the defined type
  placed where a type of a strictly larger fixed universe is required) cannot be expressed without
  cumulativity; in Lean such a use fails the kernel check of the *use* (reported, never silently
  accepted). Every use the corpus contains is measured (entry 6).

**Independent validation.**
* Audit (`tools/audit.py`): the flag only on a definition whose source type ends in a sort; every
  replaced level occurs in the source result sort and only there; each solution a lowering; R2B-V on a
  statement rejected; the replaced levels are exempt from the solution-fact check (they have no
  counterpart), all other universe checks unchanged; the protection check accepts a protected
  result-sort lowering only with the flag.
* Consumer (`Rocq2Lean/Verify.lean`, in Lean): for a protected row with the flag, the imported
  declaration's result sort equals the sort its value inhabits, and it is not a statement.
* CLI validation: a protected result-sort lowering without the flag is refused.
* Negative controls (`scripts/test-universe-c`, report-level forgeries, kernel-accepted): a non-lowering
  solution, a level that is not a result-sort level, the flag on a statement, the protected lowering
  without the rule — each rejected.

**Downstream-use tests.** Probe (`fixtures/stmt/c`): `JLFP`/`FP`/`JLDP_policy` translated under the
rule, the job generic; `hep_job`, `JLFP_to_JLDP`, `EDF`, `FIFO`, two statements about priorities
translated and audited; positive control: the policies, `EDF` and `hep_job` kernel-checked at nonzero
universes. Corpus: entry 6.

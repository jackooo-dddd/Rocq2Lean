# Task C: the `Equality.type` / `JobType` universe family

Scope (plan, 2026-10-13): the protected Prosa declarations blocked by universe rejections at
references to MathComp's `Equality.type` through Prosa's `JobType`/`TaskType`: `JLFP_policy`,
`FP_policy`, `JLDP_policy` (604 protected declarations blocked, 373 only by them, all modern), the
ideal `processor_state` obligations (280, 184 only), Classic `jlfp_instantiation`-style definitions.
Constraint: a rule with its own independent copy in the auditor, and **no narrowing of protected
declarations**.

## 1. The two mechanisms (diagnosis, measured on `runs/st-corpus-A` and the probe `fixtures/stmt/c`)

### 1a. `processor_state`: a statement specialized by defaulting its implicit levels (fixed, C-1)

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

Lean has no cumulativity: `rel.{w} (sort Job)` forces `w = (level of sort Job)`. Every translation
therefore does one of:

1. **lift the job** (`JobType` at `51 ↦ 1105`, rule R3↑): `JobType`'s level `58` is read as
   `max(51+1, 58)` (R2F, from `51 < 58`), so the lifted instance needs `1105 + 1 ≤ 58`, which the
   source graph does not entail (`1105 = 58` is consistent): **raising** — refused by R3, correctly;
2. **lower `rel`** to the job's level (`rel.{u₅₁}`, R3 allows it: `51 ≤ 1105`): then JLFP_policy's own
   result sort `Type@{1105}` must be solved to `Type@{51}` — **R2B-S on a protected declaration's
   statement** (result-sort lowering), refused by the interface protection (P0, Q5: no unapproved
   narrowing).

No third translation exists without a representation change (`ULift` around the carrier would change
the type `rel` is applied to). So the policy family is **not** a missing translator capability: it
is the protection policy refusing the only Lean representation. It needs a decision (an approved,
documented representation change for "result sort inherited from a referenced definition at a level
above the value's"), not more engineering.

## 2. Status

* C-1 implemented and measured: see `reports/statement_only/ITERATION_LOG.md` (entry C).
* 1b: blocker documented; not applied (no approved representation change). Proposed rule, for the
  user's decision: *R2B-S-inherited* — a protected type-valued definition whose source result sort is
  only the result sort of the referenced definition it unfolds to (`JLFP_policy := rel _`, the level
  `1105` belongs to `rel`, not to Prosa) may take its value's sort; validated by the existing R2B-S
  applicability check (`only_in_result_sort`) plus a check that every such level is a level of the
  head constant of the body; reported per row; never on theorem statements.

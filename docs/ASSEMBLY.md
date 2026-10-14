# Pending-to-final assembly (statement mode)

Status: implemented 2026-10-13 (Task A). Design context: `docs/STATEMENT_ONLY_DESIGN.md` (§6, §9).
Tests: `scripts/test-assembly` (`tests/statement/check_assembly.py`, synthetic fixture
`fixtures/stmt/asm/Asm.v`).

A validated statement library contains *accepted* declarations (`Rocq.*`) and *pending artifacts*
(`RocqPending.*`): definitions, inductives and statements kernel-checked with their unproved
prerequisites (proof tasks) as hypotheses. Assembly turns pending artifacts into accepted
declarations once the proofs they need exist, and gives every proved task its final theorem. It never
writes, rewrites or casts a proof.

## Names and modules

| What | Name | Module |
|---|---|---|
| validated statement library (accepted and pending) | `Rocq.*`, `RocqPending.*` | `Rocq2LeanOut` (unchanged after validation) |
| a submitted proof of a task (*template*) | `RocqProofTemplates.T<task_id>.proof` | `RocqProofTemplates.T<task_id>` |
| a final declaration | `Rocq.<source name>` (theorems: `Rocq.<leaf>`) | `Rocq2LeanAssembled` |

Module graph (acyclic): `Rocq2LeanOut` ← templates ← `Rocq2LeanAssembled`. A template module may
declare nothing outside its own namespace `RocqProofTemplates.T<task_id>` (checked), so it never adds
to `Rocq.*` or `RocqPending.*`, and `Rocq.<name>` stays reserved for assembly. Assembly never
overwrites a module that submissions import and never redeclares their constants: the templates are
recompiled from their bound sources into the assembly's own directory, and the validated library is
imported, not rebuilt.

## Task statements and their generalization

A task with prerequisites `h₁ … hₖ` (its statement is pending) asks for
`∀ h₁ … hₖ, @RocqPending.c.statement h₁ … hₖ` (the hypotheses are implicit binders of the pending
statement). The generalization is recorded per task (`prerequisites.generalization.form`):

* `none` — no prerequisite: the task statement is the final statement;
* `over_proof_prerequisites` — every prerequisite is a proposition: any two proofs of a proposition are
  definitionally equal in Lean, so the generalized statement implies the final one. Assembly still
  only uses it where the kernel accepts the instantiation (below);
* `over_data_prerequisites` — some prerequisite is opaque data. The generalized statement can be
  strictly *stronger* than the source statement (it quantifies over every value of the data's type,
  where the source fixes one), so its provability is not claimed. Such a task can still be checked,
  but it is not assembled until the data is bound (A′).

The earlier claim that "every task can be proved independently" is withdrawn: it holds for
propositional prerequisites, and is not justified in general for data prerequisites.

## Opaque data

An opaque `Set`/`Type` constant (`Qed` with a non-propositional type) is not a proof: its *value* can
matter (e.g. a `hasChoice` structure decides what `choose` returns), and its type need not have a
unique inhabitant. Assembly therefore never accepts a submitted value for it:

* `check-proof` refuses opaque-value submissions (`accepts_submissions: false` in the task record);
* rows that need an opaque value stay pending, with assembly state `OPAQUE_BINDING_PENDING`.

A′ (`docs/OPAQUE_DATA.md`) translates the data-producing bodies of these constants mechanically (Lean
`opaque` constants, their genuine proof subterms extracted as obligations), so each value is bound once,
from the source. The policy above now applies only to opaque data whose body could not be prepared
(kept as an interface, with the reason: e.g. a body recursing on a proof).

## Algorithm (`rocq2lean assemble --run RUN [--complete]`)

Inputs: the run's current `STATEMENT_VALIDATED` validation, its `PROOF_TASKS.jsonl`, and every
submission whose recorded check is `LEAN_PROOF_KERNEL_VERIFIED`.

1. **Claimed submissions are verified, not trusted.** A claimed submission whose source is missing or
   altered after its check, that was checked against another validation or another task statement, or
   whose task accepts no submission, makes the assembly fail (`PROOF_REJECTED`). Every template is then
   recompiled from its bound source and re-checked in a fresh process. *A task with no claimed
   submission is not an error*: it is simply not supplied, and its dependents stay pending.
2. **Translation in assembly mode** (`#rocq2lean_assemble`, `translateSource … (asm? := …)`), in
   dependency order, in a module importing the validated library and the templates:
   * a row the validated library accepted is translated again and must be **identical** to the
     imported declaration (`addOrReuse`: same kind, universe parameters, type, value or
     constructors); it is not added again. A difference fails the assembly (`REUSE_MISMATCH`);
   * a proof task whose statement is accepted and whose template was supplied gets the theorem
     `Rocq.<leaf> : Rocq.<leaf>.statement := T Rocq.<p₁> … Rocq.<pₖ>` (the template applied to its
     prerequisites' final theorems) — **only if the kernel accepts exactly that** at the final,
     audited statement. Otherwise the task's proof state is `ASSEMBLY_TRANSPORT_REQUIRED`: no final
     theorem, nothing cast, the submitted proof untouched;
   * a pending row whose prerequisites all have final theorems and whose dependencies are all
     available is translated again without hypotheses, as `Rocq.<name>` (`ASSEMBLED`);
   * every other row is carried over unchanged (`PENDING`, `OPAQUE_BINDING_PENDING`,
     `ASSEMBLY_BLOCKED`, `ASSEMBLY_REJECTED`, `NOT_TRANSLATED`); its pending artifact stays in
     `Rocq2LeanOut`.

   The assembled set is the largest one these rules allow: kernel convertibility (the instantiation),
   datatype identity (below), interface protection (the same contract binding as the translation) and
   dependency readiness.
3. **Fresh-process consumer** (`#rocq2lean_verify … proofs.json`) and **independent audit**
   (`audit.py … --assembly proofs.json --validated report`), with distinct policies per category:
   * validated rows: the statement library as validated (axiom-free, identical to the validated rows);
   * assembled rows: accepted `Rocq.*` declarations, audited against the source with every reference
     to a proved task being its final theorem; they never reference a pending artifact or a template;
   * final theorems: type exactly the accepted statement at its universe parameters; value exactly the
     manifest's template applied to the prerequisites' final theorems (the prerequisites recomputed
     from the validated library);
   * carried-over pending artifacts: identical to the validated rows, audited as pending artifacts;
   * maximality: a carried-over row whose prerequisites all have final theorems must say why it was
     not assembled.
4. `assembly.json` binds every input and output by SHA-256. `--complete` fails
   (`ASSEMBLY_INCOMPLETE`) unless every row is accepted and every proof task has its final theorem.

Assembly is deterministic: the same validation and submissions give the same assembly directory and a
byte-identical report.

## The datatype-identity boundary

Re-emitting a pending inductive `RocqPending.I h` as `Rocq.I` creates a **new type**. A template proved
about `RocqPending.I h` does not prove a statement about `Rocq.I`, and the kernel refuses the
instantiation: the task gets `ASSEMBLY_TRANSPORT_REQUIRED` (fixture: `is_zero_of_intro`). Nothing
identifies the two types or rewrites the proof. Such a task needs either a future proof of the final
statement or a transport rule (not implemented). Definitions are different: `Rocq.d` and
`RocqPending.d h` unfold to the same body with the hypothesis replaced, so a template about
`RocqPending.d h` is reusable (fixture: `zero_of_le`) — the kernel decides each case.

## Axioms

Submitted proofs of propositional tasks may use `propext`, `Quot.sound` and `Classical.choice`;
`sorryAx`, custom axioms and anything outside the allowance are refused. The translator's own
artifacts (statements, definitions, pending artifacts, the validated library) stay axiom-free.

An assembled declaration is **not** labelled axiom-free merely because the translator added no axiom:
an assembled data definition contains proofs in proof positions (e.g. `half_sig`'s `sig` field), and
`collectAxioms` follows them. The consumer reports the axioms of every assembled declaration
(`axioms_by_target`), including statements and inductives whose *types* mention such a definition. In
the fixture, `propext` from the obligation's proof is reported for `half_sig`, `zero_of`,
`zero_of_le.statement` and the inductive `is_zero_of`.

Proof position versus computation: Lean's definitional proof irrelevance makes a proof in a proof
position computationally inert. Computation that *inspects* a proof — an elimination of a `Prop`
inductive into a non-`Prop` sort whose major premise mentions an assembled proof (`Acc.rec`
recursion; casts are `Eq.rec`, which reduces by K-like reduction whatever the proof) — is reported by
the consumer (`proof_dependent_computation`). Its reduction behaviour then depends on how the proof
was written (a proof through an axiom does not reduce), and the current checks do not establish that
it is preserved: such a case is a reported limitation, not an accepted claim. (None in the fixture or,
so far, in assembled corpus rows: no corpus row has been assembled.)

## Computation (fixture measurement)

Kept as separate measurements (`reports/statement_only/test_assembly.json`):

* definitional reduction: `Rocq.SF.Asm.zero_of 3 = 0` by `rfl` (kernel) — holds;
* propositional unfolding equations: not applicable to the fixture;
* compiled evaluation: `#eval Rocq.SF.Asm.zero_of 3` fails ("Failed to find LCNF signature"):
  translated declarations are added through the kernel only and are never compiled. No code-generation
  backend is part of the translator.

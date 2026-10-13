# Statement-only translation: design

Status: direction adopted 2026-10-11. This supersedes the proof-transport objective. The
proof-preserving pipeline (M1–M6, P0; tag `p0-proof-transport-final`) is preserved and still tested,
but it is no longer extended.

## 1. Objective

Rocq2Lean mechanically and deterministically translates the **datatypes, definitions, operations
and elaborated theorem statements** of Prosa v0.6 and Classic Prosa (scope: `docs/SCOPE.md`), plus
the Rocq/MathComp/Stdlib/CoqEAL declarations those need, into Lean 4. **Original Rocq proof terms are
never translated.** The output is:

* a kernel-checked Lean library of datatypes, definitions and statement propositions, validated
  against the Rocq originals by an independent auditor;
* a machine-readable list of proof tasks, one per theorem statement and per extracted proof
  obligation, for a separate Lean proving agent.

Rocq2Lean does not write, generate, or check-in Lean proofs. It never introduces `sorry` or axioms, and
it never completes a declaration by hand. Success is measured by the correctness, determinism,
automation and coverage of the translator, not by theorems proved.

## 2. Two pipelines, kept apart

| | proof-preserving (historical) | statement-only (new) |
|---|---|---|
| request | `rocq2lean export` | `rocq2lean export --mode statement` |
| IR header `mode` | absent / `proof` | `statement` |
| proof-valued declarations | body transported and kernel-checked | statement only: `Rocq.<name>.statement : Prop` |
| definitions | body transported | body transported; proof subterms extracted as obligations |
| final status | `VERIFIED` (proof transported) | `STATEMENT_AUDITED` (definitions and statements validated); proofs `PROOF_PENDING` |
| tests | `test-all`, `test-m6-prosa`, `m6-finishtime-gate` (kept) | `test-statement` (new) |

Statuses and run directories never mix. A run's mode is bound in its IR, contract, report and
verdict. Historical `VERIFIED` results stay labelled as proof-transport evidence.

## 3. Component reuse

| Component | Reused as is | Changed for statement mode | Proof-transport only (unused here) |
|---|---|---|---|
| Exporter (`rocq/exporter`, MetaRocq `c18395ad`) | quoting, IR records, native metadata, universe facts, protection binding | a statement *preparation* of the environment (§5), on top of the existing prepared-body mechanism (sealed implementations, lowering) | — |
| IR (`docs/IR_SPEC.md`) | layout, terms, declarations | header `mode`; body state `statement_only`; obligation constants; `obligations` on definitions | — |
| Round trip (`tools/roundtrip.py`) | native re-checks in a fresh process | re-derives the statement preparation and compares | — |
| Contract (`tools/contract.py`) | roots, protection | required closure under the statement policy; proof tasks; obligations | — |
| Lean translator (`Rocq2Lean/`) | type, inductive, definition and fixpoint translation; universe rules R0–R8, R3G, P0 fixes; kernel insertion | statement emission; obligation statements; pending definitions | proof-term lowering of proofs (cast repair on proofs, accessibility lowering of proofs, R2B-P for proof bodies) |
| Audit (`tools/audit.py`) | structural source/target correspondence of types and definition bodies; universe checks; protection | statement definitions checked against the source types; no proof body accepted anywhere | proof-body checks |
| Consumer (`Rocq2Lean/Verify.lean`) | fresh re-read, axiom audit, protection | statement-library detectors (§8) | — |
| `verify` | anchoring, currency | `validate` for statement runs | R2B-P source instances of proof bodies |
| Inventory (`inventory/`) | census, protected interface | statement closure (`inventory/statement_closure.py`) | proof-transport coverage |

## 4. What is a proof (classification)

A constant is **proof-valued** when its type is a proposition. Rocq's kernel decides this in the
exporter (the sort of the constant's type is `Prop` or `SProp`), not the keyword:

* `Definition P : Prop := ∀ n, n = n` has type `Prop`, so it is a definition. Its body (the
  proposition) is translated.
* `Lemma p : P.` (or `Definition p : P. … Defined.`) has type `P : Prop`, so it is proof-valued. Only
  its statement `P` is translated.

Inductives are datatypes, translated with their parameters, indices and constructors (a `Prop`
inductive included). Lean generates its own eliminators. Rocq schemes (`_rect`, `_ind`, …) are
translated like any constant when something needs them (for example, a definition that computes with
`_rect`).

An opaque constant that is not proof-valued (`Definition d : T. … Qed.` with `T` not a proposition,
e.g. MathComp's `eqnP : Equality.axiom eqn`, whose `reflect` lives in `Set`, or `find_ex_minn`) is
**opaque data**. Rocq's kernel never unfolds it, so no Rocq statement or definition depends on its
body: its body is not exported, its type is kernel-checked as `def Rocq.d.type : Sort s := ⟦T⟧`
(`s` the exporter's native sort of `T`, state `opaque_interface`), and providing *a* value of that type
is a task. Opacity is read from the native environment, not from the P0-prepared one (the
preparation's lowering of SSReflect `have` turns some opaque bodies into transparent working copies;
they stay opaque data).

## 5. Statement closure and obligations

Roots: the protected public interface of the pinned inventory (4,474 declarations). The closure
follows elaborated kernel terms:

* **statement** edges: the type of every constant, and the arity, parameters and constructor types of
  every inductive;
* **computation** edges: the body of every constant that is not proof-valued, after obligation
  extraction;
* never: the body of a proof-valued constant (**proof-only**).

**Obligations.** A body that is not a proof can still contain proofs: the `eqP` field of an
`eqType` instance, `Sub x p`, an `eq_rect` cast, a `False_ind` branch. The exporter finds every
*maximal proof subterm* `t` of such a body with Rocq's kernel (`Retyping`: the sort of `t`'s type in
its local context `Γ` is `Prop`/`SProp`):

* `t` is a reference to a proof-valued constant `c`: `c`'s statement is required, and proving `c`
  becomes a prerequisite of the definition;
* otherwise `t` is replaced by `o Γ` for a new **obligation constant**
  `o := <def>__rocq2lean_obligation_<k> : ∀ Γ, T`, closed over the local context `Γ` of `t`.
  `T` is the type the position **expects** — the domain of the applied function at that argument
  (after the preceding, already rewritten arguments), or a `let`'s declared type — beta-normalized;
  only where no expected type is at hand is the inferred type used. The inferred type of a proof
  depends on how the proof was written (a tactic can leave a convertible variant, e.g. a beta-redex);
  the expected type depends only on the surrounding definition (negative control in `test-statement`).

The rewritten body `b'` must type-check against the original type in Rocq's kernel, with the
obligations as parameters (the exporter re-checks this, and the round trip re-derives it). `b'` and
the obligation statements are what is exported. The original proof subterms and their dependencies
are not. A proof-valued constant referenced from a *statement* (for example SSReflect phantom
witnesses) is handled the same way: the statement waits for that proof.

**Definitional effect.** Replacing a proof by an obligation constant changes what reduces only when
computation inspects the proof itself, for example structural recursion on an accessibility proof.
The exporter re-checks every rewritten declaration with Rocq's kernel under the constant's own
typing flags (a polymorphic constant under its abstract universe context). If the only failure is
the guard (a recursive call whose structural argument was a proof subterm, now an obligation), the
declaration is re-checked with everything but the guard, kept with `"termination": "deferred"` (in the
record and the header, re-derived by the round trip), and termination is never assumed: the Lean
translator has no rule for it yet, so such a declaration is refused by the translator
(`UNSUPPORTED_FEATURE`) instead of being translated with an unchecked recursion. Any other
failure leaves the definition without body (`obligation_extraction_failed`), reported. (The
motivating case, `find_ex_minn`, turned out to be opaque data, see §4.)

## 6. Lean representation

| Source | Lean target (accepted library `Rocq2LeanOut`) |
|---|---|
| inductive `I` | `inductive Rocq.I` (constructors, parameters, indices; universes by R2T/R5) |
| definition `d` | `def Rocq.d` (or `opaque` for opaque data), body translated |
| proof-valued `p : T` | `def Rocq.p.statement : Prop := ⟦T⟧` (universe parameters as in R2/R3G) |
| obligation `o : ∀ Γ, T` | `def Rocq.o.statement : Prop := ⟦∀ Γ, T⟧` |
| definition needing proofs `c₁ … oₖ` | **pending**: `def Rocq.d` is not added. Its translated body is kernel-checked as `RocqPending.d := fun {h₁ : ⟦c₁⟧.statement} … => ⟦b'⟧` (implicit hypothesis binders), in the same module `Rocq2LeanOut` but in the separate namespace `RocqPending`, which no accepted `Rocq.*` declaration references |

(An earlier version of this table said pending artifacts go to a separate module `Rocq2LeanPending`;
the implementation keeps one module and separates them by namespace, enforced by the consumer.)

The proving agent submits a *template* `RocqProofTemplates.T<task_id>.proof` proving the task
statement (§9). `Rocq.<name>` is reserved for the final declaration: once the prerequisites of a pending
declaration have final theorems, *assembly* (`docs/ASSEMBLY.md`) adds `Rocq.d` with its original
interface, referencing those theorems, and gives each proved task its theorem
`Rocq.p : Rocq.p.statement` where the kernel accepts the instantiated template. Rocq2Lean never
supplies those proofs.

Statement definitions have no proof-local universe levels: their only levels are those of the
statement. This removes the proof-body universe rules (R2B-P on proofs) from the statement path.

### Pending artifacts in Lean

A declaration that needs unproved prerequisites (proof tasks, directly or through other pending
declarations) is kernel-checked as `RocqPending.<name>` with one hypothesis per prerequisite leaf
(`h_<leaf>`, shared by every use, in order of first use; a prerequisite whose own statement is pending
is applied to the earlier hypotheses it needs). Pending inductives take the hypotheses as leading
parameters (references, constructors and recursor applications pass them first). Statements can be
pending too: any statement that mentions `leq` on `nat` waits for `eqnP`, because `nat`'s `eqType`
instance packs it. The accepted library `Rocq.*` never references `RocqPending.*`.

## 7. Statuses

`SOURCE_EXTRACTED` → `STATEMENT_TRANSLATED` → `STATEMENT_KERNEL_CHECKED` → `STATEMENT_AUDITED` →
`PROOF_PENDING` → (agent) `LEAN_PROOF_COMPLETED` → `LEAN_PROOF_KERNEL_VERIFIED`.

Definitions: `DEFINITION_AUDITED`, or `DEFINITION_AUDITED_PENDING` (pending artifact kernel-checked
and audited) until assembled. Statements: `STATEMENT_AUDITED` or `STATEMENT_AUDITED_PENDING`.
Translator row statuses: `TRANSLATED_AND_CHECKED`, `STATEMENT_KERNEL_CHECKED`,
`PENDING_KERNEL_CHECKED`, `STATEMENT_PENDING_KERNEL_CHECKED`; `rocq2lean validate` turns them into the
audited statuses above (run verdict `STATEMENT_VALIDATED`).
Translation failures keep the existing reasons (`UNSUPPORTED_FEATURE`, `UNIVERSE_REJECTED`,
`KERNEL_REJECTED`, `INTERFACE_REJECTED`, `RESOURCE_LIMIT`), and dependents are `BLOCKED_DEPENDENCY`.

## 8. Validation (acceptance of a statement or definition)

1. The Lean kernel accepts the declaration (statement definitions are definitions whose value is the
   proposition).
2. The independent audit (`tools/audit.py`) re-derives the correspondence:
   * binders, types, referenced declarations, universes and logical structure of `⟦T⟧` against the
     elaborated Rocq type;
   * definition bodies against `b'`;
   * obligation statements against the exporter's obligations.
3. Only accepted targets, bootstrap targets and kernel-generated constructors/recursors are
   referenced.
4. Public-interface protection: no protected declaration is narrowed (`INTERFACE_REJECTED`; P0
   enforcement in export, translator, consumer, audit and validate).
5. No axiom, `sorry`, `theorem` or opaque proof in the accepted library: `collectAxioms` is empty,
   and statement definitions are `def … : Prop`.

**How the audit checks a statement.** `tools/audit.py` (statement mode, selected by the IR header)
restates, from the source record alone, the declaration the translator builds: a leaf `c : T` is
`def c.statement : Prop := T` (`c.type : s := T` for opaque data), anything else is itself. The
existing structural and universe audit then applies unchanged. It also recomputes each claimed
row's prerequisites (leaves reached directly or through pending declarations), checks the reported
hypotheses and status against them, checks the hypothesis telescope binder by binder, and maps every
source reference to a leaf to its hypothesis (to a pending definition: its artifact applied to its
hypotheses). A claimed row may depend only on claimed rows.

**Negative controls.**
* Type-correct mutations of a statement (swapped arguments, a weakened hypothesis, a changed
  quantifier) must be rejected by the correspondence audit.
* Changing or complicating an irrelevant *source proof*, with the statement fixed, must leave the
  closure, the IR records used and the generated proposition byte-identical.

## 9. Proof-task interface

`rocq2lean tasks --run RUN` writes `RUN/PROOF_TASKS.jsonl`, one object per proof task (theorem
statement, extracted obligation, opaque data value, source assumption):

* source identity: kernel name, file, line;
* Lean statement constant and its rendered statement;
* the reserved theorem name and the output module path;
* the required Lean modules;
* parameters, instances and universe levels;
* prerequisites already proved, and prerequisites still pending;
* a priority: how many pending declarations need it (assembly unblocked);
* validation evidence (audit record digests);
* a stable task id (sha256 of the kernel name and the statement digest).

**Task statement.** Without prerequisites, the task is `Rocq.c.statement` (or `Rocq.c.type`). With
prerequisites `h₁ … hₖ` it is `∀ h₁ … hₖ, @RocqPending.c.statement h₁ … hₖ`. Each task records the form
of this generalization (`docs/ASSEMBLY.md`, "Task statements"): over propositions it is harmless (proof
irrelevance); over opaque *data* it can be strictly stronger than the source statement, and its
provability is **not** claimed. (An earlier version of this section claimed that every task can be
proved without waiting for its prerequisites; that is withdrawn for data prerequisites.) Opaque-data
value tasks accept no submission: the value must come from the source body (A′), not from an arbitrary
inhabitant.

`rocq2lean check-proof` checks a proof file submitted by the agent:
* it is the module `RocqProofTemplates.T<task_id>`, compiled in a fresh Lean process against the
  statement library, and it declares nothing outside its namespace;
* the template constant's type must be syntactically the task statement (a `theorem`; never an axiom,
  unsafe or partial);
* `collectAxioms` is recorded; anything beyond the declared allowance is refused, and `sorry`
  (`sorryAx`) is always refused.

Rocq2Lean itself never proves anything.

## 10. CLI (statement mode)

```
rocq2lean export   --mode statement --manifest M --roots R --out RUN
rocq2lean translate --input RUN/source.ndjson --out RUN
rocq2lean validate --run RUN                 # consumer + audit + protection; STATEMENT_AUDITED
rocq2lean tasks    --run RUN [--out FILE]    # proof tasks
rocq2lean check-proof --run RUN --task ID --file PROOF.lean [--allow-axioms A,B]
rocq2lean assemble --run RUN [--complete]  # final declarations from verified submissions (docs/ASSEMBLY.md)
```

## 11. Open points (tracked in `reports/statement_only/BLOCKER_REASSESSMENT.md`)

* Opaque data constants (`data_opaque`) built by tactics: their bodies are definitions, but they can
  contain proof subterms (obligations). Decided 2026-10-13 (A′): their data-producing bodies are to be
  translated mechanically, keeping their opacity and extracting their proof subterms as obligations;
  until then their dependents are not assembled (`OPAQUE_BINDING_PENDING`).
* Definitions whose computation eliminates a proof (structural recursion on a proof): exported with
  deferred termination, refused by the translator until a rule with a termination task exists.
* Universe rules for statements: R3 references and template `prod` at `Prop` in statements (as
  opposed to proofs).
* Coinductive data (Classic `extraction_tdma.Task_T`).

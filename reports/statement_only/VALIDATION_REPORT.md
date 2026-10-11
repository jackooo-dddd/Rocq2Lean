# Statement-only translation: validation report

Policy and design: `docs/STATEMENT_ONLY_DESIGN.md`. This report covers what the statement pipeline
checks, the evidence that the checks reject what they should, and the corpus results
(`TRANSLATION_RESULTS.json`). Rocq2Lean proves nothing. Every proof is a task for a separate Lean
proving agent (`PROOF_TASKS`).

## 1. What a validated row means

`rocq2lean validate --run RUN` (statement runs only; `verify` refuses them and vice versa, before
touching any artifact) returns `STATEMENT_VALIDATED` when all the gates below hold for every row the
translator claims. A row the translator did not claim is reported with its reason, never accepted.

| Gate | Check |
|---|---|
| source anchoring | snapshot hashes of sources, libraries, IR, manifest, toolchain; the round trip re-derives every statement preparation (rewritten type and body, state, obligations, deferred termination) in a fresh Rocq process |
| kernel insertion | every claimed declaration went through `addDecl` with checking at translation |
| fresh readback | a separate Lean process imports the module and compares every claimed declaration with the report (kind, type, value, levels, constructors); `collectAxioms` is empty; no `theorem`, `opaque` or `axiom`; accepted targets are `Rocq.*`, pending ones `RocqPending.*`, and accepted targets never reference pending ones; a proof task's statement is a `def` of type `Prop` (or a sort for opaque data) after its hypotheses; an accepted definition is not a proof |
| independent audit | `tools/audit.py` restates the declaration the translator must build from the source record alone (`def c.statement : Prop := T` for a proof task), recomputes the prerequisites, checks the hypothesis telescope, and compares types and values term by term. Each leaf reference must be its hypothesis. It also runs the universe (R2/R3/R5/R6/R8) and instance-level checks |
| interface | no protected Prosa/Classic declaration is specialized (no R2B-S, no R2B-P on a statement level) |
| freshness | every bound artifact is unchanged before and after validation; `tasks` and `check-proof` refuse a stale validation |

Per-declaration verdicts: `STATEMENT_AUDITED`, `STATEMENT_AUDITED_PENDING` (proof tasks),
`DEFINITION_AUDITED`, `DEFINITION_AUDITED_PENDING` (definitions and datatypes), `NOT_TRANSLATED`.

## 2. Tests (`scripts/test-statement`, `reports/statement_only/test_statement.json`)

29 checks, all passing at the commit of this report.

### Pipelines

| run | export / translate / validate | rows |
|---|---|---|
| FinishTime (5 Prosa roots, `fixtures/m6`) | 0 / 0 / 0, `STATEMENT_VALIDATED` | 73 definitions audited, 18 pending definitions audited, 2 statements, 5 pending statements |
| statement fixture A (`fixtures/stmt/a`) | 0 / 0 / 0 | 8 definitions, 2 pending definitions, 4 statements, 1 pending statement |
| statement fixture B (`fixtures/stmt/b`) | 0 / 0 / 0 | same |

All five FinishTime roots are translated and audited. They wait for exactly three prerequisites:
* `eqnP`, opaque data packed in `nat`'s `eqType` instance, on which every use of `<=` depends;
* a value of the opaque `find_ex_minn`;
* `finish_time`'s extracted obligation, the proof that the job finishes.

Before this work, all five were blocked (`find_ex_minn` was refused).

### Statement mutations (negative controls)

Each mutation changes a translated statement in a type-correct way. The mutated report is replayed
into Lean's kernel (`#rocq2lean_replay`), which accepts it; validation must then reject it through
the structural audit.

| mutation | declaration | kernel | validate | detector |
|---|---|---|---|---|
| swapped hypotheses | `finish_time.finished_at_finish_time` | accepted | rejected (2) | structure |
| negated conclusion | `finish_time.completes_at_finish_time` | accepted | rejected (2) | structure |
| negated conclusion | `SF.Stmt.double_succ` | accepted | rejected (2) | structure |
| dropped hypothesis | `SF.Stmt.le_trans_alt` | accepted | rejected (2) | structure |
| swapped arguments (`a <= b` ↦ `b <= a`) | `SF.Stmt.le_trans_alt` | accepted | rejected (2) | structure |
| universal ↦ existential quantifier | `SF.Stmt.double_even` | accepted | rejected (2) | structure |

The consumer accepts all six: they are well-typed, axiom-free declarations. Only the
correspondence audit catches them, which is what this control shows.

### Irrelevant proof change (negative control)

`fixtures/stmt/a` and `fixtures/stmt/b` have the same statements and definitions and different
proofs. Lemma proofs differ (`rewrite` vs `f_equal; exact plus_n_Sm`; `induction` vs `revert;
induction`), and so does the inline proof inside the definition `half_sig` (`induction n;
constructor; assumption` vs `apply le_0_n`).

* statement closure (contract): identical;
* exported declaration records (15): byte-identical;
* generated propositions and definitions (status, target, type, value, hypotheses): byte-identical.

The first run of this control **failed**: `half_sig`'s obligation statement differed, because the
exporter took the proof's inferred type, which a tactic left as a beta-redex. Obligations are now
stated by the type their position expects (`docs/STATEMENT_ONLY_DESIGN.md` §5), and the control
passes.

### Determinism, tasks, proof checker

* Translating the same export twice gives identical targets and statuses.
* `tasks`:
  * one task per proof-task statement;
  * task ids are stable across runs;
  * kinds are correct (theorem statements, obligations);
  * every task is `PROOF_PENDING` with its reserved name `Rocq.<name>`.
* `check-proof` rejects every negative submission, each for the intended reason:

| submission | reason |
|---|---|
| `:= sorry` | depends on `sorryAx` |
| a theorem of type `True` | type is not syntactically the task statement |
| a proof through a custom axiom | depends on the axiom `cheat`, outside the allowance |
| the reserved name declared as an `axiom` | is an axiom |
| no theorem with the reserved name | not declared |
| ill-typed proof | the module does not compile |

No positive proof check is part of the suite, because Rocq2Lean does not write proofs.

## 3. Historical proof-transport pipeline

`scripts/test-all` (18 proof-mode suites) passed on the statement-mode implementation (`4bec75f`,
see `STATUS.md`). The statement work changed shared code: the consumer (mode-selected), the audit
(universe section factored out; proof-mode audit output byte-identical on three verified runs),
replay, the retry ladder and the CLI. The statement-mode translation rules are gated by the IR's mode
(`GEnv.stmtMode`), so proof-mode translations are unchanged.

## 4. Corpus (`TRANSLATION_RESULTS.json`)

The merged statement export of both families (9,970 records, all 4,474 protected roots) was
translated under a contract carrying the pinned protection binding, then checked by the same
fresh-process consumer and independent audit that `validate` runs:

| check | result |
|---|---|
| merge | 0 inconsistent copies across 36 chunk exports: the statement preparation is request-independent |
| consumer | OK, all detectors (incl. namespaces, statements, target_deps, axioms, interface) |
| audit | OK: 3,990 claimed rows, all MATCH; 0 problems |

The first corpus pass was **not** clean: the audit reported 1,497 problems and the consumer an
interface failure. They were translator and report inconsistencies (statement level reporting,
opaque-interface sorts, an implicit-level rule, an R2F-c reporting bug, a ζ-order difference). Each
was fixed as a general rule (`STATEMENT_ONLY_REPORT.md` §4), and the corpus was re-run.

**Limit.** The corpus run uses the inventory export driver, not the CLI. It therefore has no
per-run source snapshot and no round trip. The round trip of the statement preparation (re-derived
in a fresh Rocq process) is exercised by the CLI runs in `test-statement`.

# Statement-only Rocq2Lean: report

Direction: `docs/STATEMENT_ONLY_DESIGN.md` (adopted 2026-10-11). Rocq2Lean mechanically translates
datatypes, definitions and theorem statements of Prosa v0.6 and Classic Prosa, and of the Rocq,
MathComp, Stdlib and CoqEAL declarations they need. It never translates a Rocq proof and never
writes a Lean proof: every proof is a task for a separate Lean proving agent. The historical
proof-transport pipeline (tag `p0-proof-transport-final`) is unchanged and still passes its tests.

Data:
* `TRANSLATION_RESULTS.json`: corpus outcomes;
* `PROOF_TASKS.jsonl`: 2,277 tasks;
* `VALIDATION_REPORT.md`: checks and negative controls;
* `BLOCKER_REASSESSMENT.md`: remaining blockers;
* `SCOPE_AND_DEPENDENCIES.md`: the closure.

## 1. Closure: proof-preserving vs statement-only

The exact statement closure comes from the exporter, which classifies each constant by Rocq's
kernel and extracts proof subterms. It covers all 4,474 protected roots.

| | proof-preserving (P0) | statement-only |
|---|---|---|
| source declarations | 10,588 | **5,622** |
| eliminated (needed only by proofs) | — | **4,966 (47%)** |
| extracted obligations (new) | — | 4,348 |
| exported records (all) | 10,588 | 9,970 |

* **Eliminated, by library:**
  * MathComp 2,820
  * Stdlib 1,492
  * Corelib 459
  * modern Prosa 125
  * CoqEAL 58
  * Classic 12

  Among them are the whole `lia`/micromega certificate machinery and the proof-local universe
  problems of P0 (`Sub_spec`, `insub_spec`, `big_const_seq`, `big_morph`, `mask_cat`, template
  `prod` at `Prop`).
* **Phase B approximation (6,017):** a strict superset of the exact closure. Its 395 extra
  declarations were reachable only through inline proof subterms, which the exporter now
  extracts.
* **The statement closure, by role:**
  * 2,819 proof-valued constants (statement only);
  * 121 opaque data (interface only);
  * 2,509 definitions;
  * 173 datatypes.
* **New obligations:** 4,348 proof subterms of definitions and statements, each stated as the type
  its position expects. They come mostly from Hierarchy-Builder factories in the MathComp
  algebra and order hierarchies (100 to 160 per builder), plus `eqType`/`choiceType` instance
  proofs and Prosa's own definitions (e.g. `finish_time`'s existence proof).

## 2. Corpus result

All 9,970 records were translated in one Lean process (15 min, 3.8 GB). Then the fresh-process
consumer and the independent audit checked every claimed row:

* consumer **OK**, all detectors;
* audit **OK**: 3,990 claimed rows, all MATCH;
* 1,668 accepted rows;
* 2,322 pending rows (kernel-checked with their unproved prerequisites as hypotheses);
* 0 problems.

Protected public interface (`reports/prosa_inventory/protected_interface.json`):

| | statements | definitions | datatypes | total translated and audited | blocked by a dependency | direct failures |
|---|---|---|---|---|---|---|
| modern Prosa (2,504) | 787 / 1,564 | 544 / 921 | 15 / 19 | **1,346 (54%)** | 1,140 | 18 |
| Classic Prosa (1,970) | 729 / 1,304 | 496 / 651 | 12 / 15 | **1,237 (63%)** | 725 | 8 |

"Translated and audited" includes pending rows: a statement or definition kernel-checked together
with its prerequisite proof tasks as hypotheses, and accepted into the library once those proofs
are kernel-verified.

At the start of this phase, the first statement run blocked all five FinishTime roots, because
`find_ex_minn` was refused. All five are now statement-validated through the CLI
(`test-statement`).

## 3. Proof tasks (`PROOF_TASKS.jsonl`)

There are 2,277 tasks: 1,529 theorem statements, 706 obligations and 42 opaque-data values. Of
these, 787 are modern, 753 Classic and 737 external.

Each record carries:
* the source identity (kernel name, file, line);
* the Lean statement constant and the task statement to prove;
* the reserved name `Rocq.<name>` and the output module;
* the pending prerequisites;
* validation evidence (audit and consumer digests);
* a stable id;
* a priority: how many pending declarations need the task for their assembly.

A task with prerequisites is stated generically over them (`∀ h, RocqPending.c.statement h`). Proof
hypotheses are irrelevant, and Rocq never unfolds opaque data, so every task can be proved
independently. `rocq2lean check-proof` verifies a submitted proof:
* in a fresh process;
* the statement must be exactly the task statement;
* no `sorryAx`;
* axioms within the declared allowance.

Highest priorities (pending declarations needing each task):

| task | kind | needed by |
|---|---|---|
| `mathcomp.boot.ssrnat.eqnP` | opaque value (`Equality.axiom eqn`) | 2,114 (sole prerequisite of 1,196) |
| `mathcomp.boot.eqtype.opt_eqP` | opaque value | 707 |
| `mathcomp.boot.eqtype.inj_eqAxiom` | opaque value | 522 |
| `mathcomp.boot.choice.PCanHasChoice` | opaque value | 513 |
| `mathcomp.boot.choice.PCanIsCountable` obligation | obligation | 500 |
| `mathcomp.boot.choice.nat_hasChoice` | opaque value | 487 |
| `Corelib.ssr.ssrbool.idP` | opaque value | 420 |

The `eqType`/`choiceType` proof fields come first, as directed. `eqnP` alone gates the assembly of
most pending Prosa declarations, because `nat`'s `eqType` instance packs it and every `<=` on `nat`
goes through that instance.

## 4. What changed in the translator (this phase)

All changes are mechanical rules, tested on the fixtures and the corpus. None is
declaration-specific.

* **Exporter: statement preparation.**
  * Proof-valued constants are kept as statements.
  * Maximal proof subterms become obligations, stated by their expected type; local
    hypotheses stay.
  * Opaque data is decided by native opacity.
  * Polymorphic constants are re-checked under their abstract context and their own typing
    flags.
  * Deferred termination is recorded, never assumed.
  * The round trip re-derives all of this.
* **Translator: pending validation.**
  * Hypotheses are abstracted before universe solving.
  * Deterministic hypothesis names.
  * Pending inductives take hypotheses as parameters.
  * Opaque-interface sorts are inferred.
  * The retry ladder keeps pending results.
  * Statement-mode R3G refinements: the pick on partly determined arguments, implicit levels
    shared with referenced declarations, never a class that holds an own level.
  * The R2F-c tier is refused when unification merges interpreted levels.
  * ζ is applied before lowering.
* **Audit and consumer.**
  * Statement views and recomputed prerequisites.
  * Hypothesis telescopes.
  * Pending inductives.
  * Statement-mode consumer detectors (namespaces, accepted rows never referencing pending
    ones, statement shapes, nothing proof-like accepted).
* **CLI.**
  * `export --mode statement`, `validate`, `tasks`, `check-proof`.
  * `verify` and `validate` refuse runs of the other mode.

Several of these were found by the independent checks themselves: 1,497 audit problems on the
first corpus pass, now 0. One was found by the irrelevant-proof negative control.

## 5. Remaining blockers (genuine)

Details are in `BLOCKER_REASSESSMENT.md`.

| blocker | protected declarations blocked | nature |
|---|---|---|
| `mathcomp.boot.div.edivn_rec`, `modn_rec` | 694, 490 | recursion on `m - d` (Rocq's guard sees through `subn`): needs a rule with an explicit termination obligation |
| Prosa `JLFP_policy`, `FP_policy`, `JLDP_policy` | 447, 248, 225 | universe: `ssrbool.1105 ≤ eqtype.51` not entailed (known since P0) |
| `prosa.model.processor.ideal.processor_state` obligations | 280 | unjustified residual universe defaults in the obligation statements |
| Classic `SporadicTaskset.taskset_of`, `Affinity.affinity`; modern `ArrivalCurvePrefix` | 216, 189, 195 | the only accepted translation would narrow a protected declaration (R2B-S), refused |
| MathComp `nmodule` HB structures | 79 | `reverse_coercion` and HB phantoms vs Lean's lack of cumulativity |

## 6. Reproduce

```
INVENTORY_EXPORT_MODE=statement INVENTORY_EXPORT_CHUNK=96 INVENTORY_EXPORT_MEMORY=16G \
  python3 -I inventory/export.py modern 2      # and classic (about 16 + 10 min)
python3 -I inventory/statement_run.py merge     # 0 inconsistent copies: request-independent
python3 -I inventory/statement_run.py translate  # contract with protection binding
python3 -I inventory/statement_run.py check      # consumer + audit
python3 -I inventory/statement_run.py summary    # TRANSLATION_RESULTS.json
python3 -I inventory/statement_run.py tasks      # PROOF_TASKS.jsonl
scripts/test-statement                           # 29 checks
scripts/test-all                                 # proof-transport regression (18 suites)
```

For a single root set, the CLI path is `rocq2lean export --mode statement`, then `translate`,
`validate`, `tasks` and `check-proof`.

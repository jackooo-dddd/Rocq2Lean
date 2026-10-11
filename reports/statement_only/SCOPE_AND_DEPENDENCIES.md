# Statement-only scope and dependency closure (Phase B)

Policy: `docs/STATEMENT_ONLY_DESIGN.md`. Sources and versions are unchanged
(`reports/prosa_inventory/scope.lock.json`):
* Prosa v0.6 `414e6676`: 357 files.
* Classic (ProsaBuddy `f692cb74`): 190 files, all compiled (authorized RTS compatibility patch, see
  P0).

Data:
* `reports/statement_only/closure.jsonl`: one record per declaration, with what it is needed for and
  its typed edges;
* `closure_summary.json`;
* `blocker_reassessment.json`.

Tool: `inventory/statement_closure.py`, which works on the census store (every elaborated record of
the old closure, with type and body dependencies kept apart).

## Roots

The protected public interface: **4,474** declarations (2,504 modern, 1,970 Classic). Under the
statement policy they split into:

| roots | count |
|---|---|
| theorem statements (proof-valued, statement only) | 2,763 |
| definitions (bodies translated) | 1,677 |
| datatypes (inductives, records, classes) | 34 |

## Closure: proof-preserving vs statement-only

| | proof-preserving (P0 census) | statement-only |
|---|---|---|
| declarations in the closure | 10,588 | **6,017** |
| eliminated as proof-only | — | **4,571** (43%) |

Eliminated by library: MathComp 2,646, Stdlib 1,460, Corelib 360, modern Prosa 92, Classic 10,
CoqEAL 3. By nature: 2,255 opaque proofs, 504 transparent proofs, 1,281 data definitions, 207
inductives and 162 type formers that were reachable only through proofs (e.g. `lia`'s
`ZMicromega`/`RingMicromega` certificate machinery and Stdlib arithmetic).

The statement-only closure (6,017) by what is translated:

| | statements | definitions | datatypes |
|---|---|---|---|
| modern Prosa | 1,502 | 1,094 | 19 |
| Classic | 1,309 | 700 | 15 |
| MathComp | 177 | 719 | 105 |
| Corelib | 36 | 164 | 34 |
| CoqEAL | 12 | 80 | 3 |
| Stdlib | 23 | 20 | 0 |
| Hierarchy-Builder | 1 | 3 | 1 |
| **total** | **3,060** | **2,780** | **177** |

## Proof tasks and obligations

* **3,060 statements** become proof tasks.
  * 2,811 are in-scope theorem statements, including the 4 Classic `Admitted` facts, which stay
    labelled as source assumptions.
  * 249 are statements of external lemmas that some definition, instance or statement *needs as a
    proof*.
* **Proof-valued constants referenced by bodies that are not proofs: 300.**
  * 177 MathComp, 37 modern, 36 Corelib, 23 Stdlib, 14 Classic, 12 CoqEAL, 1 HB.
  * These are the obligation statements (825 obligation edges): for example `eqtype` decidability
    proofs inside `eqType` instances, `eq_ind`/`eq_ind_r`/`False_ind` inside dependent casts, and
    `job_finishes` inside `finish_time`.
* **Bodies that contain such references: 300 definitions** (179 external, 102 modern, 19 Classic).
  For example Prosa's `eqn_job`/`eqn_task` (decidable equality of concrete jobs/tasks),
  `finish_time`, `quiet_time_P`, `scheduled_at_dec`. They are pending until their obligations are
  proved. Independent declarations continue meanwhile.
* **Statements whose *types* mention a proof constant: 121**, plus 85 definitions and 2 datatypes.
  These are mostly SSReflect phantom witnesses (`inPhantom`, `id_phant`) in `{in D, P}`-style
  statements. They are recorded as obligations of those statements.

**Approximation in these Phase B counts.** Proof subterms written *inline* in definition bodies
(not references to a proof-valued constant) are not delimited here; that needs typing. Their
references are counted as computation edges, so the closure above is an over-approximation for such
definitions. The statement-only exporter (Phase C) delimits them with Rocq's kernel and replaces
them by extracted obligation constants. The counts are then recomputed from the exported IR
(`TRANSLATION_RESULTS.json`).

## Dependency kinds (edges of the statement closure)

| kind | edges |
|---|---|
| statement (types of constants) | 66,843 |
| computation (bodies of non-proof constants) | 26,221 |
| datatype (arities, parameters, constructors) | 996 |
| obligation (non-proof body → proof-valued constant) | 825 |
| proof-only (bodies of proofs) | not followed |

## Exact closure (measured, statement exporter)

The statement-mode exporter (Phase C) computes the closure exactly. It classifies constants with
Rocq's kernel and extracts inline proof subterms as obligations stated by their expected type.

| | Phase B approximation | exact |
|---|---|---|
| source declarations | 6,017 | **5,622** |
| eliminated vs the proof-preserving 10,588 | 4,571 | **4,966** |
| extracted obligation constants | (not delimited) | 4,348 |

The exact closure is contained in the approximation; the 395 declarations it drops were reachable
only through inline proof subterms.

Exact closure by role:
* 2,819 proof-valued (statement only);
* 121 opaque data (interface only);
* 2,509 definitions (4 sealed implementations);
* 173 datatypes.

Eliminated by library:
* MathComp 2,820
* Stdlib 1,492
* Corelib 459
* modern Prosa 125
* CoqEAL 58
* Classic 12

## Reproduce

```
scripts/inventory-prosa                          # census (unchanged)
python3 -I inventory/statement_closure.py        # this closure
```

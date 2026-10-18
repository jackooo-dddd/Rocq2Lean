# Incremental runs

Status: **experiment** (branch `incremental`). It changes no acceptance policy. Every run now writes replay
records and names its metavariables per declaration (§4). Incremental runs are used for experiments; a stage's
evidence remains a full run.

## 1. What a declaration's translation depends on

The translator processes the export's declarations in order. Translating declaration `d` reads:

* `d`'s source (IR term, native facts), and the export-wide tables computed once from the source
  (`irBodies`, `carrierSet`, …);
* the translator's code and configuration (the heartbeat budget is counted in heartbeats, not time);
* what earlier declarations left behind: their rows (`results`: status, `prop_lift`, pending hypotheses),
  their environment entries (`GEnv`: `consts`, `constGlobals`, `leafStmt`, …), and the Lean declarations
  they installed. Only `d`'s dependencies, direct or through others, are reached: through references and
  through δ-unfolding of what they reference.

So if a rule change cannot affect `d` directly, and no declaration in `d`'s dependency closure produced
different output, `d`'s output is the base run's.

## 2. Replay records

Every run writes `replay_records.jsonl`, one line per source declaration:

| Field | Meaning |
|---|---|
| `decl`, `kind` | the source declaration and its kind |
| `genv` | whether its environment update was kept (not after an internal error or resource limit) |
| `added` | the Lean declarations it installed through the kernel (`addChecked`), still present after it, each once, in the order of its last installation |
| `rows` | per row of the declaration (the main row and its generated rows), in report order: `source`, `param_levels` (the universe parameters' source levels, not in the report) and `target` (as name components) |
| `selfcheck` | present only if replaying the row would not register what translating it did (below) |

**Self-check (every run).** After a constant is translated, its rows are turned into JSON and back, as
replay reads them, and registered by the same functions translation uses (`registerConstant`,
`registerCommon`, `registerSplit`, factored out of `translateDecl` unchanged). The resulting environment
is compared with the real one: the size of every table and the entries under every name the declaration
registers. A mismatch is written into the record and counted in `replay_summary.json`.

## 3. An incremental run

`R2L_REPLAY_BASE=<base run directory>` and `R2L_RERUN=<file>` (declarations to translate again, one per
line; `tools/select_rerun.py` builds it). The base run must have translated the same export (its report's
`input_sha256`), and it cannot be the run itself. In order, each declaration is:

* **replayed**, if it is a constant, it is not selected, and none of its dependencies is *tainted*.
  The declarations it installed are taken from the base run's module (`lean/Rocq2LeanOut.olean`, read
  with `readModuleData`, not imported) and submitted to the kernel again (`addChecked`, unchanged).
  Its rows are the base report's lines, byte for byte. Its environment entries are registered as in the
  self-check. If any step fails (a name missing from the base module, a kernel rejection), the
  declaration is translated instead and the fallback is reported.
* **translated** otherwise. Inductives are always translated (7 s of S21s). The new rows and record are
  compared with the base run's, without messages and diagnostics (they name metavariables). If they
  differ, the declaration is *changed* and tainted. A declaration translated because a dependency was
  tainted is tainted itself, even if its rows are unchanged, because its dependents can unfold it to
  the changed declaration.

Outputs: the full report, timing, module and replay records, as in a full run, so an incremental run can
itself be a base. Plus `replay_summary.json`: rows replayed and translated, `changed`, `fallback`,
`selfcheck_failures`, and the load and translation times. In the timing file, a replayed row has
`time_ms` 0, `replayed: true` and the base run's `tier_times`.

**Selection (`tools/select_rerun.py`).** It only needs to cover the declarations a change can affect
*directly*, because change propagation adds their dependents. By tier flag: `--flag un` selects every
declaration with an attempt that had flag `un` in the base run (code that runs only in such attempts can
change nothing else). By outcome: `--failed` (a new last tier runs only after every existing tier
failed), `--status S`. By name: `--names FILE`.

## 4. Determinism

An incremental run reproduces a full run only if a declaration's translation depends on nothing but its
inputs (§1). One dependence on everything translated before was found and removed. Level metavariable
sets are iterated in hash order, and their names came from a counter shared by the whole run: `prof-A`
with the least-solution change, incremental vs full, numbered `JobTask`'s two residual levels the other
way round. Each declaration now names its metavariables from its own position in the export
(`namePrefix := _r2l.<index>`).

Known remaining difference: heartbeat consumption can depend on Lean's caches filled by earlier
declarations, so an attempt near its budget can abort at another point. So far this has shown only in the
message of a failing row, never in a status or term.

## 5. Validation

`prof-A` (690 declarations):

| Test | Result |
|---|---|
| base run (new code) vs the earlier `prof-A` rows | 0 rows differ; self-check passes for all 690 |
| incremental, nothing selected | 8 s (base 456 s); 608 rows replayed, 82 translated; rows byte-identical; 0 changed, 0 fallback |
| incremental, every failing constant selected | 196 s; 0 changed; 1 row differs from the base in its message only (a budget-aborted attempt's solver log) |
| least-solution change: incremental (`--flag un`, 110 selected) vs full run with the change | see §6 |

## 6. Precise selection: attempt reasons, probes, and the retroactive check

A selection by tier flag is sound but coarse: the costly declarations go through almost every tier
(S21s: an attempt with `un` 82% of the translation time, `lo`/`cu`/`p3` 91%). Three layers make it precise.

1. **Attempt reasons** (recorded since entry 14). The timing keeps each refused attempt's status and the
   first 600 characters of its message (`STATUS | message`; `RESOURCE_LIMIT | aborted` for a budget abort).
   `select_rerun.py --reason REGEX` selects every declaration with an attempt refused for a matching
   reason. That is the selection for a change that relaxes a check: it includes accepted declarations,
   whose earlier attempt may now be accepted, which a selection by final message misses.
2. **Probes** (`probe`, `probeLog`): named branches where a universe level is chosen, counted per
   declaration over all its attempts and written to its replay record (`probes`). `--probe NAME` selects
   the declarations that reached the branch, for a change confined to it. A new probe needs a new base
   run (a replayed declaration carries its base run's probes). The probes so far:

   | Probe | Branch |
   |---|---|
   | `rebind.self_occurrence` | `rebindShared`: an own level solved through this occurrence, named by its parameter |
   | `rebind.class_several_levels` | `rebindShared`: one class of occurrences for several shared levels |
   | `rebind.left_free` | `rebindShared`: a class whose lowest level is not an own level, left to R3G |
   | `default.minimal_model`, `default.zero` | a free proof-local level defaulted to its minimal model / to 0 |
   | `solver.assign`, `solver.left` | the bounded solver assigned a postponed constraint / left one |
   | `r3g.implicit_level` | R3G names a class of references after a source level (an implicit level) |
   | `r3g.body_level_by_reference` | statement mode: a body level made a type level through a reference |
   | `carrier.copies` | R-CARRIER P2 renamed levels into per-class copies |

3. **Retroactive check** (`tools/check_selection.py BASE FULL SELECTION`). Given a full run of the changed
   translator, it replays the incremental algorithm with the full run as the oracle and lists the
   *misses*: declarations whose rows changed but that the selection, with change propagation, would have
   replayed. Every stage's full run can check the selections used during the stage.

`prof-A`, least-solution change (`rebindShared`'s self-occurrence branch, against the full run with the
change; `check_selection.py`):

| Selection | Selected | Translated (with inductives and propagation) | Their base time | Misses |
|---|---|---|---|---|
| `--flag un` | 110 | 139 | 415 s | 0 |
| `--probe rebind.self_occurrence` | 7 | 90 | 118 s | 0 |

What no selection covers: a change to shared machinery (unifier calls, iteration order, the tier order,
budgets beyond aborted attempts). That needs a full run.

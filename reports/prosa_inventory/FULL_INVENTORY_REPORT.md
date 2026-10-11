# Prosa v0.6 + Classic: full inventory and gap analysis

**Verdict: `INVENTORY_PARTIAL`.** Every authoritative file is accounted for and every compiled
module has a mechanical declaration inventory. The one gap is 3 of the 190 Classic files, which do
not compile under the fixed toolchain without editing a proof. Their declarations are recorded as
`UNKNOWN`, not zero. Nothing here is a translation result: no declaration was promoted to VERIFIED
by this work.

Regenerate with `scripts/inventory-prosa` (stage logs in `.work/inventory/logs/`, run record in
`run_log.json`). Consistency tests: `scripts/test-inventory`. Scope: `docs/SCOPE.md`.

## 1. Sources (`scope.lock.json`)

| | Modern Prosa (P) | Classic (C) |
|---|---|---|
| Identity | Prosa v0.6 `414e6676…` (release sha512 `128dd213…`) | ProsaBuddy `f692cb74…`, `prosaworkspace/classic/` (tree `24727b13…`) |
| RTS authority | `f23ca672…`: 357/357 files hash-identical to RTS's inventory | the 49 case-study files: 49/49 hash-identical to RTS's plan |
| Files | 357 (343 main + 14 refinements behind CoqEAL) | 190 (the whole directory) |
| Build | 357/357 compiled (refinements with CoqEAL `ce3d1d68`, five modules, unchanged) | 187 compiled, 1 compile error, 2 not built (dependency failed) |
| Import-only files | 7 | 3 |
| Environment | Lean 4.33.1, Rocq 9.3.0, MathComp 2.6.0, MetaRocq `c18395ad`; five M6 compatibility patches | + RTS prelude `Rocq90Compat.v` (two Rocq 9.0 defaults); `prosa.util` from the modern working snapshot |

Classic imports 12 `prosa.util` modules. ProsaBuddy's bundled copies are identical to the official
v0.6 ones. Three of them (`notation`, `seqset`, `tactics`) carry the M6 compatibility patches in
the working snapshot, which is recorded in the lock. Excluded copies, and the reasons, are in
`scope.lock.json`: ProsaBuddy's `rt-proofs-v0.6/classic/`, RTS's `classic-prosa/classic/`, the
RTS_Papers case studies, and Prosa v0.4.

**Build gap (Classic).** `classic/analysis/global/jitter/bertogna_edf_theory.v` line 332 fails
under Rocq 9.3 / MathComp 2.6 with "The LHS of ltn_add2r … does not match any subterm of the goal".
`bertogna_edf_comp.v` and `implementation/global/jitter/bertogna_edf_example.v` depend on it.
RTS ships a one-hunk proof-script patch (`prosabuddy-classic-rocq93.patch`; the statement is
unchanged). It is **not applied**, because the brief forbids changing proofs to obtain an inventory.
Applying it is a decision for the project owner.

## 2. Counting conventions

* **Declaration.** An entry of the compiled environment (MetaRocq `tmQuoteModule` over each
  compiled module, after all Sections are closed) whose name is its kernel identity. Regex counts are
  not used. Source text only attributes an entry to its sentence (keyword, locality, line).
* **Ownership** is by source file. P and C are disjoint. Classic's uses of `prosa.util` are P
  declarations in C's closure. Combined counts are |P| + |C|, and nothing is merged by short name
  (230 public short names occur in both families and are kept apart).
* **Roles.** `public_source` (a non-local source sentence) and `generated_projection` (record and
  class fields) form the **protected target interface**. The other roles are
  `source_local_helper` (`Local` / `#[local]`), `generated_scheme`, `generated_hb`,
  `generated_obligation`, `generated_instance`, `generated_anonymous_goal`, and `alias_reexport`
  (module-alias entries such as `Module basic := UniprocessorSchedule`; they point to their
  canonical declaration and are not counted).
* **Nature** is read from the elaborated type, not from the keyword:
  * `proof_opaque` / `proof_transparent`: the type's sort is Prop/SProp.
  * `data_definition` / `data_opaque`: inhabitants of Set/Type.
  * `type_former`: the codomain is a sort.
  * `inductive`.
  * `assumption`: a genuine source axiom.
* **Closure**: every kernel declaration reachable through elaborated types, transparent bodies and
  opaque proof bodies (`lia` certificates included), as recorded by the exporter.
* **Unknown** values are the string `UNKNOWN`, never 0.

## 3. Totals

| | Modern P | Classic C | Combined |
|---|---|---|---|
| Enumerated entries | 2,707 | 2,547 (incl. 562 module aliases) | 5,254 |
| Declarations | 2,707 | 1,985 (+ `UNKNOWN` in 3 files) | 4,692 (+ `UNKNOWN`) |
| Public source declarations | 2,440 | 1,870 | 4,310 |
| Protected interface (public + projections) | 2,504 | 1,922 | 4,426 |
| Source-local helpers | 122 | 1 | 123 |
| Generated (projections, schemes, HB, obligations, instances, goals) | 145 | 114 | 259 |
| Proof-valued (opaque / transparent) | 1,549 / 20 | 1,261 / 8 | 2,810 / 28 |
| Data definitions / opaque data / type formers / inductives | 685 / 96 / 338 / 19 | 478 / 20 / 197 / 15 | 1,163 / 116 / 535 / 34 |
| Genuine source assumptions | 0 | 4 (`Admitted` in `tdma_rta_example`) | 4 |
| Relaxed checking flags / universe-polymorphic | 0 / 0 | 0 / 0 | 0 / 0 |
| Closure (distinct kernel declarations) | 8,256 | 5,268 | 10,539 |

The combined closure is 10,539 declarations: 4,692 in scope plus **5,847 external**. The external
ones split into MathComp 3,647, Stdlib 1,503, Corelib 594, CoqEAL 98 and Hierarchy-Builder 5.
2,985 declarations are shared by both closures. Classic reaches 60 P declarations (its
`prosa.util` imports). The semantic graph has 314,316 edges, no missing targets, no cycles, no
inconsistent copies across export chunks, and no conflicts between the two families' records.

Two Classic natures are `unknown_opaque` (the type's sort could not be read without reduction).
External `unknown_*` natures (67) do not affect in-scope counts.

## 4. Reconciliation with RTS's historical inventories

* **Modern.** All **2,439** RTS declarations are present in the compiled environment and all are
  `public_source` here. The one extra public declaration is `prosa.util.seqset.mem_set_predType`, a
  `Canonical Structure` sentence that RTS does not count. RTS's 239 "unresolved CoqEAL boundary"
  types are now elaborated (the refinements compiled). The other 267 compiled entries are helpers
  and generated declarations, which RTS does not list.
* **Classic plan.** The 49 files / 24 case studies: all compiled; **525** public declarations,
  equal to RTS's 525. The other 141 Classic files are inventoried too.

## 5. Coverage (`coverage.jsonl`; each dimension kept separate)

| | Modern | Classic |
|---|---|---|
| Built and exported | 2,707 | 1,985 (3 files `UNKNOWN`) |
| Preflight (current `tools/preflight.py`, unchanged): candidate / blocked dependency / direct | 1,930 / 769 / 8 | 1,697 / 280 / 8 |
| Known blocker (preflight + current translation evidence): none / downstream / direct | 1,350 / 1,345 / 12 | 833 / 1,144 / 8 |
| Protected interface with no known blocker | 1,271 of 2,504 | 785 of 1,922 |
| VERIFIED as a root / as a dependency only | 87 / 76 | 0 / 0 |
| Kernel-checked in an unverified run / attempted, not translated | 43 / 24 | 0 / 0 |
| Never attempted | 2,477 | 1,985 |
| Public interface specialized (R2B-P/R2B-S) as a dependency | **1** (`ArrivalCurvePrefix`) | 0 |

Evidence comes from current-implementation runs only (implementation tree `819383b9…`): the ten M6
completion runs and the 30 single-root confirmation runs of section 7. A run counts for a
declaration only when the elaborated record is **byte-identical** to the census record. All 11,359
M6 run records that are also in the census are identical. 47 MathComp holdout records lie outside
the Prosa closure.

**Interface conflict.** In the confirmation run for `concrete_job`, the public definition
`prosa.implementation.definitions.extrapolated_arrival_curve.ArrivalCurvePrefix` was translated as
a dependency with R2B-S result-sort lowering (level `…extrapolated_arrival_curve.21` := 0). The
current translator allows statement specialization of a protected Prosa declaration when it is
not itself a root. 172 external dependencies are specialized the same way, which is allowed.

"No known blocker" is not a translation result. Most of those closures were never attempted, and
preflight is static.

## 6. Blocker map (`blockers.json`)

Grouped by mechanism. Each group gives its defining declarations, a reproducer, the affected roots
(modern / Classic) and an in-scope dependency path. "Sole" means no other known mechanism blocks
the root. Evidence: `preflight` (static), `translation:<run>` (M6 runs) or `inv-confirm-*`
(confirmed probe failures).

| Mechanism | Category | Defining nodes | Affected M / C | Sole M / C | Example path |
|---|---|---|---|---|---|
| Reference argument not entailed by the source universe graph | universe | **`FP_policy`, `JLFP_policy`, `JLDP_policy`** (Prosa), `eqtype.Sub_spec`, `bigop.big_morph` | 773 / 825 | 272 / 0 | IBF `arrives_after_beginning_of_busy_interval` → `ltn_ord` → `valP` → `Sub_spec` |
| Proof-local level, strict native fact `Set < u` | universe | `choice.PCanHasChoice` | 619 / 822 | 190 / 0 | … → `eqtype_can_type__canonical__choice_Countable` → `PCanHasChoice` |
| Default cast annotation not convertible in Lean | missing rule | `eqtype.insub_spec` | 256 / 823 | 0 / 0 | … → `val_ord_enum` → `insubK` → `insub_spec` |
| Recursive call on a non-field term (recursion through `subn`) | missing rule | `div.edivn_rec`, `div.modn_rec` | 180 / 536 | 109 / 257 | `corresponding_job_in_hyperperiod` → `lcml` → `divn` → `edivn` → `edivn_rec` |
| Proof-local level, native `le` fact | universe | `bigop.big_const_seq` | 222 / 427 | 14 / 41 | `cumulative_job_interference_bound` → `sum1_size` → `big_const_seq` |
| Template `prod` at quality Prop | universe | `ssrnat.leqif`, `ssrfun.pair_of_and`, `ssrnat.nat_of_add_pos` | 479 / 0 | 55 / 0 | `service_in_implies_scheduled_in` → `sum_nat_eq0` → `leqif` |
| Coinductive type | missing rule | `Morphisms.normalization_done`; Classic `extraction_tdma.Task_T` | 219 / 13 | 15 / 8 | setoid-rewriting proofs → `normalization_done` |
| Defaulted universe level not justified | universe | `seq.mask_cat` | 162 / 32 | 4 / 0 | … → `subseqP` → `mask_cat` |
| Kernel: application type mismatch | incorrect implementation | **`implementation.definitions.task.concrete_job`** (Prosa), CoqEAL `refines_abstr2` | 84 / 0 | 25 / 0 | `concrete_job` (direct) |
| Kernel: declaration type mismatch | incorrect implementation | CoqEAL `hrel.fun_hrel` | 82 / 0 | 22 / 0 | refinements `refine_blocking_bound` → `Rnat` → `fun_hrel` |
| Course-of-values recursion on an indexed inductive | missing rule | CoqEAL `param.{all,cat,filter,foldr,has,last,map,zip}_R` | 48 / 0 | 4 / 0 | `refine_blocking_bound` → `refine_foldr_max` → `map_R` |
| Reference argument (`max`) not entailed | universe | CoqEAL `refines_fst_R`, `refines_snd_R` | 39 / 0 | 0 / 0 | `refine_arrival_curve_prefix` → `refines_fst_R` |
| Genuine source assumption | source assumption | 4 `Admitted` facts in Classic `implementation/uni/basic/tdma_rta_example.v` (incl. the example's main theorem `ts_is_schedulable_by_tdma`) | 0 / 4 | 0 / 0 | direct |
| SProp eliminators (`_sind`) | universe | 11 generated schemes | 8 / 3 | 0 / 0 | direct, not protected |

**Co-blocking.** The largest combination is `insub_spec` + `Sub_spec`-type entailment +
`PCanHasChoice`, which blocks 388 roots that none of them unlocks alone. Most Classic roots sit
behind such MathComp `eqtype`/`choice` combinations. The full list is in `blockers.json`.

**Not counted as blockers:**

* **Context-dependent failures.** `mathcomp.boot.fintype/isFinite.axioms_` gets a kernel
  rejection ("application type mismatch") in some requests: a holdout run, and the single-root
  request for Prosa's `JobReady`. It is VERIFIED in others, including the gate.
  `Corelib.ssr.ssreflect_rw.nary_congruence`'s R2B-P statement specialization was rejected by Rocq
  in one run; it translated in four. Over 2,000 in-scope roots reach each of them.
* **Preflight contradicted by evidence.** Preflight rejects `Corelib.Init.Wf.Acc_rect` ("a type
  depends on an argument that recursive calls change"), but current runs translate it, including
  the VERIFIED gate. 754 modern and 268 Classic roots reach it.

**Resource limits (not semantic):**

* The exporter overflows the CLI's default 8 MB stack on 21 export parts (87 distinct modern roots,
  ELF/GEL/restricted-supply RTA results). The census re-ran them with a 4 GB stack. Minimal
  reproducers are the single roots `results.rta.ideal.gel.bounded_pi.total_workload_shorten_range`
  and `results.rta.ideal.elf.bounded_pi.bound_on_ep_workload`. The largest single proofs
  (`cumulative_task_interference_split`, 36 MB) export fine, so the culprit is a combination
  inside those closures and is not isolated.
* Per-declaration heartbeats depend on the request. In the 2,629-declaration modern probe, 18
  declarations hit the limit:
  * 5 were already translated in M6 runs;
  * 9 Prosa ones translate when run alone;
  * `JobReady` is blocked when run alone by `isFinite.axioms_`;
  * the 3 CoqEAL ones fail for real (kernel/universe) reasons when run alone.
* Preflight exceeds Python's recursion limit on one Classic declaration
  (`apa.bertogna_edf_example…schedulability_test_succeeds`).

No root was unquotable (sort-polymorphic) and no export failed.

## 7. Bounded diagnostic probes

`inventory/probe.py` assembles translate-only probes from the census store. Each probe takes every
in-scope root with no known blocker at the time it was built (before the probes), together with
that root's closure:

* modern: 1,462 roots, closure 2,629;
* Classic: 834 roots, closure 3,336.

The unchanged `rocq2lean translate` runs them under a memory limit. A direct failure in a probe is
only a candidate. `probe.py confirm` re-runs each candidate as its own root through the full CLI
(export with round trip, then translate) in `runs/inv-confirm-*`. Only those runs are evidence.

**Modern probe:** 2,075 translated and kernel-checked, 516 blocked by dependencies, 36 direct
failures.

* **6** are probe artifacts: the declarations were translated in current M6 runs (heartbeat or
  universe effects of the large probe request).
* **9** Prosa resource-limit failures translate when run alone (`util.list.*`,
  `supremum_spec`, `arrivals_at_sorted`, `TDMA_slot_order`).
* **`JobReady`** is blocked when run alone by the context-dependent `isFinite.axioms_` rejection.
* **Confirmed new blockers:**
  * `FP_policy`, `JLFP_policy`, `JLDP_policy` (universe entailment);
  * `concrete_job` (kernel);
  * MathComp `eqtype.Sub_spec`, `eqtype.insub_spec`;
  * `ssrfun.pair_of_and`, `ssrnat.nat_of_add_pos` (template `prod` at Prop);
  * CoqEAL `hrel.fun_hrel`, eight `param.*_R` lemmas, `refines_abstr2`, `refines_fst_R`,
    `refines_snd_R`.

  All of these are folded into section 6.

**Classic probe:** still translating when this report was written; no Classic probe result is counted. Results and confirmations will be added here.

## 8. What remains to migrate (Prosa v0.6 + Classic)

* **Whole targets:** 4,310 public declarations (2,440 P + 1,870 C) plus 116 projections, with
  their 10,539-declaration closure. 163 P declarations are VERIFIED today, 87 of them as roots.
  No C declaration has been translated yet.
* **Known blocked:** 2,509 of 4,692 in-scope declarations (P 1,357, C 1,152), through 14
  mechanisms. 9 are defined in MathComp/Corelib/CoqEAL. The Prosa/Classic-owned ones are:
  * the three priority-policy classes;
  * `concrete_job`;
  * the 4 `Admitted` Classic facts;
  * Classic's coinductive `Task_T`;
  * 11 SProp schemes.
* **No known blocker:** 2,183 declarations. Their closures are only partly attempted (the modern
  probe translated 2,075 of 2,629; the Classic probe is pending).
* **Unknown:** the declarations of the 3 unbuilt Classic files.

## 9. Recommended next tasks (`blockers.json` → `recommended_tasks`)

Each task's mechanisms have a dependency path from an in-scope root (checked by
`inventory/report.py`). "Cumulative" counts the roots whose remaining known blockers are all
covered by tasks 1..k.

| Task | Alone M / C | Cumulative M / C (protected) |
|---|---|---|
| **T1** universe solving on the Prosa closure: reference entailment (Prosa priority classes, `Sub_spec`, `big_morph`) and proof-local levels (`PCanHasChoice`, `big_const_seq`) | 567 / 43 | 567 / 43 (554) |
| **T2** recursion through `subn` (`edivn_rec`, `modn_rec`) | 109 / 257 | 697 / 309 (946) |
| **T3** default cast annotation in `eqtype.insub_spec` | 0 / 0 | 737 / 1,100 (1,758) |
| **T4** template `prod` at Prop (`leqif`, `pair_of_and`, `nat_of_add_pos`) | 55 / 0 | 980 / 1,100 (1,987) |
| **T5** correctness, interface protection and tooling: the context-dependent `isFinite.axioms_` / `nary_congruence` failures, kernel rejections (`concrete_job`, CoqEAL `fun_hrel`, `refines_abstr2`), protecting the Prosa interface from dependency specialization (`ArrivalCurvePrefix`), the stale preflight rule (`Acc_rect`), exporter stack and heartbeat limits | (correctness) | |

T3 unlocks nothing alone because `insub_spec` always co-occurs with the T1 failures. After T1–T2
it is the step that releases most of Classic. Not recommended now:

* coinduction (`normalization_done` is a setoid-rewriting marker; sole blocker of 23 roots);
* the CoqEAL course-of-values lemmas (4 sole roots);
* Classic's 4 source assumptions. They are `Admitted` in the ProsaBuddy source, so a faithful
  translation keeps them unproved and they cannot be VERIFIED without new source proofs.

## 10. Commands and logs

| Stage | Command | Output |
|---|---|---|
| scope | `inventory/scope.py` | `scope.lock.json` |
| build | `inventory/build.py` | `.work/inventory/build.json`, logs |
| enumerate | `inventory/enumerate.py` | `.work/inventory/modules.json` |
| export | `inventory/export.py modern\|classic` | chunked exports, `export-*/summary.json` |
| merge | `inventory/merge.py` | `.work/inventory/ir-*.ndjson`, `merge-*.json` |
| classify | `inventory/classify.py` | `declarations.jsonl`, `files.csv` |
| evidence | `inventory/evidence_blockers.py` | `.work/inventory/extra_blockers.json` |
| graph | `inventory/graph.py` | `dependencies.jsonl`, `.work/inventory/graph.json` |
| coverage | `inventory/coverage.py` | `coverage.jsonl` |
| report | `inventory/report.py` | `summary.json`, `blockers.json` |
| probes | `inventory/probe.py build\|translate\|confirm modern\|classic` | `runs/inv-probe-*` (direct_failures.json, confirmations.jsonl), `runs/inv-confirm-*` |

Translator code (`Rocq2Lean*.lean`, `tools/`, the exporter) is unchanged by this inventory:
the implementation tree digest is still `819383b9…`.

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
| Known blocker (preflight + current translation evidence): none / downstream / direct | 1,721 / 978 / 8 | 834 / 1,143 / 8 |
| Protected interface with no known blocker | 1,603 of 2,504 | 786 of 1,922 |
| VERIFIED as a root / as a dependency only | 87 / 76 | 0 / 0 |
| Kernel-checked in an unverified run / attempted, not translated | 11 / 19 | 0 / 0 |
| Never attempted | 2,514 | 1,985 |
| Public interface specialized (R2B-P/R2B-S) in a current run | 0 | 0 |

Evidence comes from the ten current-implementation runs (implementation tree `819383b9…`, the M6
completion). A run counts for a declaration only when the elaborated record is **byte-identical** to
the census record. All 11,359 run records that are also in the census are identical. Only 47
MathComp holdout records lie outside the Prosa closure. 172 external dependencies were translated
as statement specializations; **none** of them is a P or C declaration.

"No known blocker" is not a translation result. Most of those closures were never attempted, and
preflight is static. Section 7 adds bounded probes.

## 6. Blocker map (`blockers.json`)

Grouped by mechanism. Each group gives its defining declaration, a reproducer, the affected roots
(modern / Classic) and an in-scope dependency path. "Sole" means no other known mechanism blocks
the root.

| Mechanism | Category | Defining node | Affected roots M / C | Sole M / C | Example path |
|---|---|---|---|---|---|
| Proof-local universe level, strict native fact `Set < u` | universe | `mathcomp.boot.choice.PCanHasChoice` | 619 / 822 | 309 / 368 | IBF `arrives_after_beginning_of_busy_interval` → `exchange_big` → fintype `prod` instance → `PCanHasChoice` |
| Recursive call on a non-constructor-field term (recursion through `subn`) | missing rule | `mathcomp.boot.div.edivn_rec`, `modn_rec` | 180 / 536 | 157 / 257 | `hyperperiod` → `lcml` → `lcmn` → `divn` → `edivn` → `edivn_rec` |
| Proof-local universe level, native `le` fact | universe | `mathcomp.boot.bigop.big_const_seq` | 222 / 427 | 14 / 41 | `cumulative_job_interference_bound` → `sum_majorant_constant` → `sum1_size` → `big_const_seq` |
| Template `prod` at quality Prop | universe | `mathcomp.boot.ssrnat.leqif` | 405 / 0 | 111 / 0 | `service_in_implies_scheduled_in` → `sum_nat_eq0` → `leqif` |
| Reference argument not entailed by the universe graph | universe | `mathcomp.boot.bigop.big_morph` | 161 / 107 | 1 / 0 | `sum_majorant_constant` → `big_distrr` → `big_endo` → `big_morph` |
| Defaulted universe level not justified | universe | `mathcomp.boot.seq.mask_cat` | 162 / 32 | 4 / 0 | `eq_sum_leq_seq` → `mem_rem` → `subseqP` → `mask_cat` |
| Coinductive type | missing rule | `Corelib.Classes.Morphisms.normalization_done`; Classic `extraction_tdma.Task_T` | 219 / 13 | 16 / 8 | setoid-rewriting proofs → `normalization_done` |
| Genuine source assumption | source assumption | 4 `Admitted` facts in Classic `implementation/uni/basic/tdma_rta_example.v` (incl. the example's main theorem `ts_is_schedulable_by_tdma`) | 0 / 4 | 0 / 0 | direct |
| SProp eliminators (`_sind`) | universe | 11 generated schemes | 8 / 3 | 0 / 0 | direct, not protected |

**Co-blocking.** The two proof-local-level failures together block 151 more roots, and with `edivn`
112 more. 86 roots reach six mechanisms. The full list of combinations is in `blockers.json`.

**Not counted as blockers:**

* **Context-dependent failures.** `mathcomp.boot.fintype/isFinite.axioms_` (kernel rejection,
  "application type mismatch" in one run, VERIFIED in the gate) and
  `Corelib.ssr.ssreflect_rw.nary_congruence` (its R2B-P statement specialization rejected by Rocq in
  one run; translated in four) are recorded with the runs on both sides. Over 2,000 in-scope roots
  reach each of them.
* **Preflight contradicted by evidence.** Preflight rejects `Corelib.Init.Wf.Acc_rect` ("a type
  depends on an argument that recursive calls change"), but current runs translate it, including
  the VERIFIED gate. 754 modern and 268 Classic roots reach it. The pure preflight verdict still
  records this, because preflight's static rule predates M6's accessibility lowering.

**Resource limits (not semantic):**

* The exporter overflows the CLI's default 8 MB stack on 21 export parts (87 distinct modern roots,
  ELF/GEL/restricted-supply RTA results). The census re-ran them with a 4 GB stack. Minimal
  reproducers are the single roots `results.rta.ideal.gel.bounded_pi.total_workload_shorten_range`
  and `results.rta.ideal.elf.bounded_pi.bound_on_ep_workload`. The largest single proofs
  (`cumulative_task_interference_split`, 36 MB) export fine, so the culprit is a combination
  inside those closures and is not isolated.
* Preflight exceeds Python's recursion limit on one Classic declaration
  (`apa.bertogna_edf_example…schedulability_test_succeeds`).

No root was unquotable (sort-polymorphic) and no export failed.

## 7. Bounded diagnostic probes

`inventory/probe.py` assembles translate-only probes from the census store. Each probe takes every
in-scope root with no known blocker at the time it was built, together with that root's closure:
modern 1,462 roots (closure 2,629), Classic 834 roots (closure 3,336). The unchanged
`rocq2lean translate` runs them under a memory limit. Any direct failure a probe finds is only a
candidate. It becomes evidence only after `probe.py confirm` re-runs it as its own root through the
full CLI (export with round trip, then translate).

**Status at this report: both probes are still running** (`runs/inv-probe-modern`,
`runs/inv-probe-classic`; the translator writes its report only at the end). No probe result is
counted anywhere in this inventory. The "no known blocker" figures therefore rest on preflight and
the ten existing runs only. Probe results and confirmations will be added to this section and to
`blockers.json` when they finish.

## 8. What remains to migrate (Prosa v0.6 + Classic)

* **Whole targets:** 4,310 public declarations (2,440 P + 1,870 C) plus 116 projections, with
  their 10,539-declaration closure. 163 P declarations are VERIFIED today, 87 of them as roots.
  No C declaration has been attempted yet.
* **Known blocked:** 2,137 of 4,692 in-scope declarations (P 986, C 1,151), through 9 mechanisms
  defined in MathComp/Corelib (8) and Classic (assumptions, `Task_T`).
* **Unknown:** the declarations of the 3 unbuilt Classic files.

## 9. Recommended next tasks (`blockers.json` → `recommended_tasks`)

Each task's mechanisms have a dependency path from an in-scope root (checked by `inventory/report.py`).
"Unlocked" counts the roots whose remaining known blockers are all covered by the task.

1. **T1: proof-local universe levels in MathComp** (`PCanHasChoice`, `big_const_seq`). Unlocks
   330 P + 553 C roots (834 protected). Largest single gain.
2. **T2: recursion through `subn`** (`edivn_rec`, `modn_rec`: a recursive call on a non-field
   term). Unlocks 157 P + 257 C roots (408 protected).
3. **T3: template `prod` at Prop** (`leqif`). Unlocks 111 P roots.
4. **T4: correctness of context-dependent failures.** The kernel rejection of
   `fintype/isFinite.axioms_` and the `nary_congruence` R2B-P instance. Each is reached by more than
   2,000 roots, and either can fail a combined request once T1–T3 are done.
5. **T5: tooling limits on the Prosa closure.** Update preflight's stale rule for `Acc_rect`, the
   exporter's stack under the CLI, and preflight's recursion. These need no new translation rule
   but are needed to run Prosa-scale requests through the CLI.

Not recommended now: coinduction (`normalization_done` is a setoid-rewriting marker; sole blocker
of 24 roots) and Classic's 4 source assumptions (they are `Admitted` in the ProsaBuddy source. A
faithful translation keeps them unproved, so they cannot be VERIFIED without new source proofs).

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
| probes | `inventory/probe.py build\|translate\|confirm` | `runs/inv-probe-*`, `runs/inv-confirm-*` |

Translator code (`Rocq2Lean*.lean`, `tools/`, the exporter) is unchanged by this inventory:
the implementation tree digest is still `819383b9…`.

# Universe solver, stage A: constraint extraction (shadow mode) and phase profiling

Status: **in progress** (branch `solver-a`, from `e9885fe` = the S21 implementation). Plan:
`docs/UNIVERSE_SOLVER_PROPOSAL.md` §5, stage A. Diagnostics only: with neither environment variable set,
the translator's behaviour and every report are unchanged.

## 1. Phase profiling (`R2L_PHASES=<file>`)

One JSON line per declaration: its status, total time, number of attempts, and the time by phase summed
over all its attempts (`phase ↦ [ms, count]`; phases are inclusive of the phases nested in them):

| Phase | Where |
|---|---|
| `trans_type`, `trans_body` | `runTrans` of the source type and body (term construction, hypothesis registries) |
| `solve_levels` | `solveLevels` as a whole; nested: `check_type`, `check_value` (`Meta.check`), `defeq_type` (value type against declared type), `bounded_solver`, `keep_params` (R3G discovery, rebinding, parameters), `inst_levels` (`instantiateLevelMVars`) |
| `justify_residuals` | R3′ kernel justification of defaulted levels |
| `kernel` | `addOrReuse` of the declaration (kernel check) |
| `inductive_attempt` | one inductive attempt, whole |

The remainder of an attempt (R2B/R3 checks, generality, interface checks, JSON) is total minus phases.

## 2. Shadow-mode constraint records (`R2L_SHADOW=<file>`)

After a constant is final, the attempt that was accepted (or, if none was, the first attempt) is re-run with
the same structural flags (`fr`, `ad`, `de`, `wf`, `rv`, `p3`, `pl`, `ph`, `eq`, the extra own levels and the
same IR variant) but with every reference at a fresh, recorded level metavariable (the `unify` path of
`sharedOrFreshLevels`), and stopped after Lean's checker and the unification of the value's type with the
declared type (exactly the unification steps of `solveLevels`). Nothing is assigned, defaulted, solved by the
bounded solver or added to the environment; the state is restored; the attempt has its own heartbeat budget.

Record (`shadowDump`): the level sites of type and value *before* unification (sorts and universe arguments,
in traversal order, over metavariable ids), the own levels and the occurrences with their source levels, the
assignments unification made (fully instantiated), the constraints it postponed, the checker's diagnostics;
and, for an accepted row, the row's own level sites in the same order (`winner_type`, `winner_value`).

Levels are written compactly: `0`, `p:<param>`, `m:<id>`, `S(l)`, `M(a,b)`, `I(a,b)`.

## 3. Independent check (`tools/solver_check.py`)

Criterion (a) of stage A, from the records only (no translator code): the accepted row's levels determine
each metavariable occurring bare at a site; the assignments determine the others; then every assignment,
every postponed constraint and every site must hold as an identity of levels (normal form
`max(c, a₁+k₁, …)`, valid for every parameter value). Outcomes: OK / VIOLATED / GAP (skeleton mismatch,
undetermined metavariable, undecided `imax`) / NOT_ACCEPTED. Unit controls with forged records:
`tests/statement/test_solver_check.py`.

## 3b. Policy constraints (`tools/solver_policy.py`)

The first policy constraints over the same variables, checked against the reading the accepted row determines
(`solve_record`), from the records, the source's native facts and the report only:

* **R3 coherence**: an occurrence of a level the referring declaration has takes its own level (`u_l`, or the
  own level's value). Otherwise LOWER if the argument does not raise and the row reports a lowering
  (`universe_lowered`, R3↓), else EXCEPTION.
* **R3 no raising**: an occurrence of any other level `l` takes `max(c, u_m + k, …)` with `Set + c ≤ l` and
  `m + k ≤ l` entailed (the translator's `entails`, re-implemented). Otherwise LIFT if `l ≤ m` and the row is on
  the cumulativity tier (R3↑; LIFT_UNREPORTED if not), R8 if `l` is a motive level of an accepted constant and
  `m + k − 1 ≤ l`, else RAISING.

EXCEPTION, RAISING and LIFT_UNREPORTED are violations. Unit controls with forged records (11, including a raised
argument, an unrelated level, a shared level given another level, an unreported R3↑, R8 at a level that is not a
motive level): `tests/statement/test_solver_policy.py`.

Not yet extracted: rule R's equal-at-models readings as such (covered by the coherence test only where the
argument is the own level's value), rule H, R2B facts on proof-local levels, generality.

## 4. First results (690-declaration subset `prof-A`, 2026-10-17)

Subset: the closures of three `Num/Builders_8.HB_unnamed_factory_14` obligations, `Builders_74.HB_unnamed_factory_78`
and `FP.nonpreemptive_sched.sequential_ready_instance` (S21 source).

**Phases** (442 s, 1,757 attempts): term translation (`trans_type` + `trans_body`) 38% — redone at every attempt,
also when only levels differ; `keep_params` 20% (quadratic per level class: every argument re-read and the
interface re-walked for each class; an exact fix is measured separately); `check_value` 7%; kernel, unification
and the bounded solver ≈ 0%; ≈ 34% not yet attributed (R2B/R3/generality checks, …).

**Phases, finer** (checkpoint markers between solving and the kernel, and each attempt as a whole; 491.5 s, report
unchanged): attempts 99% (the ladder between attempts 0.7%); term translation 38%; `solve_levels` 28% (`keep_params`
19%, `check_value` 7%); **generality (binder independence, `freeLevelPin`) 20%**; R-CARRIER post-pass 6%; R3 checks
3%; everything else ≈ 1%.

**Full corpus (S21's attempt log, 10,972 declarations, 6.14 h).** First attempts 1.9 h, later attempts 4.2 h; tiers
with no success anywhere in the corpus 7,850 s (36%; the largest `c[p3,ph] eo1` 2,387 s / 96 attempts and
`c[ph] eo1` 716 s / 701 attempts); **200 declarations take 65% of the time, 128 of them fail after 25–30
attempts.** The cost is the exhaustive ladder of declarations that fail anyway: the solver's target.

**Exact speed fixes** (worktree `r2l-speed`, from `b46916c`; subset report identical row by row, 690/690):

| Change | Subset wall time |
|---|---|
| none | 7:16 |
| `keepParams`: arguments grouped once by class and by source level, values read only where needed (was quadratic) | 6:20 (−13%) |
| + generality check: name→level index once per check instead of linear scans of all source levels per occurrence and parameter; clean subterms memoised; binder domains computed lazily | 5:26 (−25%) |

**Repeated attempts** (worktree `r2l-memo`, diagnostics `R2L_ATTEMPTS`: per attempt a key made of the translated
term with fresh metavariables renumbered by first occurrence, plus every flag read after translation). Subset: no
attempt repeats an earlier one except 15 (12% of the time). Those are the R-CARRIER no-split tier's variants
(`c[p3,ph] eo1`, `c[ph] eo1`, …), which re-run earlier attempts with the carrier split off. That changes nothing
when the split never applied: `carrierSplit` is read at one point only (`tyClasses.size ≥ 2`, not under R2F-c).
420 more attempts (20%) translate to an earlier term but differ in a solving flag (`it`, `cu`, `lo`, …), so their
result can differ.

Full S21 (tier labels; on the subset, same-label repeats are same-key repeats by time, 36.0 of 36.5 s):

| Repeat of an earlier attempt with the same label | Attempts | Time |
|---|---|---|
| aborted by the late-tier budget; the earlier one completed (failed) | 99 | 2,481 s |
| completed failure | 530 | 468 s |
| other (earlier aborted, or accepted: same label, different input) | 29 | 262 s |

* **Exact skip** (worktree `r2l-speed2`): with the split off, an attempt whose inputs (decl variant by pointer, tier
  flags, extra own levels) equal an earlier completed failure of the declaration in which the split did not apply
  returns that failure's status, message and diagnostics, and charges its heartbeats. Only when the earlier
  attempt used at most 90% of this attempt's budget (repeats measured at 1.000–1.002× the heartbeats). Checked
  three ways: a verification mode that runs the repeat anyway and compares (subset: 2/2 same); memo on vs off with
  the same binary (690/690 rows equal modulo metavariable numbers in one message); and the frontier subset
  with the synthesized abort below as well. That run was stopped by the memory watchdog at 2,004 of 2,139
  declarations; on those 2,004, 0 status differences from the S21 implementation and 17% less time (exact speed
  fixes, skip and synthesized abort together; the shares are not separated yet). Gain ≤ 468 s on S21 (2%): the expensive repeats are the aborted ones.
* **Synthesized abort** (experiment only, `R2L_SYNTH_ABORT`, not adopted): a repeat whose earlier run used more than
  110% of the late-tier budget is not run and reported as `RESOURCE_LIMIT` with a fixed message. No gate reads a
  timeout message (the gates look for "not entailed", "(some 0)", "argument is 0", "defaulted universe level(s)",
  "application type mismatch" with ` h_`), so accepted rows and statuses are unchanged by construction. Only the
  `[last tier: …]` text of the affected failing rows changes. Up to 2,481 s on S21 (11%); needs approval as a
  report-text change.
* **Determinism fix** found on the way: residual parameters were numbered through `Level.collectMVars`, a set ordered
  by metavariable *name*. Two residuals in one level swapped numbers when unrelated work shifted the name counter
  (`JobTask`'s `universe_residuals`). Now numbered left to right. Only the residuals' names change.

**Constraint records** (608 constants; inductives not recorded):

| | records |
|---|---|
| OK (the accepted row satisfies every extracted constraint) | 582 |
| VIOLATED | **0** |
| GAP: P3 hypothesis sharing depends on the level choice | 19 |
| GAP: a metavariable occurring only under `max` | 2 |
| not accepted (system recorded, nothing to check) | 5 |

**Policy constraints** on the 582 OK records: **all satisfied**. 694 shared occurrences: 690 coherent and 4 LOWER
(one protected row, `FP.nonpreemptive_sched.Job`: a proof-local level placed at `0`, with `universe_lowered`).
129,822 other occurrences: 129,820 do not raise, 1 LIFT (`isNumRing.phant_axioms`, tier `c[cu,lo,ph]`) and 1 R8
(`seq.eqseqP`, argument `u_eqtype_51 + 1` for `list_rect`'s motive level `Datatypes.192`). 2 s for the subset.

* P3 creates one prerequisite hypothesis per distinct instance *type*. With fresh levels at every reference,
  instances that the accepted attempt unified are distinct, so the shadow term has more hypothesis binders:
  for P3 rows the term structure is not independent of the level choice (stage B must treat hypothesis
  sharing as part of the choice, or extract per candidate structure).
* **Inertness.** Lean's `restore` keeps the name generator and the core caches. The translator orders some
  levels by metavariable name (e.g. the numbering of `u_residual_i`), and heartbeats count allocations, so a
  shadow attempt changed later rows until the whole core state was restored too (2 rows differed, then 2 messages:
  a budgeted attempt timing out at another point, shifting later metavariable names).


## 5. The GEL/ELF frontier after Stage 6, and the conflicts typing forces

From S21's attempt log (complete although the run was killed) and the source dependency graph: the GEL/ELF
frontier is **16 declarations** (23 at S17), all `UNIVERSE_REJECTED`: 7 `Order/Builders_62.factory_64` obligations
(binder levels forced), 6 `ssrint` (a level free in the source fixed to 1 by `int : Set` packed in an HB
structure), and `GRing/Builders_406.factory_411` obligation 109, `Num/Builders_67.factory_69`,
`Algebra/Builders_74.factory_78` (raising, or a proof-local level solved above a fact).

`tools/solver_locate.py` groups, from the shadow record (fresh levels at every reference), the own levels and
reference arguments that unification puts in one class, and reports classes joining source levels that the source
only orders (`≤`/`≥`) or does not relate at all. Every frontier member has such a class: an *unrelated* join is
cumulativity to a common upper level (`A : Type@{a}`, `B : Type@{b}` both used at `Type@{c}`). Observed so far:
the `comMixin` obligations join `choice.299` with `eqtype.32` (structure carriers of `int`); the `order`
obligations join an own level with the sort arguments of an `id_phant` *statement* (the Q-b shape, not adopted);
the builders join many `nmodule` carrier levels.

Per occurrence (rerun `front-sh2`, 63 min on 2,139 declarations; each occurrence records its constant and its
side, type or value; `solver_locate.py … REPORT` prints the classes of the levels a rejection message names):

| Members | Forced join | Position |
|---|---|---|
| 6 `ssrint` | `int : Set` at an HB mixin's carrier `Type@{choice.299/333}`, the level free in the source | the statement (type) |
| 7 `order` | the obligation's own binder levels `order.15913`, `order.15972` (and `order.16020` with `HB.structures.27/28/32` at `id_phant` statements) | the statement (type) |
| 3 of the 7 (first tier) | `preorder.119 := max(…, 116__c0, …)` against the fact on `116__c1` | value; R-CARRIER copy choice |
| 2 builders | Lean's `max` level above the source's at the own prerequisite `obligation_1.statement` | reference to a generated `.statement` |
| `factory_411` o.109 | proof-local `11469` identified with `nmodule.1457/2404/625` via prerequisite `.statement`s | type and value |

21% of the occurrences are not attributed to a constant (levels not created at a reference). Consequence for rule
U: none of the 16 has a local cumulativity position (`docs/ULIFT_PROPOSAL.md` §9). For the solver: `ssrint` is a
generality decision (a free level fixed at a reference), `order` a coupling typing forces in the interface, and
the builders couplings at generated prerequisite statements.

## 6. Side experiment H⁺ (measured, rejected)

Two frontier members failed only on raising at a reference to their own prerequisite's `.statement`. H⁺ let such a
reference take any levels of the referring declaration (translator and audit copy, `R2L_EXP_HPLUS`, off by
default). Frontier subset (2,139 declarations, consumer and audit OK): **0 frontier declarations unblocked**
(the two move to their next blocker, coherence at an `axioms_` reference), **5 claimed rows lost**, 7 claimed rows
changed. Cause: relaxed on every tier, the check let dependencies be accepted on an earlier tier with a different
level structure, and their dependents then failed. Lesson for rule U and the solver: a new rule only as the last
tier, after every existing one failed.

## 7. Still to do in stage A

* The remaining policy constraints (rule R's readings in general, rule H, copy positions, R2B facts on
  proof-local levels, generality), and their independent check (§3b has coherence and no raising).
* Criterion (b), the converse: assignments satisfying the extracted system, other than the accepted one,
  kernel-checked (extraction gaps).
* Agreement rate on a corpus run; inductives (not recorded yet); the GEL frontier from S21.

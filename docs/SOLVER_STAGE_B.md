# Universe solver, stage B: the reference solver and its first uses

Status: **in progress** (plan: `docs/UNIVERSE_SOLVER_PROPOSAL.md` §5, stage B). One translator change came
out of it and is merged (the least-solution rule, §6; full corpus S22, §8); everything else here is diagnostics
and experiments behind variables (stage A's `R2L_SHADOW`, `R2L_WITNESS`, `R2L_RETRY_ABORTED`).

## 1. What the solver decides

A *group* is the set of universe-only variants of one term: tier attempts of a declaration with the same kind,
the same term-changing flags (`fr`, `ad`, `de`, `wf`, `rv`, `p3`, `pl`, `ph`, `eq`) and the same extra own levels,
differing only in `it`, `cu`, `lo`, `un`, `jo`. The stage-A shadow record of a group (fresh level metavariable at
every reference, stopped after Lean's checker and unification) is its most general term: the other variants
share own levels at references from the start, a specialization of it.

`tools/solver_search.py` decides whether some level assignment satisfies the record's system under the policy
of the group, or certifies that none does. The encoding **over-approximates** what any variant of the group can
accept, so that UNSAT is sound for skipping the group:

| Constraint | Encoding | Allowances (union over the group) |
|---|---|---|
| typing | assignments and postponed constraints of the record, as identities of levels | — |
| own levels | a free own level is its parameter `u_l`, its minimal model (R2B), or another own level's parameter (identified by solving) | `it`: also its R2F reading |
| R3 coherence | an occurrence of an own level takes the own level's value; rule R (equal at every model) | `lo` (R3↓): any non-raising value |
| R3 no raising | `max(c, u_m + k)` with `Set + c ≤ l`, `m + k ≤ l` entailed | `cu` (R3↑): `u_m` with `l ≤ m`; R8 `u_m + 1` at a motive level of the referenced constant |
| implicit levels (R3G) | a class unification left free is a new parameter for one of the levels it occurs bare at, or a residual `0` | — |
| R2S/R2B | every native fact among the own levels holds for their values | `cu`: `Set < m` as `Set ≤ m` (R2B-P) |

Not encoded, each only removing acceptances (so UNSAT stays sound): generality and interface checks, the kernel,
R3′ justification, R-CARRIER copy bookkeeping beyond the copies' source level. Search: backtracking over the
candidates, each constraint checked when its last unknown is assigned; every reported witness is re-checked
against every constraint.

## 2. Soundness on the accepted subset

`prof-A` (690 declarations, shadow records of the accepted attempts): **603 accepted records, all SAT** under
their group's allowances; 0 accepted records UNSAT. Two encoding errors were found by this test and fixed
before the numbers above: (1) own type levels identified with another own level by the solving step
(`ssrbool.rel`: `1171 := u_1105`); (2) an occurrence of an own level whose value is the own parameter inside the
own level's R2F reading (`JobType`: `58 := max(u_32, u_51 + 1, u_55, u_58)`); and R8 had first been allowed at every
level (it holds only at the referenced constant's motive levels, `admitting_levels`).

## 3. First results on the failing frontier

The 127 unprotected universe rejections of S21 (`uni-sh2`): SAT 121, UNSAT 3 (`refines_apply`, …), UNKNOWN 3
(foreign parameters of polymorphic constants). Most failing first groups are therefore *not* refuted by the
encoding: what refuses them is outside it (generality, kernel), or a variant that the solver says can succeed did
not finish. Example, the `numdomain` HB obligations (93 rows, "proof-local level 3686 solved as u_3387"):

| Group of obligation 124 | Variants (S21b) | Outcome |
|---|---|---|
| `p3,ph`, eo1 | strict | coherence at `order.149` (argument `u_3686`) |
| | `lo` | **RESOURCE_LIMIT** (late-tier budget, 21.9 s) |
| `ph`, eo1 | strict | raising `u_3686 + 1 ≤ divalg.3106` at the generated `obligation_83.statement` |
| plain, eo9 | 8 universe variants | R2B: `3686 := u_3387`, fact `3686 ≤ divalg.3442` (3387 is a rigid own level here) |

The solver finds a witness for `p3,ph` with R3↓ (`3686 := u_3686`, lowered argument at `order.149`), the variant
whose attempt ran out of budget.

**Budget, not policy, for the solver's SAT groups.** Obligation 142 of the same family (`factory_14`), alone
(246-declaration closure from S21b), with every late tier given 10× the full budget (diagnostics,
`R2L_BUDGET_X`): the variant the solver picks, `c[lo,p3,ph] eo1`, is **accepted** (14.7 s; under the late-tier
budget, a fifth of the full one, it was aborted at 9 s). Consumer OK and audit OK on the closure (244 accepted
declarations match, no axioms). Over the 127 records: 97 SAT records have their predicted variant aborted by the
late-tier budget in S21b, 24 SAT records completed every variant and failed (refused by what the encoding leaves
out), 3 UNSAT, 3 UNKNOWN. Over S21b's 238 direct failures, 115 have a budget-aborted attempt (98 of them in
`numeric_hierarchy`).

This gives a stage B tier that changes no acceptance policy: after the ladder fails, the attempt the solver
predicts satisfiable, if the late-tier budget aborted it, is re-run with the full budget. It runs only after every
existing tier failed, so only rows that failed before can change. Experiment (`R2L_RETRY_ABORTED=all` re-runs every
aborted attempt; a file of `(declaration, tier)` pairs restricts it to the solver's predictions): §6.

## 4. Speed bound

S21b: 24,804 s of attempts; **12,181 s (49%)** are universe-only variants (after the first) of groups in which no
variant succeeds (9,202 s on declarations that fail, 2,979 s on declarations accepted in another group). Skipping
on a sound UNSAT is exact for every accepted row if no skipped attempt is the one a `lastTier` gate or the final
row reads (the gates read it after two tier loops and at the end; any later attempt overwrites it).

## 5. Translator support (experiment, worktrees `r2l-solver`, `r2l-solverb`)

* `R2L_WITNESS=<file>` (one witness per line, `tools/solver_search.py … OUT.json` writes `OUT.witness.jsonl`):
  for a declaration the ladder does not accept, its first attempt is re-run on the `unify` path with the witness's
  allowances and implicit levels (extra own levels); after unification the witness assigns each occurrence (in
  creation order) and own level (`applyWitness`), then coherence by unification, R3G and every check run as
  usual. A witness value that disagrees with unification is reported (`solver witness: …`).
* `R2L_RETRY_ABORTED=all|<file>`: the late-tier attempts the budget aborted are kept re-runnable; after the ladder
  fails they are re-run with the full budget (all, or the listed `(declaration, tier label)` pairs).
* Extraction cost (`prof-A`, without `R2L_SHADOW_INST`): a shadow attempt costs about half a first attempt
  (45 s vs 92 s over 608 groups), against 158 s of later variants in the same groups.

**Witness attempts, first trials (`prof-A`'s 4 failing declarations).** Three corrections came out of them:
(1) a statement's attempt is named after its `.statement` constant, witnesses by the source name; (2) an occurs
check on the *instantiated* witness value (an own level already solved as `max(…, ?occ)` closed a cycle: stack
overflow on `sequential_ready_instance`); (3) a free own level the witness keeps as itself is given its parameter
at once, or R3G renames the class of occurrences set to it (`order.149` became an implicit level). After these,
both witnesses are refused by checks the encoding does not model yet:

* `sequential_ready_instance`: R2B, `eqtype.51 := 0` against the fact `fintype.101 ≤ eqtype.51`, where
  `fintype.101` is an *implicit* level of the witness (the encoding checks facts among the record's own levels only);
* obligation 142: generality, "the level of `u_order.149` is free in the source (no applied argument
  determines it) but its argument is `u_3686`". The translator's own acceptance of 142 (full budget) uses
  R-CARRIER copies throughout (`HB.structures.23__c0` … `__c33` as implicit levels) and R3↓.

Encoding the generality obligation, facts with implicit levels and the carrier copies would make the reference
solver a second implementation of most of the translator's policy. For the families measured here it is not needed:
the full-budget retry lets the existing tiers and checks decide, and the solver only chooses which aborted
attempt to retry. Witness attempts stay an experiment (kept behind `R2L_WITNESS`).

## 6. A dependency's level choice blocks its dependents: `Job` (branch `solver-b`, from `main` = Stage 6)

Ranking S21b's blocked protected roots by the failures in their frontier: 48 roots wait on a single failing
declaration each; the four `*_ready_instance` declarations (EDF/FP, preemptive/non-preemptive) alone block 18.
None is a local problem:

* `basic_ready_instance` (EDF): kernel, `JobReady` applied to `Job` — the argument has type
  `Equality.type.{u_32, max(u_51, u_21), u_55, 0}`, the binder `JobType.{a,b,c,d} := Equality.type.{a, b, c,
  max(a, b+1, c, d)}` (JobType's R2F reading). No instance of `JobReady` equals `0` there.
* `Job` (`Definition Job := concrete_job : eqType`; protected) was accepted on the R3↓ tier with its body level
  `eqtype.58` lowered to `0`. The `un` tier had found the right shape, `58 = max(…, 58)` through one of 58's own
  occurrences, but `rebindShared` names such an occurrence by the level's parameter `u_58`, and a body level has
  none ("mentions u_58, which is not a parameter of the declaration").
* `sequential_ready_instance` (FP): "`eqtype.58` solved as 0, native fact `Set < 58`" — the same `Job`.

**Change (experiment, 9 lines):** a body level solved through its own occurrence, `l = max(A, l)`, is solved by its
least solution `A` (as a free body level takes its minimal model, R2B); type levels keep their parameter.
`Job`'s 58 becomes `max(u_32, u_51 + 1, u_55, u_21 + 1)`, JobType's reading.

Closure of the 18 roots (397 declarations, 35 s): the 4 `*_ready_instance` accepted; both `Job`s accepted on
the `un` tier, no longer lowered; **4 protected roots newly claimed** (the `sched` definitions); the other 14
roots move from Blocked to Direct Failure (next blockers: raising at the generated
`eqn_task_arrivals_bound` obligation statement, whose R-CARRIER copy of level 21 meets `task_arrivals_bound`
at `max(u_51, u_21)`, the level `JobArrival` solved `task.43` at; and a copy-selection R2B fact); 7 accepted rows
change, all to more general ones (`Job` ×4, `Task` ×2, `JobTask`: no lowering); consumer OK, audit OK.
Changing accepted (protected) rows needs the full corpus and review: queued as S22.

## 7. Where the remaining protected roots stand (after §6, non-GEL subset)

126 failing protected roots outside the GEL/HB group (1,887 declarations): with §6, 25 newly claimed, 0 claimed
rows lost; 157 claimed rows change, every one only in universe levels (term structure identical, no new `0`
level; 10 no longer lowered). The 26 protected direct failures left are mostly one shape, a carrier packed in a
structure's carrier slot (`Equality.type`, `Choice.type`): Rocq packs `T : Type@{t}` into `Type@{c}` by
cumulativity; Lean identifies `c` with `t`. It shows as raising at the generated `eqn_task_arrivals_bound`
obligation statement (10: `JobArrival` solved the carrier slot `task.43 := max(u_51, u_21)`), coherence at
`Equality.sort` (4), levels forced to `0` by lowered dependencies (5), and in the GEL frontier as `ssrint`'s
statement specializations. A deferred R2F-reading check (the cycle check after defaults) moved `JobTask`'s
`it,un` attempt to the same blocker and changed no row; reverted. Draft policy proposal for the pin at a carrier:
`docs/CARRIER_PIN_PROPOSAL.md` (experiment `R2L_EXP_NO_PIN`, upper bound).

## 8. S22: the least-solution rule on the full corpus (`5a42d9c`, run `r2l-run-S22`)

| Run | Accepted | Audited Pending | Blocked | Direct Failure | Unclaimed |
|---|---|---|---|---|---|
| S21b (Stage 6) | 685 | 3,585 | 180 | 24 | 204 |
| **S22** | **685** | **3,610** | **153** | **26** | **179** |

* Protected moves: Blocked → Audited Pending 13, Direct Failure → Audited Pending 12, Blocked → Direct Failure
  14 (the refinements now reach `eqn_task_arrivals_bound`'s carrier coupling, §7). 0 claimed rows lost.
* 179 claimed rows changed: 177 only in universe levels (no new `0` level); 2 (`job_generation_valid_jobs`,
  `job_generation_valid_number`) on another tier, more general (one more parameter, no δ-inlining; R-CARRIER
  copies with per-instance prerequisites), still audited.
* Consumer OK, audit OK (0 problems), source instances OK, `CORPUS_PROVENANCE_BOUND`, conversion dependence
  886 `CONV_OK`; one newly attempted row (S21b: blocked) fails the kernel,
  `refine_total_hep_rbf'` obligation 5. 7,543 proof tasks.
* Frozen-worktree suites at `d24b0fb`: the 18 statement suites and `test-all` 18/18.

## 9. Still to do

* Retry experiment on the 2,631-declaration subset of the 127 rejections: newly accepted rows, audit, time.
* Extraction cost per group (a shadow attempt per group), against the variants it can skip.
* Port of the solver to Lean behind a flag; the Python solver stays as the independent checker of witnesses and
  certificates.
* The carrier coupling (§7): the referrers of `Job` identify the occurrences of `eqtype.51` and
  `extrapolated_arrival_curve.21` through the packed carriers `max(51, 21) = max(51, 21)`; stage C.

# Statement-only translator: iteration log

Append-only. One entry per completed change (or commit). Every entry measures the same fixed corpus —
the 4,474 protected Prosa v0.6 + Classic declarations (`reports/prosa_inventory/protected_interface.json`)
— with the same criteria (`inventory/coverage_delta.py`):

* **Accepted** — `TRANSLATED_AND_CHECKED` / `STATEMENT_KERNEL_CHECKED` / `BOOTSTRAP_RESOLVED`, audit MATCH;
* **Audited Pending** — `PENDING_KERNEL_CHECKED` / `STATEMENT_PENDING_KERNEL_CHECKED`, audit MATCH
  (kernel-checked with unproved prerequisites as hypotheses; not a final public declaration);
* **Blocked Dependency** — `BLOCKED_DEPENDENCY` / `OBLIGATIONS_PENDING`;
* **Direct Failure** — any other status of the declaration itself, or a claimed row the audit does not
  MATCH.

An "Accepted" proposition definition is a translated *statement*, not a proved theorem. Where the full
corpus was not re-run, the entry says "not measured". Snapshots: `reports/statement_only/coverage/`.

---

## Entry 0 — baseline (commit `7d91605`, 2026-10-11)

Statement-only report as reviewed (`STATEMENT_ONLY_REPORT.md`). Re-measured on 2026-10-13 from the
existing corpus run `runs/st-corpus` with the criteria above
(`python3 -I inventory/coverage_delta.py snapshot runs/st-corpus reports/statement_only/coverage/baseline-7d91605.json`):

| | Accepted | Audited Pending | Blocked Dependency | Direct Failure |
|---|---|---|---|---|
| modern (2,504) | 344 | 1,002 | 1,140 | 18 |
| Classic (1,970) | 225 | 1,012 | 725 | 8 |
| **total (4,474)** | **569** | **2,014** | **1,865** | **26** |

Consumer OK, audit OK (3,990 claimed rows MATCH). Matches the reported figures exactly.

Blocked protected declarations by root cause (measured from `blocked_by` chains; "only" = blocked by
this family alone): `edivn_rec`/`modn_rec` 732 (only 411; Classic 333 of those), `JLFP`/`FP`/`JLDP`
universes 604 (only 373, all modern), protected-interface narrowing refused 547 (only 225), ideal
`processor_state` obligations 280 (only 184), MathComp `nmodule` HB and other universe/kernel failures
the rest.

---

## Entry 1 — Task A: pending-to-final assembly, proof-check integration, corpus provenance (2026-10-13)

Commit: **not committed** — working tree on top of `7d91605` (changed files listed below); to be
committed on approval.

### (1) What was added and why

* **Assembly** (`docs/ASSEMBLY.md`): `rocq2lean assemble` turns pending artifacts into accepted
  `Rocq.*` declarations once their prerequisites have verified proofs, and gives each proved task its
  final theorem `Rocq.<leaf>` — only where the kernel accepts the submitted template instantiated at the
  final, audited statement. Mechanism: the translator re-runs in *assembly mode* over the same IR,
  importing the validated library; validated rows must be reproduced identically (`addOrReuse`), never
  re-added. A re-emitted pending inductive is a new type: a template about `RocqPending.I h` is not
  reused for `Rocq.I` (`ASSEMBLY_TRANSPORT_REQUIRED`), nothing is cast. Opaque-data values are never
  accepted from submissions (`OPAQUE_BINDING_PENDING` until A′). Assembled declarations report the
  axioms their proof fields bring (`axioms_by_target`); computation inspecting an assembled proof is
  reported (`proof_dependent_computation`).
* **Task interface**: templates are `RocqProofTemplates.T<task_id>.proof` (modules confined to their
  namespace); `Rocq.<name>` reserved for assembly; each task records its generalization form (none /
  over proofs / over data) — the claim that every task is independently provable is withdrawn for data
  prerequisites; opaque-value tasks accept no submission.
* **Consumer and audit**: assembly modes with separate policies for validated rows, assembled rows,
  final theorems, carried-over pending artifacts; maximality check.
* **Corpus provenance** (`reports/statement_only/PROVENANCE.md`): per-chunk snapshots, per-chunk Rocq
  round trips, a global universe-consistency check of the merged facts in one common environment, and a
  corpus manifest with a checker. A bulk `Rocq2Lean CheckRelations` plugin command was added (the
  per-pair command rebuilt the graph's name table every call: 2–4 h per large chunk).
* **Invalidation**: `export`/`translate`/`validate` now also invalidate `PROOF_TASKS.jsonl` and
  `assembly/`; submissions are kept and become stale (refused by `assemble`).
* **Documentation**: README, SCOPE (direction; the Classic patch *is* applied), TRUST (statement-only
  claim), ACCEPTANCE_INVARIANTS, STATEMENT_ONLY_DESIGN (pending artifacts share `Rocq2LeanOut` in a
  separate namespace; template naming; generalization), VALIDATION_REPORT addendum; new ASSEMBLY,
  PROVENANCE, A_PRIME_HANDOFF.

### (2) Coverage before → after (full corpus re-run: `runs/st-corpus-A`)

| | Accepted | Audited Pending | Blocked Dependency | Direct Failure |
|---|---|---|---|---|
| before (Entry 0) | 569 | 2,014 | 1,865 | 26 |
| after | 569 | 2,014 | 1,865 | 26 |
| delta | 0 | 0 | 0 | 0 |

Movements between categories: none. All 9,970 result rows are identical to the baseline in status,
target, kind, type, value, constructors, universe parameters and hypotheses (row-by-row comparison).
Consumer OK; audit OK (3,990 claimed rows MATCH). This change adds no coverage by design: it is
assembly and validation infrastructure; no corpus proof exists, so nothing is assembled.

Zero-proof corpus assembly (`runs/st-corpus-A/assembly-dry/`): 1,668 validated rows reproduced
identically (0 `REUSE_MISMATCH`), 2,322 pending rows carried over (2,280 `OPAQUE_BINDING_PENDING`, 42
waiting for proofs), 0 assembled; assembly consumer OK, assembly audit OK.

### (3) Newly unblocked

None (not expected). Measured for A′: 1,653 pending rows (1,520 protected) need *only* opaque-data
values; 26 opaque constants gate pending rows, led by `eqnP` (1,923 protected).

### (4) Remaining blockers and estimated impact

Unchanged from Entry 0 (upper bounds on protected declarations held only by each family):
`edivn_rec`/`modn_rec` 411 (B); `JLFP`/`FP`/`JLDP` universes 373 (C); narrowing refused 225 (no
approved representation change); ideal `processor_state` 184 (C family); other universe/kernel ~130.
New explicit assembly boundaries: opaque-data binding (2,280 pending rows; A′); re-emitted pending
inductives need transport or a final-statement proof (5 pending inductives in the corpus).

### (5) Regressions

None in the corpus (0 previously accepted declarations changed; 0 rows changed at all). Test suites on
the final tree: `test-all` 18/18 (361 checks), `test-statement` 29/29, `test-assembly` 32/32. One
intermediate `test-all` run failed `test-m5` because implementation files were edited while that suite
was between export and verify (the integrity gate correctly reported "implementation changed since
export"); the run on the frozen tree passes.

### (6) Commands and evidence

```
python3 -I inventory/coverage_delta.py snapshot runs/st-corpus reports/statement_only/coverage/baseline-7d91605.json
cp runs/st-corpus/{source.ndjson,merge.json} runs/st-corpus-A/
STATEMENT_RUN=runs/st-corpus-A python3 -I inventory/statement_run.py translate   # ROOTS_NOT_TRANSLATED (1,891), as baseline
STATEMENT_RUN=runs/st-corpus-A python3 -I inventory/statement_run.py check       # consumer OK, audit OK
python3 -I inventory/coverage_delta.py snapshot runs/st-corpus-A reports/statement_only/coverage/A-assembly.json
python3 -I inventory/coverage_delta.py compare reports/statement_only/coverage/{baseline-7d91605,A-assembly}.json
STATEMENT_RUN=runs/st-corpus-A python3 -I inventory/statement_run.py assemble-dry
scripts/test-statement; scripts/test-assembly; scripts/test-all
python3 -I inventory/statement_provenance.py snapshot
python3 -I inventory/statement_provenance.py roundtrip --jobs 3
python3 -I inventory/statement_provenance.py union runs/st-corpus-A --jobs 2
python3 -I inventory/statement_provenance.py manifest runs/st-corpus-A
scripts/test-provenance
```

Evidence: `reports/statement_only/coverage/{baseline-7d91605,A-assembly}.json`,
`reports/statement_only/test_{statement,assembly,provenance}.json`, `reports/test_all.json`,
`reports/statement_only/provenance/CORPUS_MANIFEST.json`, `.work/provenance/`,
`runs/st-corpus-A/` (local, git-ignored).

---

## Entry 2 — Task B: termination lowering with explicit obligations and unfolding equations (2026-10-14)

Commit: `220a8c2` (branch `task-b`, on top of `803d733`).

### (1) What was added and why

Recursion that the structural (M3c) and course-of-values (M6) lowerings cannot express — a recursive
call on a subterm that Rocq's guard sees only by reducing a function (`edivn_rec`/`modn_rec`: `if m - d
is m'.+1 then loop m' …`) — is lowered (statement mode only) to `Acc.rec` over its call relation, with
convoy matches recording why each call decreases. Well-foundedness is **not constructed**: it is a
generated termination-obligation leaf (`<c>__rocq2lean_termination_<k>`, an accepted statement and a
proof task); the definition and everything that needs it are pending on it. A generated unfolding
equation (`<c>__rocq2lean_unfold_1`) states Rocq's definitional unfolding propositionally (a proof task
over the obligation). Audit: independent re-derivation of the lowering (carrier, call-relation shape,
convoy, motive, minor premise), of the termination statement's shape and use, and of the unfolding
equation from the source. Conversion dependence: `Rocq2Lean CheckConversionDeps` (Rocq re-checks a
dependent's statement preparation with the lowered bodies removed). Details: `docs/TERMINATION.md`.

### (2) Coverage before → after

**Not yet measured.** The full corpus re-run (`runs/st-corpus-B`) was started and stopped by Claude
Code under memory pressure (while 8 Rocq round-trip processes and an unrelated campaign ran); it was
not restarted without the user's go-ahead. Expected (upper bounds, not measurements): at most 732
protected declarations blocked by `edivn_rec`/`modn_rec` can move, at most 411 only by them, and only
from Blocked Dependency to Audited Pending (the obligations are unproved), never to Accepted.

### (3) Newly unblocked

Fixture only (measured): `edivr`, `modr`, `divr`, `T3` and the statements `divr_le`, `divr_7_2`
move from blocked to audited pending; after assembly with synthetic test proofs they are accepted.

### (4) Remaining blockers

A dependent needing the definitional unfolding of a lowered recursion is a reported blocker
(fixture: `t3 : T3 := 0`, confirmed by Rocq's `CONV_NEEDS`); corpus count not yet measured. Opaque
data (A′), policy universes (C), narrowing — unchanged.

### (5) Regressions

Fixture suites on the frozen tree: `test-statement` 29/29, `test-assembly` 32/32, `test-termination`
22/22 (new). (An earlier run of the first two failed because the exporter plugin was rebuilt while they
ran; the integrity gate reported stale artifacts — not a translator regression; rerun on the frozen
tree passes.) `test-all` 18/18 on `220a8c2` (frozen worktree, proof-mode suites unchanged). Corpus
regressions: not yet measured.

### (6) Commands and evidence

```
scripts/test-termination; scripts/test-statement; scripts/test-assembly
python3 -I inventory/conversion_deps.py runs/st-corpus-B --jobs 2      # (corpus: pending)
```
Evidence: `reports/statement_only/test_termination.json`, `docs/TERMINATION.md`.

---

## Entry 3 — Task C-1: R3G for statements; no statement specialized by a defaulted level (2026-10-14)

Commit: `5dcee42` (branch `task-c`, on top of `220a8c2`).

### (1) What was fixed and why

Finding (measured on the baseline run `runs/st-corpus-A`): **1,381 statement rows** — 701 of them
*protected* Prosa statements — were accepted or audited pending with universe levels **defaulted to
0**: R3G (implicit reference levels become parameters) read only the declared type of a statement row,
which is `Prop`, never the statement itself (the row's value). Those statements are specialized
(e.g. quantified over `Set`-level job types only), contrary to the design ("a statement is never
specialized by defaulting a level"), and neither the translator nor the audit refused them. The same
defect specialized MathComp's `opt_eqP` and hence `option`'s canonical `eqType`, which blocked
Prosa's ideal `processor_state` family (generic jobs).

Rule: R3G reads a statement row's statement; a statement level still free is **refused**, never
defaulted (translator); a statement row with defaulted levels is **rejected** (audit, independent).
`JLFP`/`FP`/`JLDP_policy` are diagnosed as a policy blocker (`docs/UNIVERSE_FAMILY_C.md`): not applied.

### (2)–(5) Coverage, unblocked, blockers, regressions

**Corpus not yet measured** (same reason as entry 2). Probe `fixtures/stmt/c` (measured):
`opt_eqP` generic in `eqtype.51/58`, `option`'s eqType generic, ideal `processor_state` and its two
obligations translated and audited pending (were `UNIVERSE_REJECTED`/blocked); `JLFP_policy` still
refused; `STATEMENT_VALIDATED`. Expected corpus effect, to be measured: the 701 protected specialized
statements become generic or — where R3G finds no source level — are refused (a *correction* that may
lower the Accepted/Audited Pending counts: those rows were narrowed, not faithful).

Regressions (fixture/historical, measured on `5dcee42`): `test-statement` 29/29, `test-assembly` 32/32,
`test-termination` 22/22, `test-universe-c` 8/8, `test-all` 18/18 (frozen worktree).

### (6) Commands and evidence

`scripts/test-universe-c` (8 checks), `reports/statement_only/test_universe_c.json`,
`docs/UNIVERSE_FAMILY_C.md`.

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

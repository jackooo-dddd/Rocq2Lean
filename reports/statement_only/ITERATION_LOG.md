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

Commit: `803d733` (code; local, not pushed), provenance results in the follow-up commit.

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
python3 -I inventory/statement_provenance.py check
scripts/test-provenance
```

Provenance results (2026-10-14): 36/36 chunk round trips OK (48,064 records), merge re-derived, all
4,474 protected roots covered, union universe check 0 violated, manifest `CORPUS_PROVENANCE_BOUND`,
`check` OK, `test-provenance` OK (4 negative controls rejected). See `PROVENANCE.md` §5.

Correction (found in Task C, entry 3 on branch `task-c`): 701 of the protected statements counted
above as Accepted/Audited Pending were translated with universe levels defaulted to 0 (specialized),
which neither the translator nor the audit refused at this commit.

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

---

## Entry 4 — C-1 correctness repair; corpus measurement of B (diagnostic) and B+C-1 (2026-10-14)

Commits (branch `task-c`): `4eef4bc` (repair: translator + audit), `5330d87` (docs, provenance reuse
check, transition tooling), `3227883` (tooling); measurement commit: this entry. B diagnostic run: branch
`task-b-run` (`a9d49bf`: `task-b` implementation tree + measurement tooling only; implementation-tree
digest `7a9d5055…` = `task-b`'s).

### (1) What was changed and why

C-1 is a **correctness repair**, not a coverage extension. The baseline's Accepted / Audited Pending
totals (entries 0–1) are **historical results affected by a universe-specialization defect**: universe
levels that the source leaves free were fixed (mostly to 0) — `∀ Job : Equality.type.{0,0}`,
`∀ Job : JobType.{0,1}` — narrowing statements and protected definitions. The baseline translator
self-reported defaulted levels on 701 protected statements (entry 3); the defect is wider: a level can
be pinned *without* a default, by unification with an already specialized declaration (a hypothesis
typed by the specialized `opt_eqP.type.{}`) or, for a definition, by its value (no cumulativity).

Repair (`docs/UNIVERSE_FAMILY_C.md` §2): a **source-derived generality obligation**, in the translator
(`Rocq2Lean/Emit.lean` `freeLevelPin`, refusal) and independently in the audit (`tools/audit.py`
`check_statement_generality`, rejection; it reads no translator flag). For a reference `c.{σ…} a₁…aₙ` and
a source level `l` of `c` that is not a level of the declaration: `l` is free when the native graph does
not force `l ≤ Set` and no applied argument determines it (pending hypothesis binders excluded;
sibling-fixed type arguments skipped); a free level whose argument is not its parameter is a
specialization. Enforced in every statement and in the binder domains of protected definitions and
inductives; reported as a diagnostic for non-protected definitions (their value may fix the level).
Plus C-1 proper (entry 3: R3G reads a statement's statement; residual statement levels refused).

Strengthened controls (`scripts/test-universe-c`, 14 checks): the *target* narrowed with every
self-reported trace removed (no `universe_level_defaults`, no residual record, no implicit level) —
`opt_eqP` at `Equality.type.{0,0}`, `.{0,1}` (a nonzero closed level R3 admits; only the generality
obligation rejects it), `.{2,2}` (R3 rejects: raising), and the protected `job_cost` at its `Job`
binder — kernel-accepted, audit-rejected. Positive control: the generic `opt_eqP`, `option`'s eqType,
`ProcessorState` and `job_cost` kernel-checked at universes 2..5, the statement used at an
`Equality.type.{3,4}`; the same file fails on the narrowed module.

Correction of entry 3: the ideal `processor_state` is **refused** (its translation still narrows `Job`
to level 0 through `ProcessorState`'s R2F core-finType level `max(u₁₀₁, u₅₁)` and `unit`'s finType at
0); entry 3's "processor_state family translated" was a false acceptance caught by neither check then.

`JLFP`/`FP`/`JLDP_policy`: unsupported by the current representation and rules; kept blocked; the
proposed result-sort relaxation is **not** applied.

### (2) Coverage — same 4,474 protected roots, same merged IR (9,970 records, SHA-256 identical to A's)

| run | family | Accepted | Audited Pending | Blocked Dependency | Direct Failure |
|---|---|---|---|---|---|
| A (`803d733`), historical | modern | 344 | 1,002 | 1,140 | 18 |
| | Classic | 225 | 1,012 | 725 | 8 |
| | **total** | **569** | **2,014** | **1,865** | **26** |
| A, of which narrowed (re-audit with the repair audit) | modern | 122 | 836 | — | — |
| | Classic | 75 | 843 | — | — |
| A, claims surviving the repair audit | **total** | **372** | **335** | — | — |
| B only (`task-b`), **diagnostic** (no C-1) | modern | 344 | 1,055 | 1,087 | 18 |
| | Classic | 225 | 1,307 | 428 | 10 |
| | total | 569 | 2,362 | 1,515 | 28 |
| **B + C-1** (`3227883`) | modern | 340 | 987 | 1,140 | 37 |
| | Classic | 185 | 609 | 1,126 | 50 |
| | **total** | **525** | **1,596** | **2,266** | **87** |

B + C-1: consumer OK, audit OK (0 problems, generality check included). Raw claimed rows go from
2,583 (A) to 2,121; claims that survive the source-derived audit go from 707 (A) to 2,121. B-only is
not a faithful-coverage claim: its own (pre-repair) audit passes, but re-audited with the repair audit
**all 1,876 baseline narrowings persist** and **257 of its 348 newly supported declarations are
narrowed** (2,843 narrowed rows in all).

### (3) Per-declaration transitions A → B + C-1 (`reports/statement_only/coverage/transitions-A-to-C1-repair.json`)

| class | modern | Classic | total |
|---|---|---|---|
| unchanged | 1,434 | 817 | 2,251 |
| **newly supported** (Blocked/Direct → Accepted/Pending) | 98 | 160 | **258** |
| **false acceptance corrected** (narrowed in A; claimed now, generic) | 847 | 342 | **1,189** |
| **false acceptance rejected** (narrowed in A; refused or blocked now) | 111 | 576 | **687** |
| collateral loss (faithful in A; blocked now by a false acceptance now refused) | 0 | 27 | 27 |
| **genuine regression** | 6 | 0 | **6** |
| moved between Blocked and Direct Failure | 8 | 48 | 56 |

Matrix (category A → B+C-1): Accepted→Accepted 525, →Blocked 37, →Direct 7; Pending→Pending 1,338,
→Blocked 644, →Direct 32; Blocked→Pending 250, →Blocked 1,572, →Direct 43; Direct→Pending 8, →Blocked
13, →Direct 5. No Accepted → Audited Pending move.

* **Newly supported (258):** 212 also in B (termination lowering of `edivn_rec`/`modn_rec`, now
  generic); the rest unblocked by C-1 (`opt_eqP`, `option`'s eqType generic).
* **Old false acceptances (1,876 protected; 2,586 rows in all):** 958 modern (122 Accepted, 836
  Pending), 918 Classic (75 Accepted, 843 Pending); 1,189 now generic, 687 refused or blocked.
  Top root blockers of the 687 + 27: `mathcomp.boot.choice.HB_unnamed_mixin_106__rocq2lean_obligation_1`
  (367; in A `∀ T : Countable.type.{0,0}`; now refused: two statement levels reach references only
  through `max`, which R3G cannot map to source levels), `Priority.JLFP_policy` 73, `JLDP_policy` 49,
  `FP_policy` 48 (policy blocker), `JobReady` 46 (protected inductive, narrowed field), `Sustainability.
  type_of_label` 25, `overheads.processor_state` 15, `PolicyTDMA.TDMA_slot_order` 12.
* **Collateral losses (27, Classic):** A rows that pass the repair audit themselves but depend on a
  false acceptance now refused (`FP_policy`/`JLFP_policy`, the `HB_unnamed_mixin_106/107` obligations
  via `pick`/`minmax`, `type_of_label`). A consequence of the repair, not of an unrelated change.
* **Genuine regressions (6):** `prosa.implementation.refinements.refinements.refine_{all,cons,flatten,
  last,map,nil}` (Audited Pending → refused). Their defaulted level occurs only as `max(u₃₈₁, r)`, so
  the defaulted statement equals the source's; the source-derived audit accepts them in A. C-1's
  blanket refusal of residual statement levels is conservative here. Not yet fixed.
* **Downstream:** the 701 statements have no protected dependents (proof tasks). The 1,876 have 1,222
  distinct protected dependents outside the set: 1,110 unchanged, 79 newly supported, 21 collateral
  losses, 12 moved Blocked ↔ Direct.

The 701 self-reported statements, individually (`reports/statement_only/c1/AFFECTED.json`, every row
with its A / B / B+C-1 status, class, root blockers, downstream): 518 corrected (generic, still claimed:
Pending→Pending 410, Accepted→Accepted 108); 183 no longer claimed (Pending → Blocked 175, → Direct 8),
of which 177 are rejected false acceptances and 6 the genuine regressions. 695 of the 701 are also found
by the source-derived check; the other 6 are the `refine_*` rows (not narrowed).

### (4) Remaining blockers and pending obligations

* Pending (B + C-1): 1,780 pending rows (1,596 protected); 1,558 proof tasks (`PROOF_TASKS.jsonl`:
  1,194 theorem statements, 320 obligations, 38 opaque values, **2 termination obligations**, **2
  unfolding equations**, 2 source assumptions). The termination obligations of `edivn_rec`/`modn_rec`
  are prerequisites of 204 / 138 protected pending declarations; `eqnP` of 1,534; `opt_eqP` of 194.
* Conversion dependence (B and B + C-1): 738 dependents of the lowered definitions re-checked in Rocq:
  737 `CONV_OK`, 1 `CONV_NEEDS` (`mathcomp.boot.div.gcdn`, not claimed: `TRANSLATION_FAILED` with an
  internal "unknown metavariable" error rather than a clean refusal — a translator defect to fix);
  status OK (no claimed row needs the unfolding).
* Universe: the `HB_unnamed_mixin_106/107` obligations (max-coupled statement levels, R3G), the policy
  family (unsupported by the current rules), protected inductives/definitions whose only translation
  narrows (`JobReady`, ideal / overheads `processor_state`, `SystemEvolutions`, `seq_argmax_nat`).
* A′ (opaque data bodies), HB builder obligations: unchanged.

### (5) Regressions and validation

Fixture suites on the repair (`4eef4bc`, r2l-B): `test-statement`, `test-assembly`, `test-termination`,
`test-universe-c` (14), `test-provenance`: all OK. `test-all` 18/18 on `3227883` (frozen worktree
`r2l-B-test`, 24 min; proof-mode suites unchanged).
Corpus: the 6 genuine regressions above; no other faithful A claim is lost except the 27 collateral
losses.

Validation gaps: (a) the generality check is syntactic determination — sound for the rejections it
makes, but a level fixed only through definitional unfolding would be refused/rejected conservatively;
(b) protected definitions are checked at their quantification ranges, not their result types;
non-protected definition types are a diagnostic only (65 candidates in B + C-1, 139 in A); (c) the
round trips are reused (inputs byte-identical; round-trip tool and `RtEq.v` unchanged; exporter
sources changed by 78 added lines only, `ROUNDTRIP_TOOLS_BASE.json`), not re-run; (d) the corpus run
directories are local (git-ignored), bound by digest in the manifests.

### (6) Commands and evidence

```
# frozen worktrees: r2l-run-B (task-b-run), r2l-run-C (3227883); source.ndjson copied from runs/st-corpus-A
STATEMENT_RUN=runs/st-corpus-B  python3 -I inventory/statement_run.py translate && … check   # r2l-run-B
STATEMENT_RUN=runs/st-corpus-C1 python3 -I inventory/statement_run.py translate && … check   # r2l-run-C
python3 -I inventory/conversion_deps.py RUN --jobs 2
python3 -I inventory/coverage_delta.py snapshot RUN reports/statement_only/coverage/{B-termination,C1-repair}.json
python3 -I inventory/statement_provenance.py manifest RUN && … check
python3 -I tools/audit.py … (repair audit) on runs/st-corpus-A and runs/st-corpus-B   # re-audits
python3 -I inventory/c1_transitions.py A-assembly.json A_REAUDIT NEW.json RUN transitions-A-to-NEW.json --old-run runs/st-corpus-A
python3 -I inventory/c1_affected.py transitions-A-to-C1-repair.json transitions-A-to-B-termination.json reports/statement_only/c1/AFFECTED.json
STATEMENT_RUN=runs/st-corpus-C1 python3 -I inventory/statement_run.py tasks
```
Evidence: `reports/statement_only/coverage/{B-termination,C1-repair,transitions-A-to-*}.json`,
`reports/statement_only/c1/AFFECTED.json`, `reports/statement_only/provenance/CORPUS_MANIFEST{,-A,-B}.json`
(current = B + C-1; `CORPUS_PROVENANCE_BOUND`, `check` OK for all three),
`reports/statement_only/termination/CONVERSION_DEPENDENCE-{B,C1}.json`, `PROOF_TASKS.jsonl` (B + C-1),
`reports/statement_only/test_universe_c.json`.

---

## Entry 5 — A′: opaque data translated with its body (2026-10-14)

Commits (branch `task-a-prime`, from `ec3409c`): `f786571` (A′), `01782c7` (conversion dependence
through parent definitions), `2f1d5cb` (round trip: term-only quotation), `cedf425` (manifest records
its evidence directories). Frozen run worktree `r2l-run-AP` at `2f1d5cb`/`cedf425` (tooling only
differs; implementation tree of the run = `2f1d5cb`).

### (1) What was added and why

Opaque `Set`/`Type` constants (`Qed` data) were exported as interfaces only; their values were tasks
that no submission may satisfy, so 1,588 of the 1,596 protected pending declarations of B + C-1 could
never be assembled. A′ (`docs/OPAQUE_DATA.md`): the exporter prepares the body (proof subterms extracted
as obligations, Rocq's kernel re-check) and exports it (`opaque_data`, native opacity kept); the
translator emits a Lean `opaque` constant under the source name (never unfolded, as Rocq never unfolds
`Qed`), pending on the obligations; consumer and audit require the `opaque` kind and audit the body as
a definition. A body Rocq accepts only with the guard check deferred (a recursion on an extracted proof
subterm) or not at all keeps the interface, with the reason (`opaque_body_refused`). No value is ever
accepted in place of a source body; Rocq2Lean writes no corpus proof.

Round trip: the statement re-derivation now prepares the environment once per export
(`CheckStatementsPrepared`, as the export does) plus a deterministic per-constant sample (request
independence), and quotes the term alone (`quote_term`; identical output measured on a corpus chunk).
Cost: 135 chunk round trips in 25 min wall (3 jobs), against 16.7 CPU-hours for the 36 chunks of A.

### (2) Coverage — same 4,474 protected roots, re-exported (A′ exporter), 10,966 merged records

| run | family | Accepted | Audited Pending | Blocked Dependency | Direct Failure |
|---|---|---|---|---|---|
| B + C-1 (`3227883`) | modern | 340 | 987 | 1,140 | 37 |
| | Classic | 185 | 609 | 1,126 | 50 |
| | total | 525 | 1,596 | 2,266 | 87 |
| **A′** (`2f1d5cb`) | modern | 338 | 989 | 1,146 | 31 |
| | Classic | 182 | 612 | 1,126 | 50 |
| | **total** | **520** | **1,601** | **2,272** | **81** |

Consumer OK, audit OK (C-1 generality check included). The category totals barely move — a pending row
stays pending — but **what the pending rows wait for changes**:

| protected pending rows | B + C-1 | A′ |
|---|---|---|
| needing at least one opaque value (not assemblable) | 1,588 | **6** |
| needing only opaque values | 1,342 | 0 |
| needing only proof tasks (assemblable once proved) | 8 | **1,595** |

The 6: dependents of `mathcomp.boot.ssrnat.find_ex_minn` (body recurses on an accessibility proof;
interface kept). Opaque data in the closure: 167 translated with their bodies (5 accepted, 41 pending
on obligations, 118 blocked, 3 direct failures), 1 interface.

### (3) Transitions B + C-1 → A′ (`coverage/transitions-C1-to-AP-opaque.json`)

4,463 unchanged; **no claimed row of B + C-1 (protected or not) becomes unclaimed**; 5 protected rows
Accepted → Audited Pending (`Sustainability.eqlabelP`, `fixedpoint.iter_fixpoint_ind`, `list.mapP2`,
`ideal_uni_exceed.eqn_exceedance_processor_state`, `tactics.neqP` — themselves opaque data: before,
only their type interface was accepted, their value a task; now the definition with its body, pending
on its obligations); 6 protected rows Direct Failure → Blocked Dependency. Newly supported: 0.
A → A′ (`transitions-A-to-AP-opaque.json`): 258 newly supported, 1,189 false acceptances corrected,
687 rejected, 27 collateral losses, 6 genuine regressions (the C-1 `refine_*`), as in entry 4.

### (4) Remaining blockers and pending obligations

* Proof tasks: 1,677 (474 obligations, 1,196 theorem statements, 2 termination obligations, 2
  unfolding equations, 2 source assumptions, **1 opaque value** — `find_ex_minn`; B + C-1: 38).
* Newly reached failures (rows not in B + C-1's closure; none protected): 45 — CoqEAL refinement
  relations (`Prop ≤ Type` cumulativity at relation arguments, R2B/universe refusals), `Corelib.Classes`
  morphisms, Prosa implementation helpers.
* Blocked opaque bodies (118): mostly CoqEAL `refines_*` obligations (universe solving), the protected
  `ArrivalCurvePrefix` (R2B-S refused), `hrel.fun_hrel` (kernel).
* Conversion dependence: 887 dependents (extracted obligations now checked through their parent
  definitions): 886 `CONV_OK`, 1 `CONV_NEEDS` (`gcdn`, not claimed); status OK. The 10 kernel-rejected
  `Rnat_div_eucl` obligations do not need the unfolding (Rocq accepts them without the lowered bodies):
  they are cumulativity failures.

### (5) Regressions and validation

`test-all` 18/18, `test-statement` 30, `test-assembly` 34, `test-termination` 22, `test-opaque` 16
(new), `test-universe-c` 14, `test-provenance` OK — all on `2f1d5cb` (frozen worktree `r2l-B-test`).
Test expectations changed by A′ (documented in the tests): FinishTime roots now wait for proof tasks and
`find_ex_minn`'s value instead of `eqnP`'s value; the assembly fixture's `pick` is an accepted opaque
constant and the value-task path is exercised by a new interface case (`pick_wf`); C's negative
controls narrow an `opt_eqP` obligation statement (opt_eqP is now an opaque constant). Corpus: no
claimed row lost.

Provenance (`provenance/CORPUS_MANIFEST.json`, current = A′): 135 chunk snapshots (IRs match their
export records), 135/135 round trips OK, merge re-derived (10,966 records), all 4,474 roots, union
universe check 260,885 facts, 0 violated; `CORPUS_PROVENANCE_BOUND`, reuse `SAME_TOOLS`, `check` OK.
The manifests of A, B and C-1 (`CORPUS_MANIFEST-{A,B,C1}.json`) check OK with their own tools (task-c)
and are correctly rejected under A′'s (the round-trip tool changed): evidence is tool-relative.

Validation gaps: the A′ round trip's request-independence evidence is a sample (8 constants per
export), not every constant; opaque bodies blocked by universes or cumulativity keep their dependents
blocked (now through the body, before through the interface).

### (6) Commands and evidence

```
# r2l-run-AP; INVENTORY_EXPORT_MODE=statement INVENTORY_EXPORT_TAG=aprime
python3 -I inventory/export.py modern 2 && python3 -I inventory/export.py classic 2
export STATEMENT_EXPORT=export-statement-aprime STATEMENT_PROVENANCE=provenance-aprime STATEMENT_RUN=runs/st-corpus-AP
python3 -I inventory/statement_run.py merge && … translate && … check && … tasks
python3 -I inventory/conversion_deps.py runs/st-corpus-AP --jobs 2
python3 -I inventory/coverage_delta.py snapshot runs/st-corpus-AP reports/statement_only/coverage/AP-opaque.json
python3 -I inventory/statement_provenance.py snapshot && … roundtrip --jobs 3 && … union runs/st-corpus-AP --jobs 2
python3 -I inventory/statement_provenance.py manifest runs/st-corpus-AP && … check; scripts/test-provenance
python3 -I inventory/c1_transitions.py C1-repair.json C1_AUDIT AP-opaque.json runs/st-corpus-AP transitions-C1-to-AP-opaque.json
```
Evidence: `coverage/{AP-opaque,transitions-C1-to-AP-opaque,transitions-A-to-AP-opaque}.json`,
`provenance/CORPUS_MANIFEST.json`, `termination/CONVERSION_DEPENDENCE-AP.json`, `PROOF_TASKS.jsonl`
(A′), `test_opaque.json`, `docs/OPAQUE_DATA.md`.

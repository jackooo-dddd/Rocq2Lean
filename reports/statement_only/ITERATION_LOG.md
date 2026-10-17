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

---

## Entry 6 — R2B-V: a type-valued definition declared at the sort of its value (2026-10-14)

Approved by the user on 2026-10-14 ("feel free to merge task-c and any JLFP_policy rule after the other
parts … are done"). Commits (branch `task-r2bv`, on top of `task-a-prime`): `7957a82` (rule),
`5922bc6` (the value's sort must be a Type — found by the first corpus run, see below), `df09655`
(only validated runs are bound by a manifest). Also: `main` fast-forwarded to `task-c` (`ec3409c`;
local, not pushed).

### (1) What was added and why

`JLFP`/`FP`/`JLDP_policy` (`:= rel Job`) are typed by Rocq at `rel`'s level through cumulativity; Lean
has none. Rule R2B-V (`docs/UNIVERSE_FAMILY_C.md` §4), general (no name-specific case): for a
*definition* whose source type ends in a sort, the levels occurring only in that result sort are
replaced by the sort of the translated value, each solved to a **lowering** (native facts), the value's
sort a **Type** (never Prop); binders, value and references unchanged (C generality and R3 still
apply). Last translation tier, statement mode only, so no previously accepted row changes. Independent
copies: audit (applicability, occurrence in the result sort, lowering, Type, never a statement),
consumer (in Lean: declared result sort = the value's sort, never zero), CLI validation (flag required
for a protected result-sort lowering).

First corpus run (`7957a82`) — **not validated**: the audit rejected 5 rows (sort mismatch) and the
consumer 1 (a definition emitted as a theorem): Prop-valued relations declared in `Type` (CoqEAL `Rnat`,
`hrel.fun_hrel`; Prosa `Rtask`, `Rtask_ab`, `RArrivalCurvePrefix`) had been declared as propositions —
not a level lowering. Fixed in `5922bc6` (all three checkers require a Type; fixture control
`SF.R2bv.Rprop`); the numbers below are from the re-run.

### (2) Coverage — same 4,474 protected roots, A′ export (10,966 records, chunk evidence reused: `SAME_TOOLS`)

| run | family | Accepted | Audited Pending | Blocked Dependency | Direct Failure |
|---|---|---|---|---|---|
| A′ (`2f1d5cb`) | modern | 338 | 989 | 1,146 | 31 |
| | Classic | 182 | 612 | 1,126 | 50 |
| | total | 520 | 1,601 | 2,272 | 81 |
| **R2B-V** (`5922bc6`) | modern | 446 | 1,276 | 745 | 37 |
| | Classic | 227 | 899 | 775 | 69 |
| | **total** | **673** | **2,175** | **1,520** | **106** |

Consumer OK, audit OK (0 problems), provenance bound (`checks` consumer/audit OK, reuse `SAME_TOOLS`),
`check` OK, `test-provenance` OK.

### (3) Transitions A′ → R2B-V (`coverage/transitions-AP-to-V-r2bv.json`)

3,708 unchanged; **727 newly supported** (modern 395, Classic 332); 39 Blocked → Direct Failure; **no
claimed row lost** (no false acceptance, no regression). A → R2B-V (`transitions-A-to-V-r2bv.json`):
767 newly supported, 1,397 false acceptances corrected, 479 rejected, 17 collateral losses, 6 genuine
regressions (the C-1 `refine_*`).

Rows using the rule: 14, all protected — `JLFP`/`FP`/`JLDP_policy` and `TDMA_slot_order` (modern and
Classic), Classic `Sustainability.type_of_label`, four Classic `ConcreteTask.concrete_taskset`, modern
`ArrivalCurvePrefix`.

Downstream-use measurement: the 14 have 1,439 protected dependents — 713 newly supported (143
Accepted, 570 Audited Pending), 687 still blocked (other blockers), **39 direct failures**: the uses the
interface analysis predicts (a dependent needing the definition at a larger universe, refused, never
narrowed): 15 refused by the C generality check, 7 by R2B-P protection, 5 by level solving, 1 by binder
protection, and 9 `TRANSLATION_FAILED` ("pending prerequisite pair_eqP__rocq2lean_obligation_1 is
needed at two different types": the prerequisite statement is used at two universe instances in one
declaration, and a pending artifact has one hypothesis per prerequisite — a reported limitation of the
hypothesis telescope, not a crash).

### (4) Remaining blockers and pending obligations

Proof tasks: 2,116 (1,581 theorem statements, 526 obligations, 2 termination obligations, 2 unfolding
equations, 4 source assumptions, 1 opaque value). Conversion dependence: 887 dependents, 886 OK, 1
needs the unfolding (`gcdn`, not claimed). Blockers: the `HB_unnamed_mixin_106` obligation family
(max-coupled levels), protected definitions whose translation narrows (`JobReady`, ideal / overheads
`processor_state`), the 39 use-site refusals, CoqEAL cumulativity (`Prop ≤ Type`).

### (5) Regressions and validation

`test-universe-c` 22 (R2B-V: policies translated with the job generic; 6 downstream uses audited;
nonzero-universe positive control; forgeries — not a lowering, a binder level, on a statement, the
protected lowering without the rule — rejected; Prop-valued control), `test-statement` 30,
`test-assembly` 34, `test-termination` 22, `test-opaque` 16: OK on `5922bc6`; `test-all` 18/18 on
`7957a82` and 18/18 on `5922bc6` (frozen worktree `r2l-B-test`; the proof-mode pipeline does not use the
tier).

### (6) Commands and evidence

```
# r2l-run-V (5922bc6 / df09655); source = runs/st-corpus-AP/source.ndjson; chunk evidence of A′ linked
export STATEMENT_EXPORT=export-statement-aprime STATEMENT_PROVENANCE=provenance-aprime STATEMENT_RUN=runs/st-corpus-V
python3 -I inventory/statement_run.py translate && … check && … tasks
python3 -I inventory/conversion_deps.py runs/st-corpus-V --jobs 2
python3 -I inventory/coverage_delta.py snapshot runs/st-corpus-V reports/statement_only/coverage/V-r2bv.json
python3 -I inventory/statement_provenance.py manifest runs/st-corpus-V && … check; scripts/test-provenance
python3 -I inventory/c1_transitions.py AP-opaque.json AP_AUDIT V-r2bv.json runs/st-corpus-V transitions-AP-to-V-r2bv.json
```
Evidence: `coverage/{V-r2bv,transitions-AP-to-V-r2bv,transitions-A-to-V-r2bv}.json`,
`provenance/CORPUS_MANIFEST.json` (current = R2B-V; `-AP`, `-C1`, `-B`, `-A` kept),
`termination/CONVERSION_DEPENDENCE-V.json`, `PROOF_TASKS.jsonl`, `test_universe_c.json`,
`docs/UNIVERSE_FAMILY_C.md` §4.

---

## Entry 7 — Rule round 2: binder-level independence (P1), jointly occurring level metavariables (P2), R2B-P validation parity (2026-10-14)

Commit `d40a55c` (branch `rules-r2`, from `main` `64195dc`); run worktree `r2l-run-R2` (same commit),
run `runs/st-corpus-R2` on the A′ export (chunk evidence reused, `SAME_TOOLS`). Backlog refreshed:
`reports/statement_only/RULE_BACKLOG.{md,json}` (tool `inventory/rule_backlog.py`; every unclaimed
protected root traced to its direct blockers; 0 UNCLASSIFIED).

### (1) What was changed and why

* **P1 — diagnosis first.** The six `refine_*` regressions of entry 4 were statement rows whose
  defaulted level was absorbed by `max`. Since A′ they are opaque data with bodies; what blocks them now
  are their *obligations*, whose residual levels are **not** irrelevant: CoqEAL's `list_R` has one level
  (`Datatypes.190`) for both carriers and the relation, so the Lean translation identifies the
  obligation's independent binder levels `1580`, `1581`, `1582` (`A : Type@{1580}`, `C : Type@{1581}`,
  facts `1580 ≤ 1582`, `1581 ≤ 1582` only) — defaulting would narrow. The six roots are also blocked by
  CoqEAL `all_R`/`map_R`/`last_R`/`cat_R`/`foldr_R` (course-of-values).
* **P1 — rule implemented (translator `Rocq2Lean/Emit.lean` `binderIndependence`; independent audit
  copy `tools/audit.py` `check_binder_independence`).** A statement's binder levels keep the source's
  independence: a translated order between two binder levels (identification included) must be entailed
  by the native facts; a binder level fixed at a closed level must be forced `≤ Set`. This source-derived
  check **replaces** C-1's blanket refusal of defaulted statement levels (translator) and the
  self-report-based rejection (audit): a residual default is acceptable exactly when the defaulted
  statement passes binder independence and reference generality. Re-audit of the previous run
  (`st-corpus-V`) with it: 0 problems (no hidden false acceptance of this kind).
* **P2 (translator, statement rows).** Level metavariables that occur only jointly — summands of one
  `max` with one offset in every level expression, the hypothesis telescope excluded — are identified
  before R3G names classes (the statement depends only on their maximum). Restricted to statements
  (for a definition the residual-default path stays: identifying there made `eqtype.Sub` fail R3).
* **P2 diagnosis of the rest.** The other obligations of the `HB_unnamed_mixin_10x` family are not
  max-coupled: their `Countable` carrier level is fixed to 0 *before* R3G by unification through
  `ssrfun.pcancel` (one universe parameter for both type arguments, applied to `nat`/`option`), which
  Rocq accepts by cumulativity: the coupled-reference mechanism of P1. Both need one representation
  decision (below).
* **Validation parity (found while testing).** The corpus check path lacked two CLI-validation rules:
  pending artifacts with R2B-P levels (one was claimed: `mathcomp.boot.eqtype.insub`, non-protected, no
  claimed protected dependent) and Rocq's instance re-check of accepted R2B-P rows (4 rows, all
  `INSTANCE_OK` when re-checked against the previous run). Now: the translator refuses R2B-P on pending
  artifacts; `statement_run.py instances` re-checks accepted R2B-P rows in the common environment; the
  corpus manifest requires it (`checks.source_instances`).

### (2) Coverage — FULL CORPUS, same 4,474 protected roots

| run | family | Accepted | Audited Pending | Blocked Dependency | Direct Failure |
|---|---|---|---|---|---|
| R2B-V (`5922bc6`) | modern | 446 | 1,276 | 745 | 37 |
| | Classic | 227 | 899 | 775 | 69 |
| **round 2** (`d40a55c`) | modern | 446 | 1,276 | 745 | 37 |
| | Classic | 227 | 899 | 775 | 69 |
| | **total** | **673** | **2,175** | **1,520** | **106** |

Consumer OK, audit OK, source instances OK (4), provenance bound (`checks` all OK), `check` OK.
Per-declaration transitions (protected): **4,474 unchanged** (`coverage/transitions-V-to-R2-binder.json`).
All rows: 23 newly claimed (MathComp `choice` `HB_unnamed_mixin_106/107/109` obligations, now generic
statements), 1 no longer claimed (`eqtype.insub` — an unvalidated claim corrected), 16 rows changed
refusal reason. No genuine regression. Direct failures 770 → 757.

### (3)–(4) Backlog (refreshed) and next tasks

Largest families (affected / only-this-family protected roots): `SOLUTION_FACT_VIOLATED` 917 / 31,
`STATEMENT_FREE_LEVEL_PINNED` 885 / 48, `REFERENCE_COHERENCE` 388 / 225, `PROTECTED_RANGE_NARROWED`
379 / 211, `PROP_TYPE_CUMULATIVITY` 102 / 0, `COUPLED_BINDER_LEVELS` 39 / 2, `MULTI_INSTANCE_PREREQUISITE`
36 / 18, `INTERNAL_ERROR` (gcdn) 25 / 25, `COINDUCTIVE` 13 / 13. The roots formerly counted under the
P1/P2 residual family (749 jointly with solution facts) are now blocked by `STATEMENT_FREE_LEVEL_PINNED`
(the pcancel-coupled obligations). Representation decision needed: per-binder-sort universe parameters
for declarations whose one source level covers several independently instantiated arguments.
Next (unblocked): P3 (instance-aware prerequisite hypotheses).

### (5) Regressions and validation

`test-universe-r2` (new, 9: `pairR_intro` refused by binder independence; consistent narrowing
forgeries — two binder levels identified, a binder level at 0, the P2 obligation narrowed at
`choice.959` — kernel-accepted and audit-rejected; nonzero-universe positive control), `test-statement`
30, `test-assembly` 34, `test-termination` 22, `test-opaque` 16, `test-universe-c` 22: OK;
`test-all` 18/18 (frozen worktree, `d40a55c`).

### (6) Commands and evidence

```
STATEMENT_EXPORT=export-statement-aprime STATEMENT_PROVENANCE=provenance-aprime STATEMENT_RUN=runs/st-corpus-R2 \
  python3 -I inventory/statement_run.py translate && … check && … instances && … tasks
python3 -I inventory/conversion_deps.py runs/st-corpus-R2 --jobs 2
python3 -I inventory/coverage_delta.py snapshot runs/st-corpus-R2 reports/statement_only/coverage/R2-binder.json
python3 -I inventory/statement_provenance.py manifest runs/st-corpus-R2 && … check
python3 -I inventory/rule_backlog.py runs/st-corpus-R2 --conversion …/CONVERSION_DEPENDENCE.json
```
Evidence: `coverage/{R2-binder,transitions-V-to-R2-binder}.json`, `RULE_BACKLOG.{md,json}`,
`provenance/CORPUS_MANIFEST.json` (current; `-V` kept), `termination/CONVERSION_DEPENDENCE-R2.json`,
`test_universe_r2.json`, `PROOF_TASKS.jsonl`.

---

## Entry 8 — P3: instance-aware prerequisite hypotheses (2026-10-14)

Commit `1d45a15` (branch `rules-r2`); run worktree `r2l-run-R3`, run `runs/st-corpus-R3` (A′ export,
chunk evidence reused, `SAME_TOOLS`).

### (1) What was changed and why

`mathcomp.boot.eqtype.pair_eqP__rocq2lean_obligation_1` (accepted, generic in two levels) was needed
at two universe instances by 9 protected Prosa definitions (`TRANSLATION_FAILED`: "needed at two
different types"); prerequisite hypotheses were keyed by leaf name only. Now (`Rocq2Lean/Translate.lean`
`hypFor`, `Rocq2Lean/Emit.lean` `collapseHyps` + retry tier, `tools/audit.py`):

* one hypothesis per *instance* (`h_<leaf>`, `h_<leaf>__k`); a hypothesis is reused only at its own
  type, never at another; the default path compares the statement constant's universe arguments first
  (no unfolding across instances);
* retry tier (statement mode, after the other attempts fail): reuse only at a type equal without
  assigning any level metavariable; after universe solving, hypotheses of one leaf at the same type
  are collapsed into the first (otherwise eager unification across uses merges instances the source
  keeps apart — the fixture `use2` pinned `B` to level 0);
* audit: a leaf may occur once per instance in `pending_hypotheses`, never twice at the same type;
  references resolve to any hypothesis of the right leaf (the kernel checked its type); tasks and
  assembly unchanged (sets; each use re-translated against the generic final theorem).

### (2) Coverage — FULL CORPUS, same 4,474 protected roots

Unchanged: 673 / 2,175 / 1,520 / 106 (modern 446 / 1,276 / 745 / 37, Classic 227 / 899 / 775 / 69);
4,474 protected rows unchanged. Consumer, audit, source instances (4), provenance: OK.

All rows: no row newly claimed, none lost. The 9 `pair_eqP` rows now pass the prerequisite step and stop
at their next blockers (8: residual levels the kernel does not justify generically — `hep_task`
applied to a `RocqPending.…Task` at another level, the coupled-reference mechanism; 1: a coherence
refusal); no claimed row uses per-instance hypotheses yet. P3 is validated on the fixture
(`test-multi-instance`), **not** a measured corpus gain.

### (3)–(4) Backlog and next

`MULTI_INSTANCE_PREREQUISITE` removed; its members are now `UNIVERSE_OTHER`/`REFERENCE_COHERENCE`.
`REFERENCE_COHERENCE` (389 / 226) diagnosed: `JobType`/`TaskType`'s R2F reading `max(u51+1, u58)`
against a single-level sort `?a+1`; the bounded solver fixes the free level to 0, which the generality
check refuses. The three largest families (`SOLUTION_FACT_VIOLATED`, `STATEMENT_FREE_LEVEL_PINNED`,
`REFERENCE_COHERENCE`) and `COUPLED_BINDER_LEVELS` share one mechanism — one Lean universe parameter where
Rocq's cumulativity instantiates several arguments independently — and need the representation decision
(per-binder-sort universe parameters) before further work. `PROTECTED_RANGE_NARROWED` (379 / 211) and
`PROP_TYPE_CUMULATIVITY` (102) need their own representation decisions. Without a decision, the next
unblocked items are `INTERNAL_ERROR` (gcdn → clean refusal, 25 roots blocked only by it, but it stays
blocked: it needs the unfolding) and `COINDUCTIVE` (13, Classic `extraction_tdma`).

### (5) Regressions and validation

`test-multi-instance` (new, 9), `test-universe-r2` 9, `test-statement` 30, `test-assembly` 34,
`test-termination` 22, `test-opaque` 16, `test-universe-c` 22: OK; `test-all` 18/18 (`1d45a15`).

### (6) Commands and evidence

As entry 7 with `runs/st-corpus-R3`; evidence `coverage/{R3-multi,transitions-R2-to-R3-multi}.json`,
`RULE_BACKLOG.{md,json}` (current), `provenance/CORPUS_MANIFEST.json` (current; `-R2` kept),
`termination/CONVERSION_DEPENDENCE-R3.json`, `test_multi_instance.json`.

## Entry 9 — R-SPLIT (experimental): one source level shared by several parameter sorts (2026-10-14)

Branch `rules-split` (from `rules-r2` `97ffe00`), commits `f79144d` and `a28c4b3`, **not merged, not
pushed**. Approved as a controlled experimental rule (Option A); held for review.
Run worktree `r2l-run-SPLIT2` (`a28c4b3`), run `runs/st-corpus-SPLIT2`. Inputs: the A′ export with its
chunk evidence reused; the merged source is byte-identical to R3's (`8eaf2da4…`); the exporter plugin is
byte-identical (`44a8c6ac…`). `docs/LEVEL_SPLIT.md`.

### (1) What was changed and why

COUPLED_BINDER_LEVELS: a monomorphic declaration such as CoqEAL `list_R` uses one level (`Datatypes.190`)
for both carriers and the relation. Rocq instantiates them independently by cumulativity. One Lean
universe parameter identifies them, so P1 refused the statements that use them at independent
levels (`refine_*` obligations).

**Translator** (`Rocq2Lean/Split.lean`, `translateSplit` in `Emit.lean`):
* A level that is the final sort of at least 2 parameter binders and occurs nowhere else except the
  result sort (counted over the type, body, constructors, instances, primitives and native metadata)
  gets one copy `l__s<i>` per binder.
* The result sort becomes the join of the copies.
* Copies satisfy `l__s<i> ≤ l` and inherit the upper bounds of `l`, never its lower bounds.
* References read every copy as `l` (R3: argument `a ≤ l`).
* The split view is kept only if the kernel accepts it and every copy stays a universe parameter.
  Otherwise the declaration is translated unsplit.

**Audit** (independent): its own split view by occurrence paths, then three checks:
* the reported split equals the derived one;
* the copies are fresh;
* the diagonal recovers the source exactly.

The row is then audited against the view by all existing checks (R3 with copies mapped back, binder
independence, generality); the audit output records this as `level_split_checked`.

**Consumer** (detector `levels`): each copy's parameter occurs as a sort only at its binder's final
sort and at the type's final sort.

**Correspondence** (`docs/LEVEL_SPLIT.md` §3):
1. The diagonal recovers the source exactly. The auditor checks this per row and over the whole
   corpus source (13/13 eligible declarations).
2. Each off-diagonal use is justified by the source fact `a ≤ l`, checked by R3 at every reference.
3. `tests/statement/proofs/split_correspondence.lean` is a synthetic proof on the fixture's own
   declarations, checked axiom-free. It shows every off-diagonal instance of `pR` / `fun_R` is
   isomorphic to the diagonal instance at the `ULift`ed carriers.

### (2) Coverage — FULL CORPUS, same 4,474 protected roots (validated)

| | Accepted | Audited Pending | Blocked | Direct Failure |
|---|---|---|---|---|
| R3 (entry 8) | 673 | 2,175 | 1,520 | 106 |
| **R-SPLIT** | **673** | **2,177** | **1,518** | **106** |

By family: modern 446 / 1,278 / 743 / 37, Classic 227 / 899 / 775 / 69 (unchanged).

Consumer, audit (`level_split_checked` 3), source instances (4) and provenance (`CORPUS_PROVENANCE_BOUND`):
all OK.

Protected transitions: 2 newly supported, 4,472 unchanged, 0 regressions, no old false acceptance.
The 2 newly supported roots are `prosa.implementation.refinements.refinements.refine_cons` and
`refine_nil` (blocked → audited pending).

All rows (10,970): 42 changed.
* 3 split declarations: `prod_R` (two levels), `list_R`, `pred_R`. All are more general; `pred_R`'s
  level 1105 was not a parameter before.
* `list_R_rect`: its split was not kept (one copy was defaulted, so the guard applies). Unsplit, it
  now keeps 190 generic (0 defaulted levels, previously 1).
* 16 statements newly accepted (`UNIVERSE_REJECTED` → `STATEMENT_KERNEL_CHECKED`):
  * 13 refine obligations: `refine_last` ×5, `refine_map` ×3, and one each for `refine_cons`,
    `refine_nil`, `refine_flatten`, `refine_all` and `refine_size`;
  * `refines_fst_R`, `refines_snd_R` and `refines_pair_R` obligations.
* 11 rows newly unblocked (`BLOCKED` → pending): six `refine_last` obligations; `refines_fst_R`,
  `refines_snd_R` and `refines_pair_R`; and `refine_cons` and `refine_nil` (protected).
* 11 `CoqEAL.refinements.binnat.Rnat_div_eucl` obligations remain failures with a new blocker:
  `KERNEL_REJECTED` (type mismatch at `prod_R`) → `UNIVERSE_REJECTED` (residual defaults not justified
  generically). PROP_TYPE_CUMULATIVITY drops from 20 to 9 members and UNIVERSE_OTHER rises from 9 to
  20. These are not regressions: the rows were failures before and remain failures.

No row lost its class.

**Remaining blockers.**
* The refinement roots are blocked by COURSE_OF_VALUES: `map_R`, `all_R`, `last_R`, `zip_R`, `cat_R`
  and `foldr_R` are eligible but unsupported, and `flatten_R` depends on them.
* The CoqEAL `Rnat` chain also blocks them (SOLUTION_FACT_VIOLATED).
* COUPLED_BINDER_LEVELS is gone from the backlog (it had 13 members, 39 affected, 2 blocked only by it).

**First corpus run (`r2l-run-SPLIT`, `f79144d`): NOT validated, kept as evidence.**
* `list_R_rect`'s split kept a defaulted copy (`s2 := 0`); the consumer rejected it.
* The audit refused the copy names `list_R_rect` shares with `list_R`.
* Fixed in `a28c4b3`:
  * a guard: every copy must stay a parameter;
  * a fact `l__s<i> ≤ l`;
  * a shared copy name is allowed only for the same level;
  * new fixture case `pR_tail` and a degenerate-split negative control.

### (3) Corrections to entries 7–8

The round-2/entry-8 claim was that SOLUTION_FACT_VIOLATED, STATEMENT_FREE_LEVEL_PINNED,
REFERENCE_COHERENCE and COUPLED_BINDER_LEVELS share one mechanism (`pcancel`-like single-level
references). **That claim is wrong.** `ssrfun.pcancel`'s two carriers are separate levels.

Re-diagnosis of STATEMENT_FREE_LEVEL_PINNED from the R3 report:
* 280 of its 340 members pin the **result-sort-only** level of an HB structure:
  * `eqtype.hasDecEq.axioms_ (T : Type@{29}) : Type@{32}`: 144 members;
  * `choice.hasChoice.axioms_` (level `choice.299`): 136 members.
* 50 more are at `Equality.type`.
* Lean's use context fixes that level to 0, where Rocq leaves it free.
* A rule (irrelevance of a result-sort-only reference level, up to `ULift`) needs a semantic decision.
  It is recorded as a lead, not adopted.

REFERENCE_COHERENCE is a question of its own (a single-level occurrence against a two-level R2F
reading). Entry 8 also listed `test-multi-instance` with 9 checks; the suite has 8.

### (4) Backlog

`RULE_BACKLOG.{md,json}` was regenerated from `st-corpus-SPLIT2` with the corrected family notes:
* COUPLED_BINDER_LEVELS: R-SPLIT implemented, not merged;
* STATEMENT_FREE_LEVEL_PINNED: re-diagnosed;
* REFERENCE_COHERENCE and RESIDUAL_STATEMENT_LEVELS: the `pcancel` attribution withdrawn.

Next, pending decisions:
* review and merge of R-SPLIT;
* a semantic decision on result-sort-only reference levels (STATEMENT_FREE_LEVEL_PINNED, 885 affected).

### (5) Regressions and validation

* `test-level-split` (new): 18 checks.
  * Validated fixture: `pR`, `fun_R` and `pR_tail` split; `pR_intro` and `fun_R_id` accepted; `qR`
    and `gR` not split; `qR_intro` still refused.
  * Negative controls, each kernel-accepted and then rejected:
    * forged split of the ineligible `gR`, reported and hidden: audit;
    * copies exchanged between binders: consumer and audit;
    * a degenerate split: consumer and audit;
    * statement narrowed to the diagonal: audit.
  * Positive control at off-diagonal nonzero universes.
  * Correspondence proofs: 8 declarations, no axioms.
* `test-universe-r2`: 9. Its `pairR_intro` check now expects acceptance through `pairR`'s split; the
  refusal case moved to `qR_intro`.
* Other suites: `test-statement` 30, `test-assembly` 34, `test-termination` 22, `test-opaque` 16,
  `test-universe-c` 22, `test-multi-instance` 8, `test-provenance` 5: all OK.
* `test-all`: 18/18 (`a28c4b3`).

### (6) Commands and evidence

As in entry 8, with `runs/st-corpus-SPLIT2`.

Evidence:
* `coverage/{SPLIT2,transitions-R3-to-SPLIT2}.json`;
* `RULE_BACKLOG.{md,json}`;
* `provenance/CORPUS_MANIFEST.json` (current: SPLIT2; `-R3` kept);
* `termination/CONVERSION_DEPENDENCE-SPLIT2.json`;
* `test_level_split.json`.

## Entry 10 — R3G-F (result-sort-only levels) and the P2 retry tier for definitions (2026-10-14)

Branch `rules-rsonly`, from `main` `679dd59`. The validated implementation is `6fe8890` (commits
`6ff07a7` `dd0deec` `c77696c` `2200033` `48a8ec3` `6fe8890`); it was reviewed and merged into `main`.

Corpus run worktree `r2l-run-RS4`, run `runs/st-corpus-RS4`. Inputs:
* the A′ export, with its chunk evidence reused;
* the merged source is byte-identical to R-SPLIT's (`8eaf2da4…`);
* the exporter plugin is byte-identical (`44a8c6ac…`).

The statement suites and test-all ran in the frozen worktree `r2l-B-test` at `6fe8890`. Design:
`docs/RESULT_SORT_LEVELS.md`.

### (1) Diagnosis: the STATEMENT_FREE_LEVEL_PINNED members are two cases

The 356 pinned rows of the R-SPLIT run were classified by where the pinned level occurs in the
referenced declaration's source (by occurrence paths; scripts and `pin_classes.json` in
`reports/statement_only/rsonly/`).

| Case | Rows | Pinned level | Mechanism |
|---|---|---|---|
| **A: result-sort-only** | 280 | `hasDecEq.axioms_` `eqtype.32` (144); `hasChoice.axioms_` `choice.299` (136) | R3″ fixed it to 0 inside the class records' fields (`Equality.axioms_.Class : hasDecEq.axioms_.{u51, 0} T → …`), so a statement holding a mixin at its own level unified it to 0 |
| **B: a structure's carrier (a field sort)** | 58 + 18 | `Equality.type` 51, `Countable.type` 959, `Choice.type` 333, `JobType`/`TaskType` | A concrete instance (`nat_eqType` packs `Nat : Type 0`) coupled to a generic one through one carrier level (`prod_eqType SporadicTask nat_eqType`) |

Reproducers:
* Case A: the corpus obligation `Builders_32.HB_unnamed_factory_34` obligation 5, and the fixture
  `SF.Rs.unify_like` (pre-change result in `rsonly/pre_fixture_report.json`).
* Case B: the Classic `fp_rta_comp` statements.

Protected paths (frontier of the R-SPLIT run):
* 749 roots are blocked by B (`HB_unnamed_mixin_107` obligations 2/4/8, `Countable.type`'s carrier) and
  by two solution-fact rows (`eqtype.insub`, `fintype.HB_unnamed_factory_57`);
* 62 roots are blocked by B alone;
* case A lies on the frontier of 79 roots, all also blocked by B, solution facts or kernel failures.

**Correction to entry 9:** "280 of 340 members pin the result-sort-only level" holds, but those rows
are not on the protected paths alone; B is.

### (2) What was changed: two separate mechanisms

**R3G-F (case A).** A level metavariable qualifies when:
* it occurs only in the constructor fields of a non-template single-body block;
* at every reference it is the argument for a level `l` that is result-sort-only in the referenced
  declaration;
* the native facts bound `l` by a level of the block's result sort.

Such an `l` becomes an implicit universe parameter of the block. Three refinements were needed:
* **Minimal reading.** `ι l = u_l`: the lower bounds of `l` are omitted, as for R-SPLIT's copies; the
  levels above it are still raised.
* **Scope.** A level is read minimally only where it is implicit, and only for R3G-F levels of the
  declaration's own **dependency closure**.
* **Applicability at constants.** A level also counts at a reference to a constant (for example a
  projection) when it is in that constant's closure and not in its own source.

There is no lifting and no transport: the previous translation is the instance `u_l := 0`.

Independent checks:
* **Audit** (`check_result_sort_implicit`, `result_only_levels`, `RS_CLOSURE`, `ro_of`, minimal
  `own_level_interp`) re-derives every condition from the source.
* **Consumer** (`resultImplicitOk`): no binder range mentions the parameter, and no constructor type
  has it as a sort.

**P2 retry tier for definitions (a coherence-family mechanism, not part of R3G-F).**
* A definition accepted only with defaulted levels is retried with the statement-mode joint
  identification and the M6 bounded solver.
* The retry is kept only if it is accepted with fewer defaults and every added parameter occurs in the
  type.
* Reproducer: fixture `pr1`, MathComp `eqtype.pred1`'s shape.

### (3) Coverage — FULL CORPUS, same 4,474 protected roots (validated)

| Run | Impl | Accepted | Audited Pending | Blocked | Direct Failure | Notes |
|---|---|---|---|---|---|---|
| R-SPLIT baseline (entry 9) | `a28c4b3` | 673 | 2,177 | 1,518 | 106 | |
| R3G-F v1 | `6ff07a7` | 549 | 593 | 3,128 | 204 | validated; 1,708 protected genuine regressions (R2F `max` readings at references); not adopted |
| R3G-F v2 | `c77696c` | – | – | – | – | superseded mid-run (value-only parameters found); not measured |
| R3G-F v3 | `2200033` | 673 | 1,645 | 2,075 | 81 | validated; one direct regression, protected `ProcessorState`, from global order-dependent minimality |
| **R3G-F + P2 retry tier (v4)** | **`6fe8890`** | **673** | **2,180** | **1,518** | **103** | **merged** |
| R3G-F only (ablation of v4) | `6fe8890` with the retry tier disabled | 673 | 2,177 | 1,518 | 106 | measurement patch, not committed |

* **v4 by family:** modern 446 / 1,281 / 743 / 34; Classic 227 / 899 / 775 / 69 (Classic unchanged).
* **v4 checks:** consumer, audit, source instances (4) and provenance (`CORPUS_PROVENANCE_BOUND`) are
  all OK.
* **Ablation:** consumer and audit OK.

**Attribution.**
* **R3G-F solves 276 internal rows** (all case-A pins: 144 `hasDecEq.axioms_`, 132
  `hasChoice.axioms_`; 4 case-A rows remain) **and adds zero protected roots independently**: the
  ablation's protected coverage equals the baseline.
* **The P2 retry tier for definitions is responsible for the three newly supported protected roots**,
  all previously refused by coherence (REFERENCE_COHERENCE). With the tier disabled, nothing else is
  claimed or lost. The three roots:
  * `prosa.analysis.facts.delay_propagation.propagated_arrival_curve_valid`;
  * `prosa.analysis.facts.delay_propagation.propagated_arrival_curve_respected`;
  * `prosa.analysis.abstract.restricted_supply.task_intra_interference_bound.instantiated_task_intra_interference_is_bounded`.

**Protected transitions (baseline → v4):**
* newly Audited Pending: 3 (above);
* newly Accepted: 0;
* unchanged: 4,471;
* genuine regressions: 0;
* old false acceptances corrected: 0 (none found).

**All rows (10,970):**
* claimed rows go from 4,143 to 4,422 (+279); 0 claimed rows lost; no accepted row became pending;
* direct failures (backlog census) go from 741 to 462;
* 25 rows carry R3G-F levels; 13 definitions used the retry tier;
* newly supported external dependencies: 276 MathComp rows (`mathcomp.boot` 224, `mathcomp.order` 52),
  all proof-task statements or their definitions; the other 3 gained rows are the Prosa protected roots
  above.

**Prerequisite / assembly readiness.**
* Proof tasks: 2,161 → 2,440.
* Statements with no prerequisites: 626 → 902.
* Statements with prerequisites: 1,535 → 1,538 (the 3 protected roots).
* Pending definitions: 965, unchanged.
* No existing pending row's prerequisite set changed.

### (4) Remaining blockers on the selected paths (v4)

* **749 roots: case B plus solution facts.**
  * `HB_unnamed_mixin_107` obligations 2, 4, 8 pin `Countable.type`'s carrier 959.
  * `eqtype.insub`: `SubType.sort` identifies `SubType`'s parameter level 573 with its sort field 577
    under R2F; `Sub` fixes 573 to 0 by R2B-P; this forces 695 to 0 against `Set < 695`.
  * `fintype.HB_unnamed_factory_57`: 551 is solved to 0 against `ssrbool.1169 ≤ 551`.
  * Both solution-fact rows are structure-carrier couplings.
* **62 roots:** case B alone.
* **4 case-A rows** (`Builders_62.HB_unnamed_factory_64` obligations 3/7/10/14): the mixin level is
  identified with another statement level, `u_order_15972`; C-1 correctly refuses them.
* **Independent blockers of comparable size:** coherence (`ideal.processor_state`, 225 roots alone)
  and `JobReady` (212).

**Case B needs a representation decision (not implemented).** The options:
1. lifted carriers of concrete instances, with transport at every use of `sort`;
2. per-operand carrier levels for structure operations, an R-SPLIT-style extension.

### (5) Process corrections in this round

* A suite run in the dev tree while the implementation was being edited is invalid. Suites now run in
  the frozen worktree `r2l-B-test` at a pinned commit.
* Direct translations without the run's contract skip the protection binding: protected-range
  refusals are invisible there. Only CLI runs bound to the contract, and corpus runs, are
  authoritative.

### (6) Regressions and validation (`6fe8890`, frozen worktree)

* `test-result-sort` (new): 15 checks.
  * Fixture `stmt/rs` plus the real `Equality` structures and corpus obligation 5.
  * Positive controls: projections (`getop`), dependent elimination (`pack_eta`), a constructed
    instance (`mk_op`), and instantiation at nonzero universes.
  * Negative controls, each kernel-accepted, then rejected:
    * a carrier claimed as result-sort-only: audit and consumer;
    * a field at a level that is not its interpretation: audit;
    * a carrier range raised by the new level: audit and consumer;
    * a dependent use narrowed: audit.
* `test-universe-c`: 22. Its expectations now read `Equality.type`'s parameters from its row (four
  levels: 32, 51, 55, 58) instead of listing two; the conditions are unchanged (generic, none
  defaulted, narrowing rejected, nonzero positive control, discrimination).
* Other suites: `test-statement` 30, `test-assembly` 34, `test-termination` 22, `test-opaque` 16,
  `test-universe-r2` 9, `test-multi-instance` 8, `test-level-split` 18, `test-provenance` 5.
* **`test-all`: 18/18.**

### (7) Commands and evidence

As entry 9, with `runs/st-corpus-RS4` (and `runs/st-corpus-RS4abl` for the ablation).

Evidence:
* `coverage/{RS4,RS4abl,transitions-SPLIT2-to-RS4,transitions-SPLIT2-to-RS4abl}.json`;
* `RULE_BACKLOG.{md,json}`;
* `provenance/CORPUS_MANIFEST.json` (current: RS4; `-SPLIT2` kept);
* `termination/CONVERSION_DEPENDENCE-RS4.json`;
* `rsonly/`;
* `test_result_sort.json` and the other test reports from the frozen run.

---

## Entry 11 — R-CARRIER (case B, Option 2): per-operand carrier universe levels (2026-10-15)

Branch `rules-carrier`, from `main` `f9c9073` (plus the local `CLAUDE.md` commit `0120f56`). Commits:
`bb1840d` `d462a93` `202de49` `326033f` `dda0a2a` `a29cfbc` `eefad94` `775f1d4` `ee4e779` `58996a3`.
**Experimental, not merged or pushed: pending review.** Design: `docs/CARRIER_LEVELS.md`.

Corpus run worktrees:
* `r2l-run-CB2` (implementation `775f1d4`) and `r2l-run-CB3` (implementation `ee4e779`);
* the merged source is byte-identical to RS4's (`8eaf2da4…`);
* the exporter plugin is byte-identical (`44a8c6ac…`).

The suites ran in the frozen worktree `r2l-B-test`.

### (1) Diagnosis (real exporter, fixture `fixtures/stmt/cb`)

Case B and the two solution-fact rows on the 749-root path were reproduced with the real MathComp
declarations (`reports/statement_only/carrier/pre_fixture_report.json`).

| Row | Mechanism |
|---|---|
| `prod_eqType T nat_eqType` (Classic `fp_rta_comp`) | one parameter `u_51` named the two operands' free carrier classes; `nat_eqType` (carrier `Nat : Type 0`) pinned the generic operand at 0 |
| `HB_unnamed_mixin_107` obligations 2/4/8 | `Countable.type`'s carrier 959 pinned through `SubType` (next row) |
| `eqtype.insub` | R2F read `SubType`'s parameter carrier 573 as `max(u573, u577)` (fact `577 ≤ 573`); `SubType.sort` identified the carriers and `Sub` pinned both at 0 |
| `fintype.HB_unnamed_factory_57` | **not a carrier coupling**: 551 is the motive level of `isSub`'s `Sub_rect` (542; `551 = 542` in the source). A statement class containing a proof-local own level was represented by it and never named, so 551 was defaulted to 0 |

**Correction to entry 10:** `factory_57` was grouped with the structure-carrier couplings. It is a
separate mechanism (P3 below).

### (2) What was changed

All parts are derived from the source and from typing; there are no names and no whitelists.
* **P1:** a block's parameter carrier is not raised by its own block's other levels. These pairs are
  `Split.decoupledPairs` in the translator and `DECOUPLED` in the audit.
* **P2:** the distinct free classes of an implicit level in a declaration's type (a statement's
  statement) are named as copies `l__c<k>`, which lie below `l` and inherit its upper bounds.
  References read every copy as `l`, and the report field `level_copies` lists them.
* **P3:** in statement mode only own *type* levels represent a class. A proof-local level is solved
  and checked by R2S.

There is no lifting: no `ULift` occurs anywhere, and `nat_eqType`'s carrier stays `Nat`.

Refinements found on the corpus:
1. P2 classes are counted without the generated prerequisite-hypothesis binders.
2. A post-pass merges stale and dangling copies.
3. A copy position skips the shared-level coherence rule, but not R3.
4. Owning a copy means owning the level in the generality check.
5. **(new in this round, `ee4e779`)** In the generality check, an argument `max(u_a, …)` of own
   parameters for a referenced level `l` is accepted when every summand is *equal* to `l` in the
   source graph (≤ both ways). It is `l`'s reading, not a specialization. Implemented in the
   translator (`freeLevelRef`) and in the audit (`check_statement_generality`).

Codex workers:
* `taskcost` diagnosed and proposed refinement 1;
* `corr` wrote the correspondence proofs.

Both were reviewed and rerun here.

### (3) Independent checks and controls

* **Audit:** `carrier_levels`, `DECOUPLED`, the `level_copies` pre-pass (fresh, implicit, occurring),
  copies registered with R-SPLIT's copy map, `GEN_COPY_POS` coherence and the generality refinements.
* **Consumer:** each copy is a universe parameter occurring in the type (for a statement, in its
  statement).
* **`test-carrier`: 20 checks.**
  * Fixed rows and the representation checks.
  * Negative controls:
    * accidental pinning: kernel-accepted, audit-rejected;
    * incorrect identification (a structure copy relabelled as a carrier copy): kernel-accepted,
      audit-rejected;
    * splitting the genuine dependency `prod_same`: rejected by the kernel;
    * P1 coupling restored on `subT`: kernel-accepted, audit-rejected.
  * Positive control at mixed nonzero universes.
  * 17 axiom-free synthetic correspondence proofs (equality and `insub`).
  * **New:** refinement-5 controls. `max(u_a, u_b)` is accepted only for source-equal levels; it is
    rejected when a summand is only below `l`, carries an offset, or is not an own level.

### (4) Coverage — FULL CORPUS, same 4,474 protected roots

| Run | Impl | Accepted | Audited Pending | Blocked | Direct Failure | Notes |
|---|---|---|---|---|---|---|
| RS4 baseline (entry 10, `main`) | `6fe8890` | 673 | 2,180 | 1,518 | 103 | |
| corpus run 1 | `326033f` | – | – | – | – | not validated: stale copies; 61 rows lost to the five mechanisms fixed by refinements 1–4 and the narrowed P1; not adopted |
| **CB2** | **`775f1d4`** | **673** | **2,257** | **1,499** | **45** | validated |
| **CB3** | **`ee4e779`** | **673** | **2,260** | **1,494** | **47** | validated |

**CB3 by family:** modern 446 / 1,281 / 743 / 34 (unchanged from RS4); Classic 227 / 979 / 751 / 13.

**Checks (CB2 and CB3):** consumer, audit, source instances, `CORPUS_PROVENANCE_BOUND` (10,966
declarations) and the conversion dependence are all OK.

**Protected transitions:**
* RS4 → CB2: 77 newly Audited Pending (all Classic); 0 regressions; 0 old false acceptances.
* CB2 → CB3:
  * 3 newly Audited Pending: Classic `Affinity.affinity`, `task_affinity` and `is_subaffinity`;
  * 2 moved from Blocked to Direct Failure: `ConcreteTask.concrete_task` (a protected-range refusal)
    and `Affinity.can_execute_on` (coherence). Their dependencies now translate, exposing their own
    refusals; they were not claimed before;
  * 0 regressions; 0 old false acceptances.

**All rows (10,970):**
* claimed rows: RS4 4,422 → CB2 4,532 (+110) → CB3 4,583 (+51);
* **0 claimed rows lost in either step**;
* rows with level copies: 887;
* proof tasks: 2,440 → 2,524 → 2,551.

**Reported separately** (`carrier/case_b_status.json`):

| Row | RS4 | CB2 | CB3 |
|---|---|---|---|
| case B, Classic `fp_claimed_bounds_gt_zero` (basic and jitter) | refused | **claimed** | claimed |
| `HB_unnamed_mixin_107` and obligations 2/4/8 (Countable carrier) | refused/blocked | **claimed** | claimed |
| `eqtype.insub` | refused | **claimed** | claimed |
| `fintype.HB_unnamed_factory_57` | refused | **claimed** (`551 := u542`) | claimed |
| `choice.HB_unnamed_mixin_109` obligation 13 | blocked | refused (equal-level `max`) | **claimed** (refinement 5) |
| `choice.HB_unnamed_factory_165` obligation 1 | refused | refused | **claimed** |
| ideal `processor_state` | refused | refused (coherence) | refused (coherence) |

**The 749/761-root group (STATEMENT_FREE_LEVEL_PINNED only; 744 Classic, 17 modern) is not
unblocked.**
* Its frontier moved twice:
  * RS4: `mixin_107` and the solution-fact rows;
  * CB2: `mixin_109` obligation 13, blocking 751 roots;
  * CB3: `fintype.HB_unnamed_factory_66` obligation 1, blocking 712 roots.
* In CB3, 3 of these roots are claimed, 746 are blocked and 12 are refused.

### (5) Remaining blockers on the selected paths (CB3)

* **`factory_66` obligation 1** (712 roots of the group): `ord_enum`'s level `ssrbool.1169` (ordinal's
  sort) reaches the statement at 0. Cause, upstream:
  * `choice.eqtype_sub_type__canonical__choice_Countable` (not protected) is accepted only on the R3↓
    tier, with 4 defaulted levels;
  * its plain tiers fail the shared-level coherence rule on R2F `max` readings: `Countable`'s class
    level 968 is read `max(299, 938, 965, 1, 968, 32)`;
  * the specialization then flows through `factory_59` and `mixin_63` to `ordinal.{0}`.

  This is the REFERENCE_COHERENCE mechanism.
* **REFERENCE_COHERENCE** (213 roots alone; ideal `processor_state` and 9 others): a shared monomorphic
  level, such as `Equality`'s class level 58, gets a concrete instance's R2F reading (unit's eqType:
  `max(u32+1, u55, 1)`) in a prerequisite-hypothesis type, where coherence demands `u_58`. The R3↓
  tiers then narrow `Job`'s carrier: refused, correctly.
* **PROTECTED_RANGE_NARROWED** (227; `JobReady`, `concrete_job`, `SystemEvolutions`, `concrete_task`).
* **R2F readings of source-equal levels** (`docs/CARRIER_LEVELS.md` §5). In the corpus-wide facts one
  class of 232 levels is mutually equal; it includes `eqtype.51`, `choice.959`, `eqtype.577`,
  `ssrbool.1169` and `fintype.101`. Two repairs were measured on corpus subsets and **not kept**:
  * one parameter per source-equal class (R2F-eq): 8 protected `schedule`/`service` rows lost;
  * identifying `max` summands of equal levels at uses (P4): protected `service_during` lost.

  Both merged independent Prosa carriers.

Each of these needs a decision on the coherence rule or a new representation; that decision is the user's (a proposal follows this entry, not yet adopted).

### (6) Process corrections in this round

* **Corpus run 1.** P1 was broad (every carrier minimal everywhere), and P2 counted hypothesis binders.
  The run lost 61 rows, `task_T`, `TaskCost` and `is_idle_iff` among them. P1 was narrowed and
  refinements 1–4 were added; CB2 lost 0 rows.
* **`test-universe-c`.** It expected ideal `processor_state` to be claimed (`dda0a2a`), which held only
  under the broad P1. At `775f1d4` it failed (1/22). The check now states the actual result: refused,
  never claimed narrowed, now by the coherence rule (`ee4e779`; 22/22).
* **Ablations.** Ablations run without the run's contract skip protection. Only CLI and corpus-subset
  translations through `statement_run` are used as evidence.

### (7) Regressions and validation

* **At `ee4e779` (frozen worktree):**
  * `test-statement` 30, `test-termination` 22, `test-assembly` 34, `test-opaque` 16;
  * `test-universe-c` 22, `test-universe-r2` 9, `test-multi-instance` 8;
  * `test-level-split` 18, `test-result-sort` 15, `test-carrier` 19, `test-provenance` 5;
  * **`test-all`: 18/18.**
* **At `58996a3`:** `test-carrier` 20 (adds the refinement-5 controls; test-only commit).
* **Corpus:** 0 claimed rows lost; 0 protected regressions; validated.

### (8) Commands and evidence

As entry 10, with `runs/st-corpus-CB2` and `runs/st-corpus-CB3`. Corpus subsets for the diagnoses:
`STATEMENT_RUN=<corpus run> python3 -I inventory/statement_run.py subset ROOT out/source.ndjson`, then
`statement_run.py translate` and `check` (protection-bound).

Evidence:
* `coverage/{CB2,CB3,transitions-RS4-to-CB2,transitions-CB2-to-CB3}.json`;
* `RULE_BACKLOG.{md,json}` (regenerated from CB3);
* `PROOF_TASKS.jsonl` (CB3);
* `provenance/CORPUS_MANIFEST.json` (CB3; `-CB2` and `-RS4` kept);
* `termination/CONVERSION_DEPENDENCE{,-CB2,-CB3}.json`;
* `carrier/{pre_fixture_report,case_b_status}.json`;
* the `test_*.json` reports from the frozen runs.

### (9) Proposal awaiting a decision: coherence modulo an R2F reading (measured, NOT adopted)

A measurement only. The experiment patch is kept as `r2l-run-CR/EXP_COHERENCE_R.patch`; it is off
by default (`R2L_EXP_READ`) and is not on this branch.

**Rule R.** At a reference, consider an argument for a source level `l` that is *shared* with the
referring declaration. Today it must be exactly `u_l`. Under R it may also be
`max(u_l, s₁, …)`, provided each other summand passes R3 (`m + k ≤ l` and `Set + c ≤ l` are entailed
by the source graph). At every model of the source facts this argument equals `l`. That is the
justification already used for R2F readings: the referring declaration keeps `u_l` as a parameter,
so nothing is narrowed. The translator (`checkInstantiation`) and the audit (`check_universe_args`)
implement it independently.

**Corpus `r2l-run-CR`** (impl `c77dd68` + patch; validated: consumer, audit with the rule, source
instances and `CORPUS_PROVENANCE_BOUND` all OK):

| | Accepted | Audited Pending | Blocked | Direct Failure |
|---|---|---|---|---|
| CB3 | 673 | 2,260 | 1,494 | 47 |
| CB3 + R | 673 | **2,834** | **933** | **34** |

**By family:** modern 446 / 1,302 / 736 / 20; Classic 227 / 1,532 / 197 / 14.

**Protected transitions:** 575 newly supported (554 Classic, 21 modern), 3 moved between unclaimed
categories, **1 genuine regression**.
* The regression is Classic `Affinity.task_affinity`. Its dependencies become more general under R
  (`eqtype_sub_type` Countable instance: 13 → 19 parameters, 4 → 0 defaulted levels), which exposes a
  concrete instance at its own shared carrier level 51 in its body. Coherence then refuses it, as for
  `processor_state`.

**All rows:** 589 gained, 1 lost (the same row); no accepted row became pending.

STATEMENT_FREE_LEVEL_PINNED falls to 6 members (3 roots alone). The `factory_66` chain is fixed.

**Not addressed by R:** the remaining REFERENCE_COHERENCE family (7 members, 355 roots alone), with
ideal `processor_state` and `task_affinity` among them.
* There, a concrete instance in the *body* (unit's finType, carrier 0) references a level that the
  declaration shares with its binder (`Job`'s carrier 51).
* References to shared levels use one level variable ("coherence by construction"), so the instance
  pins `Job`'s carrier; the protection check refuses that.
* Handling it needs per-occurrence instantiation of shared levels in bodies (a P2-like split of own
  levels), which is a further representation decision.
* A second variant measured on subsets (H: copy semantics at prerequisite-statement hypotheses) gained
  nothing on its own.

## Entry 12 — Rules R and H: shared-level coherence modulo an R2F reading; prerequisite instances (2026-10-15)

Request: merge case B and push; adopt rule R (entry 11 §9) with an independent audit, negative
controls and full regression testing; investigate and fix the `Affinity.task_affinity` regression.
Then find the next blocker family by measurement. Branch `rules-coherence`, from `main` = `74ca20b`
(case B, merged and pushed at the start of this round).

### (1) What was changed

* **Rule R** (`b915360`, `docs/COHERENCE_READINGS.md` §1–4). At a reference, an argument for a shared
  level `l` may be `max (u_l, s₁, …)` when every other summand passes R3 (no raising). This is not
  allowed for motive-level (R8) or proof-local levels.
  * Translator: `checkInstantiation`. Audit: `check_universe_args`.
  * It is always on; the experiment's environment flags were removed.
* **Rule H** (`892699a`, §5). At a reference to a proof task's statement (the type of a generated
  prerequisite hypothesis), an argument for a shared level may lie below it. This is R3↓, on every
  tier.
  * Translator: `GEnv.leafStmtTargets`, filled where `leafStmt` is registered.
  * Audit: `HYP_STATEMENTS`, derived from the source's proof tasks (`is_leaf` plus the generated
    statements) under both target namings.
* **Task rendering** (`2e46cbf`): the heartbeat limit applies per task. Before, it applied to the
  whole `#rocq2lean_render_tasks` command, and 3,186 tasks exceeded it in run RH. Translation and
  checks are unchanged.

### (2) The `task_affinity` regression (diagnosis and fix)

`Affinity.task_affinity (T : eqType) (n : nat) := T -> affinity n` shares `eqtype.51` with its
binder `T`.
* `affinity`'s prerequisite hypothesis `inj_eqAxiom`'s obligation 1 is used at `nat_eqType`, whose
  carrier is 0. `task_affinity` inherits that hypothesis at `…, 0, …`, and coherence refused the plain
  tiers.
* On the R3↓ tier, `T`'s carrier was solved to 0: a narrowing, refused for this protected definition.
* Under R the dependency chain became general, which exposed this; before R it was specialized
  enough to hide it.
* H accepts the hypothesis instance (R3-checked). The fixture `task_ord_affinity` reproduces the
  shape: without H it is accepted only on R3↓ with `T : Equality.type.{…, 0, …}`; with H it is on a
  plain tier with `u_51`.

### (3) Independent checks and controls

* `scripts/test-coherence` (16 checks; fixture `fixtures/stmt/coh`: real exporter, real MathComp
  declarations, synthetic statements):
  * Positive: the `choice` sub-type Countable instance has no defaulted level, and its references
    read 299 as `max (u_299, u_577)`. `factory_66`, its obligation 1, `ord_pickle_refl` and
    `sub_pickle_refl` are claimed. Before R (checked at `74ca20b`), the obligation was refused and
    the others blocked.
  * Negative forged rows, audit-rejected (the kernel rejected the forged rows too):
    * `max (u_299, u_1007)`, which raises;
    * `u_577` for the shared 299 on a plain tier, which specializes.
  * Rule H: `task_ord_affinity` as above. Its hypotheses forged at `u_51 + 1` (raising) are
    audit-rejected.
  * Unit controls on the audit:
    * R: readings accepted; rejected are a raising summand, an offset, `Set + 2`, `u_l + 1`, no `u_l`
      summand, a motive level and a proof-local level;
    * H: a lower argument is accepted at a statement only; raising and offset arguments are rejected
      there.
* `tests/smoke/UniverseRules.lean`: the same R cases as `#guard`s on the translator's
  `checkInstantiation`.

### (4) Coverage — FULL CORPUS, same 4,474 protected roots

| Run | Impl | Accepted | Audited Pending | Blocked | Direct Failure |
|---|---|---|---|---|---|
| CB3 (entry 11) | `ee4e779` | 673 | 2,260 | 1,494 | 47 |
| RR (R) | `b915360` | 673 | 2,834 | 933 | 34 |
| RH (R + H) | `892699a` | 673 | 2,983 | 785 | 33 |
| **RH2 (R + H + task fix)** | `2e46cbf` | **673** | **2,983** | **785** | **33** |

All four runs were validated: consumer, audit, source instances (R2B-P), `CORPUS_PROVENANCE_BOUND`
and conversion dependence. RH's task rendering failed, which is the fix in `2e46cbf`; RH2 renders
3,156 tasks.

**Protected transitions:**

| Transition | Newly supported | Classic | Genuine regressions | Moved between unclaimed categories |
|---|---|---|---|---|
| CB3 → RH2 | 723 | 702 | 0 | 2 |
| CB3 → RR | 575 | — | 1 (`task_affinity`) | — |
| RR → RH2 | 149 | 149 | 0 | — |

**All rows (10,966):**

| Transition | Claimed gained | Claimed lost |
|---|---|---|
| CB3 → RH2 | 737 | 0 |
| CB3 → RR | 589 | 1 |
| RR → RH2 | 149 | 0 |

Old false acceptances: 0.

### (5) Remaining blockers (RH2 backlog)

818 protected roots are unclaimed (756 modern, 62 Classic). REFERENCE_COHERENCE no longer occurs.

| Family | Members | Roots affected | Roots blocked by it alone |
|---|---|---|---|
| PROTECTED_RANGE_NARROWED | 11 | 623 | 597 |
| SOLUTION_FACT_VIOLATED | 312 | 139 | 11 |
| PROP_TYPE_CUMULATIVITY | 10 | 82 | 1 |

Measured on the dependency frontier of the unclaimed protected roots, PROTECTED_RANGE_NARROWED has
two mechanisms:

* **(a)** `JobType`'s carrier 51 pinned to 0: the processor-state instances (`ideal.processor_state`
  and 5 more), plus `schedule_up_to`. 280 roots have `processor_state` on their frontier.
  * `ProcessorState`'s parameter `Job` and field `Core` get the R2F reading `max (u51, u101)`, because
    51 and 101 are mutually equal in the source graph.
  * A concrete `Core := unit` therefore pins `Job`'s carrier.
* **(b)** `JobType`'s level 32 pinned to 0: `JobReady`, `SystemEvolutions`, `concrete_job`. 332 roots
  have `JobReady` on their frontier.
  * Upstream, the protected `schedule` was accepted with its result-sort level 22 *solved* to
    `max (u51, u101)`. The source has only `51 ≤ 22`, so this ties `PState`'s `State` universe to the
    job carrier.
  * Cause: coherence by construction makes the declared sort `?22` and `ProcessorState`'s reading
    `max (?22, ?51, ?101)` one cyclic equation, which the bounded solver settles at `max (51, 101)`.
  * Both checks (R2S facts and generality) accept this solution, because typing forced it under the
    single-variable representation.

Stage 3 (per-occurrence shared levels) is in progress on branch `rules-occurrence`. It is not
adopted and is measured separately (entry 13).

### (6) Process corrections in this round

* The frozen suite worktree `r2l-B-test` held a copied fixture (from the pre-change baseline check
  of `fixtures/stmt/coh` at `74ca20b`) that blocked the checkout. That first suite job was stopped
  and the tree cleaned before the recorded runs. Baselines are now taken only in throwaway
  directories.
* A `pkill -f` pattern matched the shell running it. Jobs are now stopped by PID.
* Pushes over SSH stall in the machine's proxy (fake-IP TUN routing of `github.com`); the push
  output is authoritative. Memory note `github-push-proxy`.

### (7) Regressions and validation

* Frozen worktree `r2l-B-test`:

  | Commit | Statement suites | `test-all` |
  |---|---|---|
  | `b915360` | all 12 pass (`test-coherence` 12) | 18/18 |
  | `892699a` | all 12 pass (`test-coherence` 16) | 18/18 |
  | `2e46cbf` | all 12 pass | 18/18 |

  The statement suites are `test-statement` 30, `test-termination` 22, `test-assembly` 34,
  `test-opaque` 16, `test-universe-c` 22, `test-universe-r2` 9, `test-multi-instance` 8,
  `test-level-split` 18, `test-result-sort` 15, `test-carrier` 20, `test-coherence` and
  `test-provenance` 5. The reports in `reports/statement_only/test_*.json` and
  `reports/test_all.json` are from the `2e46cbf` run.
* Corpus as in (4). No protected regression in RH or RH2.

### (8) Commands and evidence

Corpus runs in frozen worktrees `r2l-run-RR`, `r2l-run-RH` and `r2l-run-RH2`, as in entry 11
(`statement_run.py merge / translate / check / instances / tasks`, `conversion_deps.py`,
`coverage_delta.py snapshot`, `statement_provenance.py manifest / check`, `c1_transitions.py`,
`rule_backlog.py`).

Evidence:
* `coverage/{RR,RH,RH2}.json`;
* `coverage/transitions-CB3-to-{RR,RH2}.json` and `coverage/transitions-RR-to-RH2.json`;
* `RULE_BACKLOG.{md,json}` and `PROOF_TASKS.jsonl` (RH2);
* `provenance/CORPUS_MANIFEST.json` (RH2; `-CB3` kept);
* `termination/CONVERSION_DEPENDENCE{,-RH2}.json`;
* `test_coherence.json` and the other frozen-suite reports.

## Entry 13 — Stage 3: coherence by unification (shared levels per occurrence) (2026-10-15)

Request: identify the mechanism that unblocks the most protected roots on the full-corpus dependency
frontier after rules R and H, and design, implement and validate a general solution. Branch
`rules-occurrence`, from `main` = `28c477a`; one squashed commit (tree identical to the measured
`2c78107`). Rule document: `docs/COHERENCE_READINGS.md` §6.

### (1) Measured frontier (RH2) and diagnosis

PROTECTED_RANGE_NARROWED was the largest family: 11 members, 597 roots blocked by it alone. On the
frontier of the 818 unclaimed protected roots, its members split into:
* `JobReady` (332 roots) and `ideal.processor_state` (280), with 144 roots needing both;
* `concrete_job` (48), `concrete_task` (36) and `SystemEvolutions` (19).

All of them were coherence *by construction*: every reference to a shared level used the
declaration's one level variable. Three shapes:

* **`JobType := Equality.type`** reads its level 58 as `max (u32, u51+1, u55, u58)`.
  * `Equality.sort Job` needs that reading at its 58 position, while the binder has `u58`.
  * Every plain attempt was ill-typed: the kernel reported an application type mismatch, from
    `?58 =?= max (…, ?58)`.
* **`schedule`**: the declared result sort `?22` had to equal `ProcessorState`'s reading
  `max (?22, ?51, ?101)`.
  * The bounded solver chose `22 := max (51, 101)`. The source has only `51 ≤ 22`, so `PState`'s
    `State` universe was tied to the job carrier.
  * Both checks accepted this because typing forced it. `JobReady` inherited the narrowing.
* **`ProcessorState`**: its R2F interpretation read `Job`'s and `Core`'s carriers both as
  `max (u51, u101)`, because 51 and 101 are mutually equal in the source graph.
  * `Core := unit` therefore pinned `Job`'s carrier.
  * The plain attempt failed only through the first shape.

### (2) What was changed (§6 of the rule document)

1. **Per-occurrence shared levels** (new retry tier).
   * Every reference to a level shared with the declaration takes its own level metavariable,
     including universe-polymorphic instance levels on the stage-4 branch only.
   * After `solveLevels` has unified the value's type with the declared type, the free ones are bound
     back to the declaration's own variable (`rebindShared`).
   * A level that typing solved through one of its own occurrences becomes its parameter. It is then
     booked as *interpreted*, and its solution must equal its R2F reading exactly
     (`ownLevelInterp`), or the tier is refused.
   * Constants try the tier after the strict tiers. Blocks try plain parameters per occurrence before
     R2F (M6's order).
2. **Blocks with plain parameters per occurrence**: the arity's final sort is read through R2F
   (`sort_interp`, reported). The audit recomputes the R2F image for that sort and checks every other
   part of the arity with plain levels (`split_sort_interp`).
3. **Generality retry for definitions**: a definition accepted with an own type level solved by typing
   is retried per occurrence. The retry is kept only if it has fewer solved type levels and no more
   defaults.
4. **Discovery modulo readings** (blocks):
   * a metavariable summand of an arity argument `max (?x, …)` is a candidate for its source level;
   * prerequisite statements (rule H) decide no class.
5. **Rule R in its general form**: equality at every model of the source facts. This is
   `equalAtModels` in the translator and `equal_at_models` in the audit, implemented independently.
   It applies to:
   * the argument for a shared level;
   * the argument for a solved or interpreted own level;
   * generality (`freeLevelRef` / `check_statement_generality`), which extends R-CARRIER refinement 5.

   The justification is unchanged: an argument equal to the level at every model is the source's
   level, not a specialization.

### (3) Controls

* `scripts/test-occurrence` (10 checks; fixture `fixtures/stmt/occ`, the real Prosa `schedule`,
  `JobReady` and `ideal.processor_state` with their MathComp closure):
  * Positive (generality checked directly, since fixture rows are not protected): every universe
    argument in the parameter types of `JobReady` and `processor_state` equals its level at every
    source model. `schedule` has no solved level. `ProcessorState` is `plain_levels` with
    `sort_interp`.
  * Forged rows, all audit-rejected:

    | Forgery | Kernel |
    |---|---|
    | A sort that is not the R2F reading | rejected |
    | `sort_interp` on a template block | accepted |
    | `JobReady`'s `Job` binder with 58's reading lacking `u58` | rejected |
    | A reported interpretation of 22 that is not R2F | accepted |

  * Unit controls on `equal_at_models`: identity, readings `a ≤ l` and `a + 1 ≤ l`, and a
    source-equal level are accepted; raising, below-only and foreign parameters are rejected.
* `tests/smoke/UniverseRules.lean`: `equalAtModels` `#guard`s.
* Suite expectations updated to the stricter results:
  * `test-universe-c`: `processor_state` is now claimed *generic* (`Job`'s carrier equal to
    `eqtype.51` at every model). Before, it was refused.
  * `test-carrier`: refinement 5 in the general form. "One summand only below" (`a = l`, `b ≤ l`) is
    accepted; a new negative, "all summands only below", is rejected.
  * `test-coherence`: the Countable instance is now on a plain tier, so the raising forgery is refused
    by coherence or by R3.

### (4) Coverage — FULL CORPUS, same 4,474 protected roots

| Run | Impl | Accepted | Audited Pending | Blocked | Direct Failure |
|---|---|---|---|---|---|
| RH2 (entry 12) | `2e46cbf` | 673 | 2,983 | 785 | 33 |
| U3 (measurement) | `5e88da0` | 673 | 3,477 | 299 | 25 |
| **S3** | `2c78107` (= `bd1a71e` tree) | **673** | **3,477** | **299** | **25** |

Validation (S3): consumer OK, audit OK, source instances OK, `CORPUS_PROVENANCE_BOUND`, conversion
dependence OK, 3,576 proof tasks rendered.

* **Protected transitions RH2 → S3:** 494 newly supported (all modern), 0 genuine regressions, 1
  moved between unclaimed categories. That root is `slackless_interval_continuation`: its
  dependencies now translate, and its own statement is refused honestly.
* **All rows:** 531 claimed rows gained, 0 lost. Old false acceptances: 0.
* **Cumulative since case B (CB3 → S3):**

  | | Accepted | Audited Pending | Blocked | Direct Failure |
  |---|---|---|---|---|
  | CB3 | 673 | 2,260 | 1,494 | 47 |
  | S3 | 673 | 3,477 | 299 | 25 |

### (5) Remaining blockers (S3)

324 protected roots are unclaimed (262 modern, 62 Classic). Grouped by the exact set of failing
frontier members:

| Roots | Frontier | Status |
|---|---|---|
| 71 | MathComp `order`/`nmodule` HB obligations (13 members: SOLUTION_FACT_VIOLATED and a kernel rejection of `axioms_`) | Proof-local levels solved to a type level, violating a native fact. |
| 48 | `concrete_job` | Stage-4 work in progress, below. |
| 36 | Classic `concrete_task` | Fixed on the stage-4 branch (R3G for field-only classes), not yet measured on the corpus. |
| 25 | `div.gcdn` (INTERNAL_ERROR) | A translator bug: an unknown metavariable in the body translation of the termination-lowered fixpoint; bisected to the body's `runTrans`. |
| 19 | `SystemEvolutions` (template block) | R3G discovery is not run for template blocks, so `JobType`'s 32 is defaulted. |
| 17+ | CoqEAL `fun_hrel` | **Needs a decision.** A `Prop`-valued body declared at `Type` (Prop ≤ Type cumulativity), which Lean can only represent with a lift (`PLift`/`ULift`): a new representation policy. |
| 13 | Classic `Task_T` | **Needs a decision.** Coinductive; Lean has no coinductive types. |

### (6) Process corrections

* A pattern-based `pkill`/`pgrep -f` killed the tool's own shell twice: the pattern was in its
  command line, and a following commit silently did not run. Jobs are now stopped by PID (memory note
  `no-pkill-f-self-match`).
* Intermediate WIP commits carried temporary debug traces. The branch was squashed before merging, so
  no trace is in the merged history, and the merged tree is byte-identical to the measured one.

### (7) Regressions and validation

* Frozen worktree `r2l-B-test` at `2c78107`: all 13 statement suites pass.

  | Suite | Checks | Suite | Checks |
  |---|---|---|---|
  | `test-statement` | 30 | `test-level-split` | 18 |
  | `test-termination` | 22 | `test-result-sort` | 15 |
  | `test-assembly` | 34 | `test-carrier` | 20 |
  | `test-opaque` | 16 | `test-coherence` | 15 |
  | `test-universe-c` | 22 | `test-occurrence` | 10 |
  | `test-universe-r2` | 9 | `test-provenance` | 5 |
  | `test-multi-instance` | 8 | | |

  `test-all` is 18/18 (`reports/test_all.json`).
* Corpus as in (4).

### (8) Evidence

* `coverage/{U3,S3}.json` and `coverage/transitions-RH2-to-S3.json`;
* `RULE_BACKLOG.{md,json}` and `PROOF_TASKS.jsonl` (S3);
* `provenance/CORPUS_MANIFEST.json` (S3; `-RH2` kept);
* `termination/CONVERSION_DEPENDENCE{,-S3}.json`;
* `test_occurrence.json`, `test_coherence.json` and the other frozen-suite reports.

## Entry 14 — Stage 4 (blocks and terminations) and translator speed (2026-10-15)

Request, in order:
1. Finish U4 and fix `gcdn`, verifying the actual downstream gains.
2. `SystemEvolutions` and `concrete_job`, with independent audit checks and negative controls.
3. Submit the `fun_hrel` lifting design for approval.
4. The MathComp `order`/`nmodule` group, measured on its complete frontier.

Then, on request, speed up full runs: conditional tiers, reuse, late-tier budgets, timing, pruning.
Branch `rules-speed`: `rules-fields`, stage 4, followed by the speed changes.

### (1) `div.gcdn` (25 protected roots blocked by it alone)

* **Root cause of the internal error.** `transFix` restores the Meta state after a failed structural
  attempt, but the hypothesis registry (an `IO.Ref`) kept a hypothesis for `modn`'s prerequisite that
  pointed to a metavariable which no longer existed. Backtracking now also truncates the registries
  (`TransSaved`).
* The real gain needed four more steps (docs/TERMINATION.md §9):
  * the decreasing argument may contain prerequisite-hypothesis placeholders (`modn` is pending);
  * hypotheses are created outside local scopes, since they are closed propositions;
  * let-bound locals are unfolded in a call context's binder types *before* abstraction;
  * **B-P**: the termination statement is a pending proof task over the prerequisites its relation
    mentions. The audit copy checks the telescope and requires the hypotheses to be among its
    constant's recomputed prerequisites.
* **Downstream:** `gcdn`, `lcmn` and `lcmseq.lcml` are claimed. Conversion dependence is now
  `needs unfolding: []`, where `gcdn` used to be the one CONV_NEEDS.

### (2) Blocks (docs/COHERENCE_READINGS.md §7)

* **R3G for template blocks** (`SystemEvolutions`). Implicit levels are non-template parameters, never
  solved. Audit copy in `ind_params`.
* **R3G for field-only classes** (Classic `concrete_task`; the fixture `holder`, the limitation
  recorded in entry 10, is lifted).
* **Per-occurrence discovery,** and class rebinding to the lowest level of a class.
* **δβ-inlining of erasing polymorphic definitions** (`reverse_coercion`), last tier for blocks
  (`concrete_job`). The audit re-derives the erasing property (`erasing_poly_body`) and audits against
  the inlined source (`inline_erasing_block`, which includes primitive-record projection types).
* **Translator-side rule mirroring the audit:** an implicit level must be the argument of some
  reference for that level.
* **Reverted after measurement:** per-occurrence *instance* levels. U4's audit correctly rejected the
  `reverse_coercion` instance arguments they produced; such blocks now go to δβ-inlining.
* **Controls:** `scripts/test-blocks` (13 checks, fixture `fixtures/stmt/s4`). Forged rows, all
  audit-rejected:
  * a termination statement over a non-prerequisite;
  * a template level reported as implicit;
  * `delta_inlined` naming a non-erasing definition;
  * an unreported inlining;
  * an implicit level that is no reference's argument.

  Unit controls cover `erasing_poly_body`. `test-result-sort`'s `holder` expectation now states
  acceptance.

### (3) Proposals awaiting decisions (not implemented)

* `docs/PROP_LIFT_PROPOSAL.md` (now `docs/PROP_LIFT.md`), **rule P**: `PULift` for Prop ≤ Type cumulativity, with
  correspondence obligations C1–C5. Measured: `fun_hrel` (17 roots alone).
* `docs/PHANTOM_SORT_PROPOSAL.md` (now `docs/PHANTOM_SORT.md`), **rule Q**: sort arguments of HB phantom checks.
  * The complete frontier of `GEL`, shared by the 79-root group, is 315 failing declarations.
  * 306 of them are SOLUTION_FACT_VIOLATED in declarations whose type contains
    `HB.structures.unify`. Their levels occur only as type arguments of that check, and Rocq types
    them by cumulativity.
  * Recommended option: Q-a (phantom-only).

### (4) Speed

| Change | Kind | Measured effect |
|---|---|---|
| **Native code** (`precompileModules`, `--load-dynlib` in translate and the consumers) | The translator ran in Lean's IR interpreter. | Subset 104 s → 2 s, byte-identical. Corpus translation ≥ 106 min (S4, interpreted, ungated; stopped) → 26 min (S6). |
| **Conditional tiers** | Discovery only with generalized dependencies. Per-occurrence attempts only with shared levels and kernel/universe failures. Per-occurrence discovery lazily, after the plain attempts fail. δ tier only for kernel/universe failures. | |
| **Exact gates** | R2⁺ tiers only when a sort is fact-reducible. P3 variants identical to earlier tiers skipped without prerequisites. | S6 → S7: 1,520 s → 1,353 s of translation, identical rows. |
| **Late-tier budgets** | A fifth of the declaration's heartbeat budget, failure contained. | |
| **Timing** | `translation_timing.json`: phases and per-declaration attempts, outside the deterministic report. | The first plain attempt per declaration is 76% of translation time (S6). Zero-yield tiers cost 261 s (S6) before the gates. |

Other findings:
* **Performance bug.** Class rebinding was O(n²) in occurrences; it is now a single pass. This was
  U4's 2h+ runtime.
* **Hashing.** The 157 MB source hash was about 100 s interpreted; it is under 1 s native.
* **Pruning** of tiers that never succeed on the corpus (it/cu/lo combinations for statements) is
  deferred. They are not provably redundant, and fixtures may rely on them. The data is in
  `translation_timing.json`.

### (5) Coverage — FULL CORPUS, same 4,474 protected roots

| Run | Impl | Accepted | Audited Pending | Blocked | Direct Failure | Translation |
|---|---|---|---|---|---|---|
| S3 (entry 13) | `2c78107` | 673 | 3,477 | 299 | 25 | ≈ 38 min (interpreted) |
| S6 | `940d82b` | 676 | 3,538 | 235 | 25 | 26 min |
| S7 | `b30ae60` | 676 | 3,538 | 235 | 25 | 23.5 min |
| **S8** | `f5e373c` (= merged tree, docs aside) | **676** | **3,538** | **235** | **25** | 22.5 min |

* **Validation (S8):** consumer, audit, source instances, `CORPUS_PROVENANCE_BOUND`, conversion
  dependence (`needs unfolding: []`), and 5,330 proof tasks rendered.
* **Earlier runs of this stage:**
  * S6's audit rejected one row: its δ-inlining check counted projection metadata. Fixed in S7, and S6
    re-audited clean.
  * U4 (partial stage 4) was audit-rejected for per-occurrence instance levels, which were reverted.
  * S4 (interpreted, ungated) was superseded and stopped.
* **Protected transitions RH2 → S8:** 558 newly supported (543 modern, 15 Classic), 0 genuine
  regressions, 4 moved between unclaimed categories.
  * 3 of these 4 went from blocked to refused, now that their dependencies translate: Classic
    `job_eqdef` and `concrete_taskset`, and `definitions.task.job_task`.
  * Relative to S3 this stage adds 64 newly supported.
* **All rows:** S3 → S8, 1,988 claimed rows gained, 0 lost. S6, S7 and S8 are row-identical
  (status and terms). Old false acceptances: 0.

### (6) Remaining blockers (S8)

260 protected roots are unclaimed (213 modern, 47 Classic):

| Roots | Blocker | Status |
|---|---|---|
| 79 | MathComp `order`/`nmodule` group | Rule Q, needs a decision |
| 43 | `definitions.task.job_task` | REFERENCE_COHERENCE, newly exposed |
| 17 alone (68 affected) | `fun_hrel` | Rule P, needs a decision |
| 13 | Classic `Task_T` | Coinductive, needs a decision |
| 11 | STATEMENT_FREE_LEVEL_PINNED | Classic `ts_obligation_1` |
| rest | Smaller families | See `RULE_BACKLOG.md` |

### (7) Validation and process

* **Frozen worktree `r2l-B-test` at `f5e373c`:** all 14 statement suites pass (`test-blocks` 13,
  `test-occurrence` 10, `test-coherence` 15, `test-result-sort` 15, …), and `test-all` is 18/18.
* An earlier `test-all` at `b30ae60` failed 15 suites on determinism, because timing was inside the
  bound report. Fixed in `f5e373c` by moving it to `translation_timing.json`.
* The stage was squashed before merging, so the debug traces of a WIP commit are not in the merged
  history.

### (8) Evidence

* `coverage/{S6,S8}.json` and `coverage/transitions-RH2-to-S8.json`;
* `RULE_BACKLOG.{md,json}` and `PROOF_TASKS.jsonl` (S8);
* `provenance/CORPUS_MANIFEST.json` (S8; `-S3` kept);
* `termination/CONVERSION_DEPENDENCE{,-S8}.json`;
* `timing/translation_timing-S8.json` and `timing/TIER_SUMMARY-S8.txt`;
* the frozen-suite reports.

---

## Entry 15 — Stage 5: job_task, rule P, rule Q-a, rule T, speed (2026-10-15/16)

Request (stage 5): (1) fix `job_task` and other no-policy blockers; (2) rule P (approved): scoped `PULift`
Prop-to-Type translation with correspondence C1–C5; (3) rule Q-a only (approved; Q-b not adopted):
phantom-only sort lowering with equivalence proofs; (4) `Task_T`: propose a sound coinductive encoding
before implementing. Then, on request, speed (exact gates only) and diagnosis of the next blockers.
Branch `rules-s5` (from `main` = `44bf88b`).

### (1) `job_task` and no-policy fixes

* **δβ-inlining of erasing polymorphic definitions for constants** (`a3ecbc9`), as stage 4 did for blocks:
  `definitions.task.job_task` (43 protected roots) is claimed. Audit: the inlined names are recomputed as
  erasing (`erasing_poly_body`), and the row is audited against the inlined source.
* **Erasing tier, own levels** (S9 audit finding): a statement's own levels are those of the *inlined*
  statement; a level that occurred only in `reverse_coercion`'s instance is no longer one. S9 was
  audit-rejected on 13 rows for this ("implicit level … is not the argument of a reference"); fixed, and
  the 12 affected roots (Classic `periodic_arrivals_*`, `ts_is_schedulable`, `job_generation_valid_jobs`)
  are claimed with the audit OK.
* **R3G for definitions, last resort** (`8440a83`): a failing definition is retried with its references'
  implicit levels as its own (the discovery pass), instead of their defaults. `refine_maxn`/`refine_minn`:
  `Rnat`'s level 47805 (`Set < 47805`) was defaulted to 0, forcing `refines`' level 38671 to 0 against
  `Set < 38671`; now a parameter. Only declarations that fail without it are retried, so no accepted row
  changes (the reason the pass is not used in place).
* **Proof-mode audit crash** (`6351998`): a variable of the stage-5 δ check (`s_` for `s`) broke proof-mode
  audits; caught by `test-m6` in the frozen suites.
* **P3 collapse with normalized levels** (`ac525ad`): two hypotheses of one prerequisite at `Type (max a b)`
  and `Type (max b a)` were not collapsed; the audit (comparing modulo the level normal form) rejected 3
  rows of the GEL subset. The translator now compares with normalized levels.

### (2) Rule P (docs/PROP_LIFT.md, adopted)

* Value lift `PULift.{u_l+1,0} P` for a proposition used at `Type@{l}` (`fun_hrel`); term-level
  `PULift.up`/`PULift.down` at casts, application arguments, the value against its declared type (with
  η-transport of an η-reduced proof body) and `match` scrutinees; an unprotected statement whose codomain is
  a lifted type is stated as its proposition (head chain δβ-inlined). Consumer allows `PULift` (+ `up`,
  `down`) as construction primitives (docs/TRUST.md).
* Audit, independent: `strip_prop_lift` (depth, source `Type` sort, level image), `peel_lift_coercion`
  (only in rows reporting coercions, only `PULift.{_, 0}`), `peel_eta`, the recomputed head chain of a lifted
  statement (never protected), and the C5 listing `prop_lift_protected`.
* C1–C5: `tests/statement/proofs/prop_lift_correspondence.lean` (12 theorems, axiom-free); fixture
  `fixtures/stmt/plift`; `scripts/test-prop-lift` (19 checks: every shape, 8 forged-row negatives — wrong
  level, depth, no cumulativity, lift of a type, unreported/non-Prop coercion, wrong head chain, unfolding on
  a definition — and unit controls).

### (3) Rule Q-a (docs/PHANTOM_SORT.md, adopted; Q-b not adopted)

* Phantom definitions (body after its λs a chain of `phantom X x`, HB's `unify`; or a statement of that
  shape, HB's `id_phant`), recomputed from the source by translator and audit. At their applications a sort
  argument at a sort-parameter position is the type of the paired value; levels occurring only there leave
  the declaration (`phantom_lowered`). Tried first when it applies (strictly more general); for declarations
  using `id_phant`, with per-instance hypotheses (P3) first.
* Equivalence: every instance of a phantom check holds, so any two instances are equivalent
  (`tests/statement/proofs/phantom_sort_equivalence.lean`, 6 theorems, axiom-free). Fixture
  `fixtures/stmt/phant`; `scripts/test-phantom-sort` (12 checks: independent carriers kept, the `id_phant`
  shape, 4 forged-row negatives, criterion units).
* GEL subset (3,382 declarations, roots `GEL`, `GEL_is_total`, `ELF`): claimed 2,423 → 3,050, direct
  failures 345 → ~20, audit OK. The three roots remain blocked by a 23-declaration frontier (§6).

### (4) Rule T (docs/COINDUCTIVE.md) — proposed, approved, adopted

* `Task_T` is the corpus's only coinductive type and is **non-recursive** (`build_task : nat → nat → nat →
  nat → Task_T`); no `cofix` occurs in the export. Proposed as rule T with obligations T1–T5 (same carrier,
  eliminations, no definitional surplus that changes a statement, universes, protection); approved by the
  user; implemented (`cba01c6`).
* A coinductive block is the Lean inductive when it has one body and no constructor argument or index
  mentions it (`nonRecursiveBlock`); `cofix` stays refused. The audit now checks every claimed block's kind
  (`check_coinductive`: flag ⇔ `CoFinite`, the criterion recomputed) — before, it had no check on it.
* Fixture `fixtures/stmt/coind` (with the Rocq-proved η lemma, T1's Rocq side), `scripts/test-coinductive`
  (10 checks), `tests/statement/proofs/coinductive_correspondence.lean` (4 theorems, axiom-free). The first
  fixture run found a wrong argument-order assumption in **both** copies (constructor arguments are stored
  innermost first): the recursive `stream` was accepted. Fixed before commit; the negative control keeps it.
* Corpus: the 13 protected roots of `extraction_tdma` are claimed (S17).

### (5) Speed (exact gates; user's suggestions evaluated)

| Change | Kind | Effect |
|---|---|---|
| Rule-P gate: dependency closure reaches a `prop_lift` definition, or a value lift is possible | exact | CoqEAL subset 244 s → 76 s; 0 rows worse, 7 improved (now within budget), other terms equal modulo level normalization; audit OK |
| Coercion prefilter: only arguments whose type mentions a lifted constant | exact | (same measurement) |
| Stop variants after an exhausted budget; log aborted attempts | exact | aborted attempts were invisible (~1,400 s of S10) |
| Q-a variants ordered by measured success, P3 first for `id_phant` users | order only | GEL subset 4,589 s → 1,249 s, same claims |
| "Stop after a repeated identical failure" | **rejected by data** | on S10 it would lose 87 claimed declarations (incl. `fun_hrel`) to save 53 s |
| Failure kind → variant map | not adopted | only "coherence on a shared level" maps cleanly (179/181 by `cu,lo`) |
| Per-declaration memoization of subterm translations | not adopted | a subterm's translation depends on the attempt's level metavariables and registries |
| Incremental corpus runs | proposed (next) | needs exact replay of per-declaration registries; validation: row-identical to a full run |

### (6) Coverage — FULL CORPUS, same 4,474 protected roots

| Run | Impl | Accepted | Audited Pending | Blocked | Direct Failure | Unclaimed | Translation |
|---|---|---|---|---|---|---|---|
| S8 (entry 14) | `f5e373c` | 676 | 3,538 | 235 | 25 | 260 | 22.5 min |
| S9 | `a3ecbc9` (job_task) | — | — | — | — | 231 | audit-rejected (13 rows, fixed) |
| S10 | `39d6b57` (+ rule P) | 678 | 3,576 | 196 | 24 | 220 | 50 min |
| **S17** | **`38df8a9`** (= merged tree, docs aside) | **685** | **3,584** | **184** | **21** | **205** | 4 h 36 min |

* **Validation (S17):** consumer OK, audit OK, source instances OK, `CORPUS_PROVENANCE_BOUND`, conversion
  dependence (`needs unfolding: []`), 7,180 proof tasks rendered.
* **Protected transitions S8 → S17:** 55 newly supported (31 modern, 24 Classic), **0 regressions**, 0 old
  false acceptances; 9 moved from Blocked to Direct Failure (their dependencies now translate: the
  `job_constructor` uniqueness facts, the refinement `*_ready_instance`s, Classic `powerset`,
  `refine_ArrivalPrefix`).
* **All rows S8 → S17:** claimed 7,839 → 9,804 (**+1,965, 0 lost**). Q-a accounts for most of them (MathComp
  HB builders, `phant_*` constants and obligations); direct failures 793 (S10) → 245.
* **Runs that did not complete:** S11–S14 were stopped to measure later commits; **S15 aborted** (stack
  overflow: the R3G-for-definitions tier's constant discovery recursed without bound on HB's
  `BaseAddMagma_isAddMagma.phant_Build`; bisected to `8440a83`, fixed in `107ab09` by excluding declarations
  with phantom checks); **S16** was killed at the tool's 2 h background limit (long runs are now detached).
* **Translation time 4 h 36 min** (timing/TIER_SUMMARY-S17.txt): P3 attempts dominate. With Q-a, about a
  thousand more HB declarations reach the late tiers. The Q-a first attempt with P3 succeeds 587/1,232; the
  non-Q-a P3 tier never succeeds on declarations where Q-a applies (0 successes, 3,821 s); the Q-a tier's
  winners are `lo,p3,ph` (232) and `cu,lo,ph` (108). These data drive the next speed step (§7).

### (7) Remaining blockers and diagnoses (S17)

205 protected roots are unclaimed (182 modern, 23 Classic).

| Family | Members | Affected roots | Diagnosis / next |
|---|---|---|---|
| SOLUTION_FACT_VIOLATED | 138 | 144 (26 alone) | GEL/order HB frontier (23 declarations at the GEL roots): (A) R-CARRIER copies — a proof-local level solved through one operand copy fails the copied fact of another (`25__c1 ≤ 158`); (B) R2F-c identification in `phant_axioms`; (C) `order.HB_unnamed_factory_64` obligations ("binder levels forced"); (D) budget exhaustion in `rings_modules` builders. Also `refines_abstr`/`refines_apply` obligations. **Next stage.** |
| UNIVERSE_OTHER | 42 | 125 | CMorphisms (`iffT_flip_arrow_subrelation`) |
| REFERENCE_RAISING | 11 | 83 | refinement obligations (`refine_search_space_emax_EDF`) |
| COUPLED_BINDER_LEVELS | 4 | 71 | `order.HB_unnamed_factory_64` obligations (shape C) |
| COURSE_OF_VALUES | 8 | 39 | CoqEAL `param.*_R` |
| PROP_TYPE_CUMULATIVITY | 12 | 28 (15 alone) | `CMorphisms.respectful` and the `job_constructor` uniqueness facts (rule P does not apply: polymorphic relation classes) |
| STATEMENT_FREE_LEVEL_PINNED | 3 | 13 | Classic `ts_obligation_1` |
| PROTECTED_RANGE_NARROWED | 1 | 9 (2 alone) | Classic `job_eqdef`: `concrete_job`'s generalized field carrier `eqtype.51` is pinned to `Set` by the concrete `concrete_task` instance; all instances are plausibly isomorphic, but accepting the specialization needs a correspondence argument — **a representation decision** (booked, not changed). |

Speed, next (data from S17; order-only changes and redundancy are exact, prunings are measured): skip the
non-Q-a P3 tier where Q-a applies (0/… successes, 3,821 s); drop the Q-a tier's repeat of the P3-first
attempt (identical flags); order the Q-a tier `lo,p3` → `cu,lo` → `it,p3`. Incremental corpus runs are
proposed (registry replay; validation: row-identical to a full run). A per-declaration progress log
(`R2L_PROGRESS`) is added for long runs (diagnostics only).

### (8) Validation and process

* **Frozen worktree `r2l-B-test`:** 17 statement suites (new: `test-prop-lift` 19, `test-phantom-sort` 12,
  `test-coinductive` 10) and `test-all` 18/18 at `107ab09` and at the measured `38df8a9` (§ log of the
  suite run). Earlier: `test-all` at `a780ad1` failed `test-m6` — the proof-mode audit crash fixed in
  `6351998`.
* **Subset identity checks** for the exact speed gates (CoqEAL subset: 0 rows worse, 7 improved, all other
  terms equal modulo the level normal form).
* The branch's history is squashed into `main`; the debugging traces used for the S15 bisection were never
  committed (only an optional progress log, merged next stage).

### (9) Evidence

* `coverage/{S10,S17}.json`, `coverage/transitions-{S10,S8}-to-S17.json`;
* `RULE_BACKLOG.{md,json}`, `PROOF_TASKS.jsonl`, `provenance/CORPUS_MANIFEST.json` (S17);
* `termination/CONVERSION_DEPENDENCE{,-S17}.json`;
* `timing/translation_timing-S17.json`, `timing/TIER_SUMMARY-S17.txt`;
* `test_{prop_lift,phantom_sort,coinductive}.json` and the frozen-suite reports.

# A′ handoff: translating the bodies of opaque Set/Type data

**Status (2026-10-14): implemented** — `docs/OPAQUE_DATA.md`, `ITERATION_LOG.md` entry 5. The
measurements below are the pre-A′ baseline.

Decision (2026-10-13): A′ mechanically translates the data-producing bodies of the opaque `Set`/`Type`
constants the corpus needs, keeps their source opacity, and extracts their genuine proof subterms as
obligations. No submitted value is accepted in place of a source body, and uniqueness of an inhabitant
is never assumed. Policy context: `docs/ASSEMBLY.md` ("Opaque data").

## Why it comes first (measured on the baseline corpus run `runs/st-corpus`, commit 7d91605)

* The export has **121** opaque-data constants (`body_state: opaque_interface`); their interface rows:
  22 `STATEMENT_KERNEL_CHECKED`, 20 `STATEMENT_PENDING_KERNEL_CHECKED`, 79 `BLOCKED_DEPENDENCY`.
* **26** of them are prerequisites of pending rows (15 MathComp, 9 Classic, 1 CoqEAL, 1 Corelib).
* Of the 2,322 pending rows, **2,280** need at least one opaque value, and **1,653** (1,520 protected
  Prosa/Classic declarations) need *only* opaque values — no proof task at all. Under the A policy they
  cannot be assembled (`OPAQUE_BINDING_PENDING`), and their tasks are generalized over data (1,501 of
  the 1,521 tasks with prerequisites).
* Highest need (protected pending rows / all pending rows):

| constant | protected | all |
|---|---|---|
| `mathcomp.boot.ssrnat.eqnP` | 1,923 | 2,114 |
| `mathcomp.boot.eqtype.opt_eqP` | 645 | 707 |
| `mathcomp.boot.choice.nat_hasChoice` | 414 | 487 |
| `mathcomp.boot.choice.PCanHasChoice` | 414 | 513 |
| `mathcomp.boot.eqtype.inj_eqAxiom` | 414 | 522 |
| `Corelib.ssr.ssrbool.idP` | 384 | 420 |
| `mathcomp.boot.eqtype.eqbP` | 31 | 54 |
| `mathcomp.boot.eqtype.unit_eqP` | 30 | 46 |
| `mathcomp.boot.seq.eqseqP` | 25 | 75 |
| Classic `ConcreteTask.eqn_task` | 22 | 32 |

These counts are an upper bound on what A′ can move: once a body is translated, its own extracted
obligations become proof tasks (the rows stay pending, now on *proof* prerequisites, which assembly
can handle), and the body may reach declarations not yet in the closure (they may reappear; the old
closure statistics are not a goal).

## What exists to build on

* Exporter (`rocq/exporter/src/r2l_export.ml`, `statement_env`): opaque data is recognized
  (`is_opaque_data`: not proof-valued, native `OpaqueDef`) and its body is *dropped*
  (`body' = None`). The obligation extraction (`extract_proofs`) and Rocq's kernel re-check of the
  rewritten declaration already exist for transparent definitions and would apply to the body.
* IR: needs a body state for "opaque data with exported body" (distinct from `opaque_interface` and
  `transparent`), re-derived by the round trip (`tools/roundtrip.py`, `check_statement`).
* Translator (`Rocq2Lean/Emit.lean`): proof transport already emitted `opaque` declarations with
  kernel-checked values (`mkConstDecl … "opaque"`); statement mode emits `Rocq.<name>.type`. A′ emits
  the constant itself, `opaque Rocq.<name> : ⟦T⟧ := ⟦b'⟧` (Lean's kernel never unfolds an `opaque`, as
  Rocq never unfolds `Qed`), pending (`RocqPending.<name>`) while its obligations are unproved.
* Audit (`tools/audit.py`): `statement_view` turns opaque data into `.type`; A′ audits the body like a
  definition and the declaration kind as opaque.
* Tasks: the opaque-value task disappears; the body's obligations are ordinary proof tasks.
* Assembly: `OPAQUE_BINDING_PENDING` rows become assemblable once the opaque constant is assembled
  (`RocqPending.<name>` → `Rocq.<name>`), with the opaque constant referenced by every use, so each
  value is bound once.

## Questions A′ must answer with evidence

1. Do the 26 bodies export and re-check with their proof subterms extracted (Rocq's kernel), or do some
   need computation on a proof (guard deferral) or fail extraction? Report each.
2. Does Lean's `opaque` match the source's use of opacity in every *statement* and *definition* that
   mentions these constants? A transparent Rocq definition never unfolds a `Qed` constant, so no
   definitional equation should be lost; any dependent type or retained definition that needed one
   would already have failed in Rocq — verify by re-checking, not by assumption.
3. Universe levels of the bodies (statement-only rows never had to solve body levels for these).
4. New closure members reached through the bodies, and their outcomes.
5. Determinism and the irrelevant-proof-change control must still hold (an opaque body *is* data: a
   different body is a different value; the control applies only to proof subterms inside it).

## Acceptance (proposed for the A′ checkpoint)

* the 26 constants (and any others the closure needs) have exported, round-tripped, kernel-checked and
  audited bodies, or a recorded blocker each;
* no opaque-value task remains for a translated body; `check-proof` keeps refusing opaque values;
* the full corpus is re-run and compared with `inventory/coverage_delta.py` against the last measured
  snapshot; regressions listed; `ITERATION_LOG.md` entry appended;
* `test-statement`, `test-assembly`, `test-all` pass; a synthetic fixture case for an opaque body with
  an obligation (e.g. `Asm.pick` made to contain one) is assembled end to end.

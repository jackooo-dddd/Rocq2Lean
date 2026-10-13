# Project scope (locked)

Rocq2Lean is a mechanical translator **for one corpus**: the complete Prosa v0.6 development plus
the complete Classic Prosa source tree identified by RTS, together with the declarations of their
dependencies that these sources actually reach. It is not a translator for arbitrary Rocq projects.
Since 2026-10-11 it translates datatypes, definitions and theorem statements only
(`docs/STATEMENT_ONLY_DESIGN.md`); the dependencies in scope are those reached by the *statement*
closure (types, definition bodies after obligation extraction), not by proofs.

The machine-readable lock is `reports/prosa_inventory/scope.lock.json` (written by
`inventory/scope.py`). The full census, blocker map and per-declaration coverage are in
`reports/prosa_inventory/` (`scripts/inventory-prosa`; report: `FULL_INVENTORY_REPORT.md`).

## Sources

| Family | Identity | Location used | Files |
|---|---|---|---|
| Modern Prosa (P) | Prosa v0.6, commit `414e66760333eaa4ef78c685bcf53291c527a548` (release archive sha512 `128dd213…`) | `.work/prosa-0.6-src` (pristine), `.work/prosa-0.6-rocq93` (working: the five M6 compatibility patches, `compat/prosa-0.6`) | 357, including the 14 refinement files behind the CoqEAL build boundary |
| Classic (C) | ProsaBuddy commit `f692cb7479780cf6009493f373a309e13165201c`, directory `prosaworkspace/classic/` | `.work/classic-f692cb7` (pristine `.v` files; the committed Rocq 9.0 `.vo` files are dropped), `.work/classic-f692cb7-build` (isolated build copy) | 190 (the whole directory, not only the 49 case-study files) |

Authority: RTS commit `f23ca67247e55cd7bd11ca02baff7cc1db3a924a`, read as a provenance reference only
(its correspondence/acceptance labels are not translation evidence). Excluded copies and why are
listed in the lock (`classic.excluded_copies`): `prosaworkspace/rt-proofs-v0.6/classic/`,
`classic-prosa/classic/` in RTS, the RTS_Papers case studies and Prosa v0.4.

## What is a target

* Targets are the **public declarations** of P and C: every declaration of the compiled
  environment introduced by a non-local source sentence, plus record/class projections. They form
  the protected target interface: a translated target keeps its full statement. Dependency
  specializations (R2B-P/R2B-S) are allowed only for non-target dependencies and are flagged in
  `coverage.jsonl` (`interface_conflict`) when they touch a target.
* Source-local helpers, generated schemes, Hierarchy-Builder output and obligations are translated
  only when a target's closure reaches them.
* External declarations (Corelib, Stdlib, MathComp, Hierarchy-Builder, CoqEAL, micromega) are
  translated only when the statement closure of a target reaches them (types and definition bodies;
  proof bodies are not followed). Installing a package to load Prosa does not make its declarations
  targets.

## Environment (fixed)

Lean 4.33.1, Rocq 9.3.0, MathComp 2.6.0, MetaRocq `c18395ad` (switch `rocq930-mc`), as in
`toolchains.lock.json`. Modern Prosa builds with the five compatibility patches; Classic builds with
the RTS prelude `Rocq90Compat.v` (two Rocq 9.0 defaults, no source edit) against the modern working
`prosa.util`. CoqEAL `ce3d1d68` (five modules, compiled unchanged into `.work/coqeal-ce3d1d6`) is
used only to compile and enumerate the refinements. The RTS Classic compatibility patch
(`prosabuddy-classic-rocq93.patch`, RTS `f23ca672`) **is applied**, exactly as authorized in P0
(`reports/prosa_inventory/P0_REPORT.md`): it changes only proof-block lines of one file; all 190
Classic files compile. (An earlier version of this file said the patch was not applied; that predates
P0.)

## Rules for future work

* A new translation feature needs a concrete dependency path from a target to its blocker
  (`reports/prosa_inventory/blockers.json`). Features without such a path are out of scope.
* Existing regression and negative suites stay; the Prosa-only scope limits new feature work, not
  correctness checking. No axioms in translated artifacts, no changed source proofs, no hand-written
  Lean proofs of corpus goals (tiny proofs of *synthetic* test fixtures under `tests/` only,
  docs/ASSEMBLY.md).

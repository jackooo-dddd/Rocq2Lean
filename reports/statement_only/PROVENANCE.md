# Corpus provenance: per-chunk snapshots, Rocq round trips, union universe check, corpus manifest

Gap closed (identified in `VALIDATION_REPORT.md` §4): the merged corpus IR was built by the inventory
export driver, so — unlike a `rocq2lean export` run — it had no per-run source snapshot and no Rocq
round trip. Tool: `inventory/statement_provenance.py`. Tests: `scripts/test-provenance`.

**Nature of the evidence.** All of it is *retrospective revalidation*: it was created on 2026-10-13,
after the chunk exports (2026-10-11), from the files present now. It is not a record that existed at
export time, and every artifact says so (`evidence` field). What it shows is that the exported IR is
reproduced, checked and bound *now*; what links it to the export itself is the IR digest each chunk
export recorded at the time (`result.json: ir_sha256`), which every chunk IR still matches.

## 1. Per-chunk snapshots (`.work/provenance/snapshots/`, index `snapshots.json`)

36 chunk IRs (23 modern, 13 Classic chunk directories; one IR each). For each: the IR digest now and
as recorded at export (all 36 match); the export request (`Export_XX.v`, its roots and `Require`s);
load paths; the exporter plugin digest at export (`f63aa7c1…`) and now; every library `.vo` and its
`.v` source by SHA-256 (no library missing; none has an mtime later than its chunk's export); toolchain
lock and fingerprint; implementation tree.

The exporter plugin now differs from the export-time build: on 2026-10-13 a bulk command
`Rocq2Lean CheckRelations` was *added* (37 lines added, 0 removed or changed in
`r2l_export.ml`/`g_rocq2lean_export.mlg`); the export and statement-preparation code is unchanged.

## 2. Rocq round trips (`.work/provenance/roundtrip/<chunk>/`, index `roundtrip.json`)

The CLI's round trip (`tools/roundtrip.py`) on each chunk IR, in the chunk's own export context (its
load paths and `Require`s): independent Python decoder → Gallina and structural equality against a fresh
MetaRocq quotation (`RtEq.v`), native opacity, recomputed dependency edges, native metadata, the
statement preparation re-derived in a fresh Rocq process (rewritten type and body, state, obligations,
deferred termination), and every ordered pair of universe levels re-checked natively.

Cost (measured): the pairwise universe check called `Rocq2Lean CheckRelation` once per pair, and each
call rebuilt a name table over the whole universe graph (~15 ms per pair; 2–4 h per large chunk). The
round trip now uses `Rocq2Lean CheckRelations` (same check, one table; validated on chunk 0019:
identical 4,692 confirmations, 75 s → 24 s). The largest chunk (`modern-chunk-0008`, 5,471
declarations, 960 levels) takes 29 min in full.

The statement-preparation re-derivation (`Rocq2Lean CheckStatementPrepared`, one fresh environment
preparation *per constant*) dominates the remaining cost: chunks whose modules have large closures
(`results.rta.*`, `analysis.abstract.*`) take 1–4 h in this step alone, against 3 min for the original
export, which prepared the environment once for all roots. A batched variant (prepare once, re-derive
every constant from it, as the export did) is a follow-up; it was not introduced mid-run because it
would change the round-trip tool and invalidate the finished chunks.

RESULTS: see §5 (filled from `roundtrip.json` when all 36 are done).

## 3. Global universe consistency (`.work/provenance/union.json`)

The merged IR's universe line is the union of 36 chunks' native facts, each computed in a different
environment (different module sets). 493 level pairs carry both `le` and `lt` (from different chunks).
Agreement on overlaps is not enough; the union must be the facts of *one* environment.

Check: one Rocq environment loading all 432 modules of both families (the common source context: the
Classic load paths, which contain the modern ones), in which every one of the 251,559 merged facts is
re-checked natively (`CheckRelations`; split over 2 processes, 60 s each):

| | facts |
|---|---|
| hold exactly | 250,981 |
| recorded `le`, native `lt` in the common context (entailed: the fact holds, it is merely weaker) | 578 |
| violated or unknown | **0** |

So a single environment satisfies every merged fact; the translation's use of them (positive
entailment) is sound for that environment. Where the merged line is weaker than the common context
(578 pairs), the translator can only be more conservative (a needed `lt` read as `le` can reject, never
wrongly accept). Regenerating the merged line from the common context (exact facts) would change the
IR and is not done here.

## 4. Corpus manifest (`reports/statement_only/provenance/CORPUS_MANIFEST.json`)

Binds by SHA-256: every chunk (IR, snapshot, round trip and its status); the merge re-derivation (every
merged declaration record byte-identical to its chunk copies; merged universe line = union of the
chunks'; merged declarations = the chunks'); root coverage (all 4,474 protected declarations in the
merged roots); the union check; the run's files (IR, contract, translation report and manifest,
consumer result, audit); the tools (implementation tree, translator build, toolchain lock and
fingerprint, exporter plugin). `check` recomputes all of it; missing or altered evidence is rejected
(`scripts/test-provenance`: altered chunk IR, missing round trip, a merged record altered under a
forged manifest, missing union check).

## 5. Results (2026-10-14)

| evidence | result |
|---|---|
| per-chunk snapshots | 36/36; every chunk IR matches the digest its export recorded; no library missing or newer than its export |
| Rocq round trips | **36/36 OK** — 48,064 declaration records re-checked (structural equality with a fresh MetaRocq quotation, opacity, dependency edges, native metadata, statement preparation re-derived, every universe pair); 16.7 CPU-hours (largest chunk 3.75 h, almost all in the statement re-derivation) |
| merge re-derivation | every one of the 9,970 merged records byte-identical to its chunk copies; merged universe line = union of the chunks' |
| root coverage | all 4,474 protected declarations are merged roots |
| union universe check | 251,559 facts: 250,981 exact, 578 `le` entailed by a native `lt`, **0 violated** (§3) |
| corpus manifest | `CORPUS_MANIFEST.json`: `CORPUS_PROVENANCE_BOUND`, `check` → OK |
| negative controls (`scripts/test-provenance`) | altered chunk IR, missing round trip, merged record altered under a forged manifest, missing union check: all rejected |

Execution notes. Three batches ran (the first by size, a second for the small chunks, a third for
three large chunks), on disjoint chunks; to keep them disjoint, the first batch's orchestrator was
paused (SIGSTOP) for about one hour and labelled placeholder results kept it from re-running the
third batch's chunks (each placeholder was overwritten by that chunk's real result). The reported
duration of the three chunks the first batch was running when paused (`0001`, `0003`, `0006`)
includes the pause. Commands: `python3 -I inventory/statement_provenance.py roundtrip --jobs 3
[CHUNK …]`, then `manifest runs/st-corpus-A`, `check`, `scripts/test-provenance`.

## 6. A′ re-export (2026-10-14)

A′ changed the exporter (opaque data bodies), so the chunk IRs changed and the evidence was rebuilt, in
separate directories (`.work/inventory/export-statement-aprime-*`, `.work/provenance-aprime`; the A,
B and C-1 evidence is kept): 135 chunk exports (all 4,474 roots, 0 failures), 135 snapshots, 135/135
round trips OK, merge re-derived (10,966 records), union check 260,885 facts with 0 violated, manifest
`CORPUS_PROVENANCE_BOUND` (reuse `SAME_TOOLS`), `check` OK, `test-provenance` OK.

The round trip's statement re-derivation is now batched (`CheckStatementsPrepared`: one prepared
environment per export, as the export prepares it) with a deterministic sample of 8 constants per export
re-derived alone (`CheckStatementPrepared`, request independence), and quotes the term only
(`quote_term`, measured identical to the earlier quotation): 25 min wall for all 135 chunks. A manifest
records its evidence and export directories; `check` recomputes reuse applicability against the tools
it runs with, so the earlier manifests check OK at their own commits and are rejected under A′'s tools.

# Parallel translation: the in-process task farm

Status: implemented on branch `par-farm` (`R2L_JOBS=N`, N > 1); the sequential translation (N = 1, the default) is
unchanged. Measured on the full corpus (2026-10-20), below.

## 1. Why in-process

The corpus translation is sequential: declaration *i* is translated in the environment of declarations 1 … *i*−1.
Splitting the export into closure shards (`r2l-par`, ITERATION_LOG entry 19) gives each shard the closure of its
roots: 4,916–9,080 of the 10,972 declarations per shard, ~19 GB per shard, 1.17× faster with 4 shards. A declaration
depends only on its dependencies (the shard runs reproduced the sequential rows), so declarations whose dependencies
are translated can be translated at the same time, once each, in one process.

## 2. Design

* **Ready set.** Each declaration waits for its dependencies (`declDeps`, names of the export); when all are
  installed it is ready. The lowest export position among the ready ones is dispatched first.
* **Workers.** A ready constant runs on a dedicated thread (`IO.asTask (prio := .dedicated)`), as `MetaM.toIO` on a
  snapshot of the main thread's environment and translator state (`GEnv`, results), which holds every installed
  declaration and therefore all of its dependencies. The per-declaration budget is unchanged: Lean counts heartbeats
  per thread. The declaration keeps the metavariable name prefix of its export position.
* **Per-thread state.** The translator's global switches and logs (tier flags, the R-OCC copy set, probes, the
  added-constant log, replay logs: 18 cells) are `TLRef`s, one value per thread (`Rocq2Lean/TLRef.lean`).
* **Installation.** The main thread installs a finished declaration as an incremental replay installs a base run's
  row (`docs/INCREMENTAL.md`): the constants the worker added, in its order, through the checked kernel
  (`addChecked`; the kernel is never skipped), and the translator registration from its rows
  (`replayRegistration`), whose equivalence with the registration of a fresh translation is self-checked for every
  declaration. Results are installed in completion order; rows are reported in export order; replay records are kept,
  so a farm run can be the base of an incremental run.
* **Inductive blocks** (173) are translated on the main thread when ready (replay does not cover them).
* Only plain translation runs use the farm (not assembly, incremental, shadow or witness runs).

## 3. Correctness evidence

Full corpus at `d8f3a10` + farm, 4 workers, compared with S25i (the validated sequential state of the same code):
every row has the same status, target type, target value and universe parameters; the accepted sets are equal (leak
checks in both directions empty); consumer and audit OK. 72 rows differ only in the text of `universe_diagnostics`
(internal metavariable numbers in solver messages: a worker starts with fresh caches and creates a few more
metavariables than the long-running sequential process).

## 4. Speed and memory

| Run | Workers | Translate wall | Peak memory |
|---|---|---|---|
| S24 (sequential) | 1 | 7h44m | ~24 GB |
| S25 (sequential, shared machine) | 1 | 10h24m | ~30 GB |
| **farm** | **4** | **1h33m** | **5.8 GB** |

The tail of the run (the last ~170 declarations, long HB builders) is sequential: the critical path.

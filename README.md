# rocq2lean-pilot

A mechanical, deterministic translator from elaborated Rocq declarations to Lean 4 kernel
declarations, for one fixed corpus: Prosa v0.6 and Classic Prosa (scope: `docs/SCOPE.md`), plus the
Rocq/MathComp/Stdlib/CoqEAL declarations their definitions and statements need.

Fixed toolchains: **Lean v4.33.1**, **Rocq 9.3.0**, **MathComp 2.6.0** and MetaRocq Template
`c18395ad` (opam switch `rocq930-mc`, `toolchains.lock.json`).

**Current direction: statement-only** (`docs/STATEMENT_ONLY_DESIGN.md`, adopted 2026-10-11). Datatypes,
definitions and theorem *statements* are translated; original Rocq proofs are not. Embedded proof
subterms become obligations, and every proof is a task for a separate, future Lean proving agent.
Rocq2Lean writes no proofs.

```text
Compiled Rocq modules + roots
  → statement-mode export (rocq/exporter): kernel classification, obligation extraction, closure
  → versioned source IR (NDJSON, docs/IR_SPEC.md)
  → deterministic translation to Lean declarations (Rocq2Lean/), kernel-checked;
    declarations needing unproved prerequisites are pending artifacts (RocqPending.*)
  → validation: fresh-process consumer + independent audit + interface protection
  → proof tasks (PROOF_TASKS.jsonl); submitted proofs checked (check-proof)
  → assembly of final declarations from verified proofs (docs/ASSEMBLY.md)
```

The claim this project supports is "this implementation translates and checks the declared fragment
on these inputs", not a verified general compiler. A kernel-checked statement is not a proved theorem,
and a pending artifact is not the final public interface. Current state: `STATUS.md`; progress log:
`reports/statement_only/ITERATION_LOG.md`.

The earlier proof-preserving pipeline (M1–M6, P0; tag `p0-proof-transport-final`) is kept as
historical evidence and regression tests (`scripts/test-all`); its `VERIFIED` results are not
statement-only coverage.

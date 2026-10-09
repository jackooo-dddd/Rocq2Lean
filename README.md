# rocq2lean-pilot

Experimental, proof-preserving translator from elaborated Rocq declarations (including their
original proof terms) to Lean 4 kernel declarations.

Fixed toolchains: **Lean v4.33.1** and **Rocq 9.3.0** (opam switch `rocq930`).

```text
Compiled Rocq 9.3.0 modules + explicit roots
  → quotation/export with dependency closure      (rocq/)
  → versioned source IR (NDJSON)                  (docs/IR_SPEC.md)
  → deterministic translation to Lean Expr/Declaration   (Rocq2Lean/)
  → Lean v4.33.1 kernel checking (checked path only)     (Rocq2Lean/Kernel.lean)
  → provenance / computation / dependency / assumption audits
```

The claim this project can support is "this implementation translates and checks the declared
fragment on these inputs", not a verified general compiler. Current state: see `STATUS.md`.

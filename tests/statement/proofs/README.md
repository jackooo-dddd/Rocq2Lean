# Synthetic fixture proofs (tests only)

Tiny Lean proofs of the **synthetic** assembly fixture `fixtures/stmt/asm/Asm.v`, used by
`tests/statement/check_assembly.py` to exercise successful proof checking and assembly. They are a
narrow testing exception (docs/ASSEMBLY.md): Rocq2Lean writes no proofs, none of these prove a
Prosa, Classic or MathComp goal, and none enter corpus results.

Each file is a template module body; `@TASK@` is replaced by the task id (the module and the
declaration are `RocqProofTemplates.T<task_id>` and `RocqProofTemplates.T<task_id>.proof`).

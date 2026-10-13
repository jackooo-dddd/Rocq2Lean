# Synthetic fixture proofs (tests only)

Tiny Lean proofs of the **synthetic** assembly fixture `fixtures/stmt/asm/Asm.v`, used by
`tests/statement/check_assembly.py` to exercise successful proof checking and assembly. They are a
narrow testing exception (docs/ASSEMBLY.md): Rocq2Lean writes no proofs, none of these prove a
Prosa, Classic or MathComp goal, and none enter corpus results.

Each file is a template module body; `@TASK@` is replaced by the task id (the module and the
declaration are `RocqProofTemplates.T<task_id>` and `RocqProofTemplates.T<task_id>.proof`).

`wf_edivr_termination.lean` and `wf_edivr_unfold.lean` prove the termination obligation and the
unfolding equation of the synthetic Task B fixture `fixtures/stmt/wf/Wf.v` (`SF.Wf.edivr`), used by
`tests/statement/check_termination.py` (docs/TERMINATION.md). Same exception, same limits.

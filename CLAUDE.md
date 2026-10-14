# Rocq2Lean — notes for Claude Code

Rocq2Lean is a mechanical, statement-only Rocq → Lean translator for Prosa v0.6 + Classic. The
current state is in `STATUS.md`. The per-change record is `reports/statement_only/ITERATION_LOG.md`.
The rule backlog is `reports/statement_only/RULE_BACKLOG.md`.

## Standing rules (from the user)

* **What is translated.** Never translate Rocq proofs, never write corpus proofs, never invoke a
  proving agent. Synthetic fixture proofs are allowed in tests only.
* **Pinned inputs.** Pinned toolchains (`toolchains.lock.json`): Lean 4.33.1, Rocq 9.3.0 (opam
  switch `rocq930-mc`), MathComp 2.6.0. Same 4,474 protected roots.
* **Soundness.** No axioms, `sorry` or public assumptions. Never narrow protected binder ranges or
  statements.
* **Independence.** The translator and the auditor (`tools/audit.py`) stay independent.
* **Policy changes.** Ask before adopting a new semantic representation policy.
* **After every change.** Rerun the tests, append an ITERATION_LOG entry, and give a chat summary with
  the coverage delta.
* **Commits.** Commit or push only when the user asks.
* **Heavy jobs.** Run them in frozen, isolated worktrees with separate run directories and monitored
  memory. Independent jobs may run in parallel.
* **Suites.** Run statement suites and test-all in the frozen worktree `../r2l-B-test`, checked out
  at the commit under test. Never run them in a tree that is being edited.
* **Protection.** Direct `translate` calls without the run's contract skip the protection binding.
  Only CLI pipeline runs bound to the contract, and corpus runs, are authoritative.
* **Pushing to GitHub.** Push over SSH with `GIT_SSH_COMMAND="ssh -o IdentitiesOnly=yes -o
  ConnectTimeout=30 -o ServerAliveInterval=10 -o ServerAliveCountMax=3 -i
  ~/.ssh/github_rts_ed25519"` to `git@github.com:jackooo-dddd/Rocq2Lean.git`. The connection is
  intermittent: retry, then verify with `git ls-remote`.

## Delegating coding work to OpenAI Codex CLI

Claude Code is the orchestrator: it plans, splits tasks, reviews, tests and integrates. Codex CLI
(`codex`, logged in through ChatGPT) is the coding worker. Use it when it helps, especially for
independent tasks that can run in parallel.

**Model and budget**
* The model is **`gpt-6-astra`**, the most capable; the reasoning effort can be anything from `low` to
  `ultra`.
* Typical efforts: `medium` for small mechanical edits and tests; `high` or `xhigh` for implementation
  and debugging; `max` or `ultra` for hard design or debugging work.
* **Stop delegating when less than 10% of the weekly limit remains.**
  `~/research/codex-tools/codex-limit` prints the usage and exits 1 below the threshold;
  `codex-worker` checks it before every run.

**Tools** (`~/research/codex-tools/`, outside the repo so that every worktree can use them):

```
codex-limit                     # weekly usage; exit 1 when < 10% remains
codex-worker -n NAME [-b BASE_REF] [-e EFFORT] [-m MODEL] [--no-setup] TASK_FILE|-
```

`codex-worker` does the following:
1. Creates (or reuses) the worktree `~/research/r2l-codex-NAME`, detached at `BASE_REF` (default
   `HEAD`).
2. Unless `--no-setup` is given, links the shared read-only inputs into `.work/` and builds the
   exporter plugin and the Lean package outside the sandbox.
3. Runs `codex exec -m MODEL -c model_reasoning_effort=EFFORT -s workspace-write -C <worktree> --json`,
   with the task prefixed by the project rules and environment.
4. Writes everything to `~/research/codex-runs/NAME/`: `prompt.txt`, `events.jsonl`, `final.txt`,
   `stderr.txt`, `exit_code`, `status.txt`, `diff.stat`, `diff.patch`.

**Safety (never relax these)**
* Sandbox `workspace-write`: Codex writes only inside its worktree; home and `~/.opam` are read-only.
  No `--dangerously-*` flags, no approval bypass.
* opam writes logs under `~/.opam/log`, which fails in the sandbox; the worker sets
  `OPAMLOGS=<worktree>/.codex-tmp/opam-logs` (`.codex-tmp/` is in `.git/info/exclude`). With it, Lake
  builds, the Rocq exporter and the statement suites all run inside the sandbox; this was verified with
  `scripts/test-result-sort`.
* Always close stdin (`< /dev/null`, or pass the prompt on stdin). Otherwise `codex exec` waits for
  input. The worker script does this.
* Codex never commits or pushes. One worker per worktree. Claude Code never edits a worktree while a
  Codex worker is running in it, and never assigns two workers overlapping files.

**Procedure**
1. Write a self-contained task file: the goal; the exact files to touch or not touch; the tests to run;
   acceptance criteria. Codex does not see this conversation.
2. Run `codex-worker -n NAME -b <commit> -e <effort> task.txt`. For parallel tasks, use distinct names
   (separate worktrees) and launch them as background jobs.
3. Review: read `final.txt`, then the actual `git diff` in the worktree; do not trust the summary
   alone. Rerun the relevant tests yourself (frozen worktree for suites, corpus runs as usual).
4. Integrate the accepted changes into the development branch by cherry-picking the diff
   (`git -C <worktree> diff | git apply`) or by editing; then follow the usual change loop (tests,
   ITERATION_LOG). Commit only with the user's permission.
5. Remove a finished worktree: `git worktree remove ~/research/r2l-codex-NAME` (check `git status`
   there first).

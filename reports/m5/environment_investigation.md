# M5 environment investigation (2026-10-10, cityu-wsl)

1. `opam install --switch=rocq930 --show-actions rocq-mathcomp-ssreflect.2.6.0`. The plan was:
   remove rocq-equations, rocq-metarocq-{utils,common,template} (pinned); downgrade dune 3.24.2 →
   3.23.1 (required by elpi/rocq-elpi); recompile coq, coq-core, rocq-core, rocq-runtime,
   rocq-stdlib, coq-ext-lib, coqide-server, stdlib-shims. **Rejected**: it would remove the pinned
   frontend.
2. Keeping the pins (`opam install … rocq-metarocq-template rocq-equations "dune>=3.24"`): "No
   solution found". `rocq-metarocq-utils` requires `rocq-core >= dev`, which conflicts with the pin
   at 9.3.0.
3. `--ignore-constraints-on=dune`: an install-only plan (32 packages, no removals). It was executed
   and failed building rocq-elpi 3.5.1: `dune-project` line 2 `(using coq 0.8)`, "Error: Extension
   coq was deleted in the 3.24 version of the dune language". Packages installed before the
   failure (27 OCaml build packages, `elpi` 3.7.3) stay in `rocq930` (`opam_before_mathcomp.txt`
   lists the state before). The translator fingerprint is unchanged and doctor is OK.
4. Building rocq-elpi from its opam source with the dune 3.23.1 binary of switch prosa-0.6 (same
   OCaml 4.14.2): `Package "elpi" doesn't exist in the current project and isn't installed either`.
   dune 3.23.1 sees only 28 libraries; the rest have `dune-package` files written by dune 3.24.2.
   Abandoned.
5. Decision: a dedicated switch `rocq930-mc` (`docs/ENVIRONMENT_M5.md`, `scripts/setup-switch-mc`).

# Reproduction

Two kinds of reproduction are distinguished; reports state which one was executed.

1. **Fresh clone, preinstalled toolchains** (executed for the hardening report):
   `./scripts/clean-rebuild [COMMIT]` clones the repository into `~/research/r2l-clean-<commit>`,
   builds `Rocq2Lean` and `Smoke` from scratch and runs `./scripts/test-all` (every suite in a fresh
   process); results go to `reports/clean_rebuild/`. Then `./scripts/package-evidence` and
   `./scripts/acceptance`. Requires the toolchains below to already be installed.
2. **Toolchain reconstruction** (documented, not executed in this report): install elan and
   `leanprover/lean4:v4.33.1`; create the opam switch and pins below; then (1).

```sh
# Lean
elan toolchain install leanprover/lean4:v4.33.1
# Rocq 9.3.0 + MetaRocq Template (no release targets 9.3; pinned commits)
opam switch create rocq930 ocaml-base-compiler.4.14.2 --repos=default,rocq-released,core-dev
opam install --switch=rocq930 rocq-runtime.9.3.0 rocq-core.9.3.0 rocq-stdlib.9.2.0
opam pin add --switch=rocq930 -n rocq-core 9.3.0; opam pin add --switch=rocq930 -n rocq-runtime 9.3.0
opam install --switch=rocq930 coq-ext-lib.0.13.2
opam pin add --switch=rocq930 -n -k git rocq-equations "git+https://github.com/mattam82/Coq-Equations.git#d56dfc2c38feb5054d75ef43540ee89a6beb1a7e"
IGN=rocq-core,rocq-stdlib,rocq-runtime,coq-core,rocq-equations,coq-ext-lib
opam install --switch=rocq930 --ignore-constraints-on=$IGN rocq-equations
for p in utils common template; do
  opam pin add --switch=rocq930 -n -k git rocq-metarocq-$p "git+https://github.com/MetaRocq/metarocq.git#c18395ad772a40d59b6d04a5fcd1a4e0e5073d81"
done
opam install --switch=rocq930 --ignore-constraints-on=$IGN,rocq-metarocq-utils,rocq-metarocq-common rocq-metarocq-template
```

`scripts/doctor` validates the result against `toolchains.lock.json` (exact version lines,
opam package versions and git pin commits); paths come from `opam`/`lake`, not from the lock.

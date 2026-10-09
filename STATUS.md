# Status

Updated only from test evidence. Statuses follow the prompt's vocabulary.

| Stage | Status | Evidence |
|---|---|---|
| Phase 0: Lean v4.33.1 checked kernel path | PASS | `lake build Smoke`: `True.intro : True` accepted; `Nat.zero : False` rejected by `(kernel) declaration type mismatch` |
| Phase 0: Rocq 9.3.0 switch | INSTALLED | `~/.opam/rocq930`, rocq-core/rocq-runtime pinned 9.3.0, rocq-stdlib 9.2.0; log `~/logs/install_rocq930.log` |
| Phase 0: MetaRocq Template compatibility | IN PROGRESS | candidate MetaRocq `c18395ad` (+ Equations `v1.3.2-9.3`, ext-lib 0.13.2) |
| id_nat end-to-end | NOT STARTED | |
| M1 | NOT STARTED | |
| M2 | NOT STARTED | |
| M3a–d | NOT STARTED | |

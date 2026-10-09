# Status

Updated only from test evidence (`scripts/test-*` on cityu-wsl). Statuses follow the prompt's vocabulary.

| Stage | Status | Evidence |
|---|---|---|
| Phase 0: toolchains | PASS | `scripts/doctor`: Lean v4.33.1 (`819816b2`), Rocq 9.3.0 / OCaml 4.14.2, locks in `toolchains.lock.json`, report `reports/environment.json` |
| Phase 0: Lean checked path | PASS | `lake build Smoke`: valid accepted, `Nat.zero : False` rejected by the kernel |
| Phase 0: MetaRocq | **METAROCQ_TEMPLATE_RUNNING** | MetaRocq `c18395ad` unpatched; gate `reports/phase0/metarocq_gate.log` |
| id_nat end-to-end | PASS | `scripts/test-smoke` (7/7): original `Qed` proof → Lean theorem, no axioms, consumer + audit; deleted body → `BLOCKED_SOURCE_BODY` |
| M1 export & dependency validation | PASS | `scripts/test-m1` (24/24): transparent/opaque/`Defined`/opaque-data/assumption states, Section discharge, cross-module opaque chains, independent round trip (`tools/roundtrip.py` + `rocq/roundtrip/RtEq.v`), relaxed-flag rejection |
| M2 expression translation | PASS | `scripts/test-m2` (13/13): prop identity, higher-order composition, shadowing lets, dependent parameters over `Set`, vm cast validated then erased, identical short names across modules, identical binder names; audit rejects swapped same-typed bodies, an unrelated `True` proof and a swapped variable; source mutation rejected by snapshot and round trip |
| M3a–d | IN PROGRESS | |
| Negative / holdout suites | PARTIAL | missing body, assumption, relaxed flags, unsupported inductive (in smoke/M1) |

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
| M3a inductives | PASS | `scripts/test-m3`: fresh `RNat`, `RList A`, `Tree A` (two recursive fields), indexed `Vec A n` as Lean inductives; constructor order kept; audit + consumer |
| M3b case lowering | PASS | nonrecursive nat/list/tree matches and indexed dependent matches (`vid`, `vtail`), `destruct` on `eq`, lowered to kernel `I.rec` with dependent motives |
| M3c fix lowering | PASS | `addR`, `lengthR`, `mapR`, `mirrorR` (distinct left/right results; swap mutation rejected), `addAcc` (function-valued motive), `vmap` (index generalization), `double_nat` (Nat.rec) |
| M3d original induction proofs | PASS | `addR n RZ = n`, `lengthR (mapR f xs) = lengthR xs`, `mirrorR (mirrorR t) = t`, `vmap id v = v`, `vid v = v` — original proofs incl. generated `*_ind` and Corelib `eq_ind`/`eq_sym`/`eq_ind_r` (global levels generalized); 15 definitional / 6 propositional laws (`reports/m3_laws.json`); computation 78/78 agree; 7 unsupported patterns rejected explicitly |
| Negative suite | PASS | `scripts/test-negative` 11/11 |
| Holdout (implementation frozen at `pilot-freeze-1`) | PASS | `scripts/test-holdout`: 9/9 new roots VERIFIED, implementation unchanged since the tag |
| Clean rebuild | PASS | fresh clone at `61cecf1`: `scripts/test-all` exit 0 (`reports/test_all.json`) |

Final report: `reports/FINAL_REPORT.md`.

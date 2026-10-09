# rocq2lean-pilot — final report

Commit `61cecf1` (implementation frozen at tag `pilot-freeze-1` = `6a4054d`; later commits change
tests, fixtures and docs only). Reproduced from a fresh clone on cityu-wsl: `scripts/test-all`
exit 0 (`reports/test_all.json`).

## Verified toolchains

| | |
|---|---|
| Lean | **v4.33.1** (`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`), `lean-toolchain` = `leanprover/lean4:v4.33.1` |
| Rocq | **9.3.0** (tag `V9.3.0`, `c8e202eb`), OCaml 4.14.2, opam switch `rocq930`, rocq-core/runtime pinned |
| Rocq stdlib | `rocq-stdlib` 9.2.0 (accepts rocq-core ≥ 9.1) |
| MetaRocq | **ran**: Template frontend, `c18395ad772a40d59b6d04a5fcd1a4e0e5073d81`, unpatched (no release targets 9.3; last `main` commit before adaptations to Rocq PRs absent from 9.3.0). Status `METAROCQ_TEMPLATE_RUNNING`. |
| Deps | Coq-Equations `v1.3.2-9.3` (`d56dfc2c`), coq-ext-lib 0.13.2 |

Locks: `toolchains.lock.json`, checked by `scripts/doctor` before every command; environment in
`reports/environment.json`. Not used: Mathlib, PCUIC, SafeChecker, erasure.

## Pipeline

`rocq2lean export` (MetaRocq `quote_term_rec ~bypass:true` in a Rocq plugin → NDJSON IR, with an
independent round trip in a fresh Rocq process) → `rocq2lean translate` (Lean `Expr`/
`Declaration`, inserted only through `Environment.addDeclCore (doCheck := true)`) →
`rocq2lean verify` (source snapshot hashes, fresh-process consumer re-check incl. `collectAxioms`,
independent structural audit `tools/audit.py`).

## Results by stage

| Stage | Result | Evidence |
|---|---|---|
| Phase 0 | PASS | doctor; checked path accepts `True.intro`, rejects `Nat.zero : False`; MetaRocq gate (`reports/phase0/metarocq_gate.log`) |
| id_nat | PASS | original `Qed` proof → Lean theorem, no axioms; deleted body → `BLOCKED_SOURCE_BODY` (`test-smoke` 7/7) |
| M1 export & dependencies | PASS | `test-m1` 24/24 |
| M2 expressions | PASS | `test-m2` 13/13 incl. audit rejecting type-correct mutations |
| M3a inductives | PASS | `RNat`, `RList A`, `Tree A`, `Vec A n` generated |
| M3b case lowering | PASS | incl. indexed dependent `vid`, `vtail`; `destruct` on `eq` |
| M3c fix lowering | PASS | `addR`, `lengthR`, `mapR`, `mirrorR`, `addAcc`, `vmap`, `double_nat` |
| M3d original induction proofs | PASS | `addR n RZ = n`, `lengthR (mapR f xs) = lengthR xs`, `mirrorR (mirrorR t) = t`, `vmap id v = v`, `vid v = v`; 15 definitional / 6 propositional laws (`reports/m3_laws.json`); computation 78/78 agree (`runs/m3-compute/computation.json`) |
| Negative suite | PASS | `test-negative` 11/11 |
| Holdout (after freeze) | PASS | 9/9 roots (`addR_comm`, `addR_assoc`, `size_mirror`, `length_app`, `vapp_nil` over Corelib `Nat.add`, `incr_not_BZ` via `discriminate`/`False`, `omap_id`, `swap_swap`, `le_0`) |

## Supported fragment

See `docs/SUPPORT_PROFILE.md`. In short: monomorphic closed constants (transparent / opaque
proof / opaque data), Prop/Set/`Type@{Set+n}` plus global monomorphic levels generalized to
universe parameters, bootstrap `nat ↦ Nat` and `eq ↦ Eq`, single-body inductives, `match`
lowered to `I.rec`, single structural `fix` matching on its decreasing argument.

## Rejected (explicitly, with node path / dependency path)

Mutual or non-direct recursion, changing parameters before the decreasing argument, recursion
over mutual/nested inductives, coinductives, `SProp`, universe polymorphism, primitives, section
variables, source axioms (`BLOCKED_SOURCE_BODY`), relaxed source checking (`AUDIT_REJECTED`).

## Assumptions and special conditions

* Success profile: no source axioms, no target axioms (every accepted declaration has an empty
  `collectAxioms`, including Lean's standard axioms).
* Untranslated declarations: only `nat` and `eq` (bootstrap, re-verified every run).
* Universe instantiation at references to generalized constants is solved by Lean's unifier
  (levels only); unconstrained levels are set to 0; the kernel re-checks.
* The `fix` motive and recursor binder types are forced by kernel typing and not compared by
  the audit (documented in `docs/TRUST.md`).
* The original source proofs are used by design.

## Known blockers (reproducers in `fixtures/m3/M3Neg.v`, run by `test-m3`)

`evenR/oddR` (mutual fix), `half` (non-direct subterm), `addPre` (changing earlier parameter),
`Stream` (coinductive), `sprop_id`, `pid` (polymorphic), `rose_size` (nested). Global levels in
*inductive* declarations (e.g. Rocq's template `list`, `prod`) are not yet generalized.

## Next narrowly-defined extension

Generalize global/template universe levels for **inductive** declarations (the rule already
used for constants), so that Corelib `list`/`prod`/`option` translate instead of needing
fixture-local copies; then mutual `fix` over a single inductive (common in MathComp-style code).

# M4 — Real Rocq standard-library declarations: report

**Status: M4 criteria met** (details below), with recorded blockers. Toolchains unchanged:
Lean v4.33.1, Rocq 9.3.0, MetaRocq Template `c18395ad` (unpatched), rocq-stdlib 9.2.0.

| Criterion | Result |
|---|---|
| ≥ 3 genuine parameterized stdlib datatypes | Corelib `list`, `option`, `prod`, `sum`, `sigT` (all template-polymorphic), plus `bool`: fresh Lean inductives with their universe parameters, kernel recursors and constructors in order |
| ≥ 5 nontrivial real function/theorem roots with dependencies | **16 Stdlib theorems** (closure 47) and **29 functions** (closure 35) VERIFIED; and 13 unseen holdout theorems |
| Original proof terms kernel-checked | yes; every accepted declaration goes through `addDeclCore (doCheck := true)`; the consumer re-reads them and finds no axioms |
| Constructor/recursor computation validated | 39/39 Rocq-vs-Lean evaluation cases agree: functions plus `list_rect`, `option_rect`, `prod_rect`, `bool_rect` (`tests/m4/compute_m4.py`) |
| Independent structural, universe, dependency and axiom audits | all pass. On the theorem closure the auditor independently determined **721** typing-determined levels (0 deferred) and checked **595** R3 arguments |
| M1–M3 regressions | `test-all` **16/16 suites, 310 checks, 0 failed**. `reports/m4/regression_vs_m3.json`: identical roots and accepted sets in every historical stage |

## Baseline

`test-all` at `6e85e3c` (the M1–M3 acceptance commit): 15/15 PASS, recorded in
`reports/m4/baseline_test_all.json` before any change.

## Investigation: Rocq 9.3.0 kernel declarations

| Declaration | Kernel form |
|---|---|
| `bool` | `Inductive bool : Set`, monomorphic, no levels |
| `option`, `list` | **template** on one level (`option.u0`, `list.u0`), "cannot be instantiated to Prop"; result `Type@{max(Set,l)}` |
| `prod` | **template** on two levels, "can be instantiated to Prop": its parameters bind a sort *quality* as well as a level |
| `sigT` | template; parameter `P : A → Type@{l}` binds its level through an **arity** |
| `length`, `app`, `map`, … | monomorphic constants with their own global levels |
| `list_rect` etc. | ordinary constants (fixpoints over the inductive), translated generically |

MetaRocq quotes template inductives at their default instance (`template_defaults`), and references
carry an **empty** instance: Rocq computes the instance from the arguments. Rocq 9.3 records this in
`Declarations.template_universes` (`template_param_arguments`, `template_concl`, `template_context`,
`template_defaults`).

## What was implemented

* **Exporter (IR):** `native.template_info` is exported natively from the kernel record (defaults, the
  bound sort per parameter, the conclusion), and the fresh-process round trip checks it.
* **R2T:** inductives with global levels become universe-polymorphic Lean inductives; non-template
  ones obey R3 at references.
* **R5:** a template level is bound by exactly one parameter of sort `Type@{l}`, or of an arity
  ending in it. A reference's level is the (codomain) level of that argument, which the kernel
  forces; the auditor recomputes it from the *source* record and the consumer checks every
  occurrence. Quality-polymorphic parameters are translated at quality Type. Prop instances, and
  Rocq's Prop ≤ Type cumulativity into a template parameter, are rejected explicitly.
* **R2B:** levels that occur only in a constant's body are solved, not generalized, and must satisfy
  the native facts; this is checked by the translator and independently by the auditor. An
  unconstrained one defaults to its minimal model, with a kernel justification. This unblocked
  every proof that uses `f_equal`.
* **`fix` with changed leading arguments:** such an argument is generalized in the motive. The
  translator and auditor each decide the set independently from the source. This covers Corelib
  `seq`, Stdlib `nth_error` and, prospectively, MathComp `iota`. The M3 fixture `addPre` is now
  supported and verified.
* **Fixes:**
  * Recursive-field detection now compares parameters (Stdlib `concat`).
  * Binders are built without β-reduction (`bindFVars`/`instLevelMVars`). The **independent audit
    caught** that Lean's `mkLambdaFVars`/`instantiateMVars` β-reduce binder types that mention
    universe metavariables.
  * Preflight no longer walks into universe instances.

## Accepted real declarations (all VERIFIED)

* **Datatypes:** `Corelib.Init.Datatypes.{list, option, prod, bool, sum}`, `Corelib.Init.Specif.sigT`.
* **Theorems:** `Stdlib.Lists.List.{app_nil_r, app_assoc, length_app, map_app, length_map,
  rev_app_distr, rev_involutive, map_map, map_id, in_map, fold_left_app, combine_split,
  length_fst_split, app_inv_head, in_app_or, map_ext}`.
* **Functions:** `Stdlib.Lists.List.{rev, fold_left, fold_right, combine, split, hd_error, existsb,
  forallb, filter, concat, last, removelast, nth_error, rev_append, flat_map, partition,
  list_prod}`, `Corelib.Lists.ListDef.{firstn, skipn, repeat, seq, map}`,
  `Corelib.Init.Datatypes.{option_map, negb, andb, orb, xorb, fst, snd}`,
  `Corelib.Init.Specif.{projT1, projT2}`.
* **Fresh holdouts** (chosen after `m4-freeze-1` = `54c9e70`; run on the frozen implementation):
  `app_comm_cons`, `app_eq_nil`, `in_or_app`, `map_rev`, `concat_app`, `flat_map_app`,
  `existsb_app`, `forallb_app`, `fold_right_app`, `firstn_skipn`, `length_seq`, `nth_error_In`,
  `app_inv_tail`, `Corelib sum`: **14/16** (`reports/m4/holdout_m4.json`). After the post-holdout
  fix, the regression rerun gives 15/16 (`holdout_m4_regression.json`).

## Negative tests (`tests/m4/check_m4.py`, rejected for the intended reason)

| Defect | Kernel | Detector |
|---|---|---|
| `prod` instantiated at Prop (`True * True`) | — | translator `UNSUPPORTED_FEATURE` |
| Prop-valued family for `sigT` | — | translator `UNSUPPORTED_FEATURE` (cumulativity) |
| `template_info` mutated in the IR | — | native round trip |
| forged template binding (`prod`) | accepted | audit `structure` |
| inductive level parameters renamed (`list`) | rejected | audit `structure` |
| template level raised at a reference (`app_nil_r`) | rejected | audit `instance_levels` |
| proof-local solution forged / proof-local set truncated | accepted | audit `universe` |
| `seq`: generalized argument / recursive-call argument changed (type-correct, synchronized forged module) | accepted | `verify` → audit `structure` |

## Unsupported cases (exact dependency paths)

| Root | Path | Cause |
|---|---|---|
| `Corelib.Lists.ListDef.nth` | `nth` | body matches `n` before the decreasing `l` (fix lowering needs the decreasing match outermost) |
| `Stdlib.Lists.List.length_rev` | `length_rev → PeanoNat/Nat.add_comm → Nat.add_0_r → Nat.succ_inj_wd → Nat.succ_inj → Corelib.Classes.Morphisms.subrelation_proper` | setoid machinery: universe-polymorphic constants and instances |
| `Stdlib.Lists.List.in_rev` (holdout) | `in_rev → … Morphisms.* → Corelib.Relations.Relation_Definitions.relation` | `relation`'s value `A → A → Prop` fits `Type@{max(l,Set)}` only through Rocq's `Set < l`; a generic Lean level can be 0, so the kernel rejects it (R2, documented) |

## Next concrete technical changes

1. A fact-justified sort floor for declaration result sorts (`relation`). This unblocks the
   setoid-free parts of `Morphisms`. The universe-polymorphic `Morphisms` constants would still
   need universe-polymorphism support.
2. `brecOn`-style lowering for fixpoints whose decreasing match is not outermost (`nth`).

## Reproduce

```sh
./scripts/test-all            # 16 suites incl. test-m4
./scripts/test-holdout-m4     # fresh-holdout runner (regression role after m4-freeze-1)
python3 -I tests/m4/compute_m4.py
```

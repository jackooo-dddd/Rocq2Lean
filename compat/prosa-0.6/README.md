# Prosa v0.6 under Rocq 9.3.0 / MathComp 2.6.0: compatibility patches

Prosa v0.6 (`rocq-prosa` 0.6, release archive `rt-proofs-v0.6.tar.gz`, sha512 `128dd213…6228`) was
released for Rocq 9.0 with MathComp 2.4 (`rocq-core >= 9.0 < 9.1`). The translator's toolchain is
fixed at Rocq 9.3.0 with MathComp 2.6.0 (`toolchains.lock.json`). The toolchain was **not** changed
and no Prosa definition was rewritten.

The unmodified release fails early on Rocq 9.3 (`reports/m6/prosa_unpatched_build.log`). Patches
0001–0004 make the FinishTime closure (26 files) build; with 0005, all of Prosa builds. `scripts/setup-prosa` applies them in
order to the checksum-verified original archive in `.work/prosa-0.6-rocq93` and records the
sha256 of every changed file (`R2L_PATCHED.json`). Exactly 10 of the 357 `.v` files change.

| Patch | Files | Cause (upstream change) | Change |
|---|---|---|---|
| `0001-ssreflect-done-moved` | `util/tactics.v` | Rocq 9.3 moved ssreflect's core (`done`, `phant`, …) into `Corelib.ssr.ssreflect_rw`. The Ltac reference `ssreflect.done` no longer resolves ("The reference ssreflect.done was not found") | `ssreflect.done` → `ssreflect_rw.done`. The tactic body is textually identical in both versions (Rocq 9.0 `ssreflect.v:395`, Rocq 9.3 `ssreflect_rw.v:344`) |
| `0002-hb-instance-stray-identifier` | `util/seqset.v` | `HB.instance Definition _  setSubType := …` has a stray identifier. Rocq 9.0 ignored it; the elaborated module has no extra argument (`HB_unnamed_factory_2 : ∀ T, isSub.axioms_ …`). Rocq 9.3 rejects the syntax ("[def_body] expected after [ident_decl]") | the identifier is removed |
| `0003-of-binder-removed` | `util/seqset.v` | Rocq 9.3 **removed** the ssreflect `of T` binder outside constructors; its replacement is `& T` (Rocq 9.3 changelog, SSReflect, #21611) | `Definition set_of of phant T` → `Definition set_of & phant T` (same anonymous binder) |
| `0004-ssr-old-rewrite-goals-order` | `util/tactics.v` plus the 8 files that import MathComp without depending on `util/tactics` | MathComp 2.4's `mathcomp/ssreflect/ssreflect.v` had `Global Set SsrOldRewriteGoalsOrder`. MathComp 2.6 dropped it, so `rewrite` with side conditions orders its subgoals differently and Prosa's scripts fail (`util/list.v:34`, `div_mod.v:157`, `unit_growth.v:286`, `sum.v:172`) | `Global Set SsrOldRewriteGoalsOrder.` restores the environment Prosa was written against; no proof script changes |
| `0005-sum-notation-level` | `results/transfer_schedulability/criterion.v` | MathComp 2.6 dropped `at level 41` from the reserved `\sum_` notations. `(t1 < t2) && \sum_(…) F == t2 - t1` now parses with the sum as the operand of `&&` (type error) | parentheses that spell out the parse elaborated in the original environment, which `Print slackless_interval` shows there as `(t1 < t2) && (\sum_(…) … == t2 - t1)` |

`util/tactics.v` is in the dependency closure of 347 of the 357 Prosa files. Its `Global Set` reaches
them as MathComp 2.4's did. The other 10 files were checked individually: the 8 that import
MathComp received the same line, and `behavior/time.v` and `util/epsilon.v` import nothing.

## Comparison with the original environment

`tools/compare_prosa.py` loads the released `rocq-prosa` 0.6 in the original environment (opam
switch `prosa-0.6`: Rocq 9.0.1, MathComp 2.4.0) and the patched build in the fixed one. For each
module it enumerates every declaration (`Print Module`) and compares the fully explicit printouts
(`Set Printing All`, opaque proofs included). Report:
`reports/m6/compat_comparison_finish_time.json`, covering the 26 modules of the FinishTime closure
(281 declarations).

* **IDENTICAL / IDENTICAL_MODULO_PRESENTATION:** all definitions of `behavior/{time, job,
  arrival_sequence, schedule, service}`, plus `finish_time`, `job_finishes` and `response_time`.
  The presentation differences are each named per declaration: scope-delimiter printing
  (`%_scope`), `return (T)` printing, the `ssreflect_rw` relocation, and HB unnamed-instance numbering.
* **INDUCTIVE_SAME_CONSTRUCTORS:** `ProcessorState`, `seqset.set`. Rocq 9.3 prints records with
  `Record` syntax and 9.0 as `Variant`; the arity and every constructor's full type are equal.
* **SAME_STATEMENT:** 177 declarations, almost all lemmas. Their statements are equal, but the
  same proof scripts elaborate to different proof terms under the newer libraries. The proof terms
  that are translated and kernel-checked are those produced by Prosa's original scripts in the fixed
  environment. Four Rocq-generated schemes of `setoid.leb` differ only in binder names and in
  `leb_rec` being expanded.
* **STATEMENT_DIFFERS:** 1 declaration, `util.bigop.big_pred1_seq`. Its hypothesis
  `P =1 pred1 i` elaborates through `ssrfun.eqfun`. MathComp 2.4 shadowed Corelib's with its own
  dependently typed `eqfun` (`eqfun (sort X) (fun _ => bool) P …`); MathComp 2.6 no longer does, so
  Corelib's non-dependent one is used (`eqfun bool (sort X) P …`). Both unfold to
  `∀ x, P x = pred1 i x`. The difference comes from the library change; the Prosa source is
  unchanged.

## Reproduce

```sh
scripts/setup-prosa              # FinishTime closure; --full for all of Prosa
python3 -I tools/compare_prosa.py reports/m6/compat_comparison_finish_time.json prosa.behavior.service ...
```

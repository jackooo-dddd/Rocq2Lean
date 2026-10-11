# M6 completion — the FinishTime proof-dependency closure

**Verdict: `M6_FINISHTIME_COMPLETE`** — with one stated validation boundary (statement
specializations of 159 dependencies, §5) and a fresh-holdout result that shows the limits of the
new rules beyond this closure (§6).

`prosa.analysis.definitions.finish_time.completes_at_finish_time`, whose Prosa proof ends in `lia`,
is translated and verified together with the four FinishTime roots reported in M6: one fresh run of
the strict gate (`scripts/m6-finishtime-gate`), required closure **1717 declarations**, every
proof the proof term of Prosa's own script in the compatibility-patched environment, kernel-checked,
independently audited, consumer-checked with empty transitive axiom sets, and current. No tactic is
translated, no proof is replaced: the `lia` certificate (a `ZMicromega` witness checked by
reflection) and its whole dependency closure — positive/integer arithmetic, `Ring_polynom`'s
normalizer, `Tauto`'s CNF checker, `ZMicromega`'s checker and soundness proofs — are migrated as
Rocq produced them.

Toolchain unchanged: Lean v4.33.1, Rocq 9.3.0, MathComp 2.6.0, MetaRocq Template `c18395ad`
(switch `rocq930-mc`, `toolchains.lock.json`). Prosa v0.6 from the sha512-checked release with the
five compatibility patches of M6 (`compat/prosa-0.6`), unchanged.

Read this report with its main validation boundary in mind (§5): **159 dependencies of the closure
are statement specializations** — their Lean statement is the source statement at a universe
instance that Rocq's kernel re-checks — and none of them is a requested root.

## 1. Baseline (implementation at b29ab03, commit 795a5dc)

| Run | Result |
|---|---|
| `scripts/test-all` | 18/18 |
| strict gate (`scripts/m6-finishtime-gate`, new) | FAIL as expected: four roots TRANSLATED_AND_CHECKED, `completes_at_finish_time` BLOCKED_DEPENDENCY |
| `scripts/test-m6-prosa` (rewritten: fixed requests in `fixtures/m6/regression`) | behavior61 (closure 426), finishtime4 (123), holdout13_prosa (411), holdout14_mathcomp (132) VERIFIED; the original 20-root holdout request: 13/20 translated, reported AUDIT_REJECTED, never VERIFIED |
| blocker graph of `completes_at_finish_time` (`tests/m6/blocker_graph.py`, types and bodies) | closure 1716, 792 accepted, **34 leaves** (30 missing features, 1 exporter/metadata defect, 3 universe solving), 890 pending only through dependencies |

All in `reports/m6/baseline/`.

## 2. Progress of the closure

| Step | Accepted / closure | Leaves |
|---|---|---|
| baseline | 792 / 1716 | 34 |
| + ι-generalized and mutual fixpoints | 1192 / 1716 | 22 |
| + ζ, functional fields, non-uniform fixpoints, δβ-inlining, course-of-values, universe rules (R3↓, plain inductive levels, R2B-S, the specialization rule) | 1555 / 1716 | 8 |
| + nested inductives (trivial auxiliary motives), cast repair, δ-inlining of `Set`-motive constants, per-declaration resource limits | **1715 + 2 bootstrap / 1717** | **0** |

Machine-readable: `reports/m6/completion_progress.json`, blocker graphs
`reports/m6/baseline/completes_blocker_graph.json` and `reports/m6/completes_blocker_graph_final.json`.

## 3. Rules added (each with an independent auditor copy, positives and mutations)

Every rule is a reusable lowering, applies only where the previous translation failed or the shape
is new, and is documented in `docs/SUPPORT_PROFILE.md`, `docs/TRUST.md` and
`docs/UNIVERSE_TRANSLATION.md`. "Mutation" means a type-correct change of a target term that Lean's
kernel accepts and the structural audit rejects (`test-m6`).

| Rule | Real instances | Positives | Mutation |
|---|---|---|---|
| ι-generalized fixpoints (decreasing match not outermost) | `Pos.eqb`, `Pos.compare_cont`, `Z.pos_sub`, `ListDef.nth` | `iotafix` (incl. a dependent return clause), `stdfix`, open-variable reflexivity lemmas | minors of two constructors swapped |
| mutual structural fixpoints (joint recursor into `PProd`) | `Pos.add/add_carry`, `Pos.sub_mask/sub_mask_carry`, inline copies in proofs | `mutfix`, `stdfix`, cross-function step lemmas | wrong projection; a call redirected to the other function |
| ζ of let-bound partial recursive applications | `Pos.peano_rect` | `sumto`, `stdfix` | changed generalized argument |
| functional recursive fields; non-uniform outer-match fixpoints | `Acc_rect`, `Acc_inv` | `walk`, `stdfix` | changed argument of the functional field |
| δβ-inlining of a constant the fixpoint passes itself to | `Ring_polynom.Padd/PaddI/PaddX/Pmul`, `EnvRing`, `Tauto.xcnf/mk_and` | `padd`, `count` | changed argument of an inlined call |
| course-of-values recursion (`PProd (M x) (Below x)`, convoyed matches) | `Ring_polynom.norm_aux`, `EnvRing.norm_aux` | `norm` (depths 2 and 3) | a call reading another field's result |
| nested inductives, trivial auxiliary motives/minors | `ZMicromega.ZArithProof_ind`, `ZChecker`; `M3Neg.rose_size` | Stdlib micromega run | negative: recursion through the nesting (`rsize`) rejected |
| cast repair (proofs only) | `Ring_polynom.norm_aux_PEadd`, `EnvRing.norm_aux_PEadd`, `Pos.sub_mask_carry_spec` | real Stdlib lemma | detector: a leaf other than the transported proof |
| δ-inlining of `Set`-motive constants (last tier) | `Nat/N/Z.strong_right_induction`, `Z.strong_left_induction` (`well_founded_induction`) | Stdlib run | detector: an unreported inlining |
| R3↓ downward instantiation | `ZMicromega.ZArithProof` (`PolC Z`) | `proof`/`Box` in `fixtures/cumul` | forged unrelated argument |
| plain universe parameters for inductives (R2F after) | `Ring_theory.ring_morph` → `RingMicromega.SORaddon`, `IDmorph` | Stdlib run | — (the R2F interpretation is the fallback) |
| R2B-S result-sort lowering | `ZMicromega.ZWitness` | `up_nat` | negative `up_binder` |
| R2B-P restricted by a source obligation; statement specializations | `Corelib.Classes.Morphisms` obligations (A : Type@{77} meeting `respectful`'s shared level at `Prop`), `OrderedRing`/`RingMicromega` `*_morph_Proper` | `uses_n`; `length_rev`/`in_rev` closure (10 specializations, each INSTANCE_OK) | negatives `prop_in_m`; a specialized row requested as a root is refused |

Recorded but unused in the final closure: the bounded solver for postponed `max` universe constraints
(candidates validated by Lean's level unification, R3 and the kernel; unsatisfiable constraints and
solver limitations are classified apart). Plain inductive levels removed the only real need
(`IDmorph`), and no fixture exercises it; it has no positive control.

## 4. Validation of the M5/M6 rules (§2 of the brief)

* **R2B-P** (`Set < m` read as `Set ≤ m`) now needs a source-derived argument per change: `verify`
  maps the Lean solution back to a Rocq level and has Rocq's kernel re-check the source declaration
  at that instance (`Rocq2Lean CheckInstance`, a fresh `rocq compile`), failing the run otherwise.
  A relaxed level of the declaration's *statement* makes the row a specialization of the source
  statement at that instance: allowed for dependencies, refused on roots, reported (`in_type`), and
  required by the auditor to be reported. Negative controls where the same-looking constraint has
  another origin: `prop_in_m` (its own typing needs `Set < m`); `up_binder`.
  The baseline accepted the Morphisms obligations under an unexplained relaxation — `∀ A :
  Type@{77}` became `∀ A : Type` with no recorded justification. They are now accepted only as
  checked specializations; no historical positive was lost.
* **R3↑** has a documented correspondence rule (`docs/UNIVERSE_TRANSLATION.md`) checked by translator
  and auditor; positive MathComp `Monoid.isLaw/isComLaw.phant_axioms`, negative forged argument.
* **Accessibility lowering** (`docs/TRUST.md`): the auditor reconstructs the carrier from the source
  and the call relation's shape (one disjunct per source call); a scoped argument explains why the
  relation's contents cannot change computed values, with executable checks: the empty relation is
  kernel-rejected, a result mutation is kernel-accepted and audit-rejected, 4 Rocq/Lean computations
  agree, and the lowering unfolds on an open proof (`search_step0`).
* **Computation.** `compute_m6`: 42 closed computations evaluated independently in Rocq (cbv,
  quoted) and Lean (normalization) agree, over every new recursion rule and the real Stdlib
  functions; open-variable computation rules are proved by reflexivity in each fixture.
  The `Nat.sub 3 3 = 0` regression (`fixtures/fixref`, `test-m5`) is unchanged and passes.

## 5. Validation boundaries and transformations

* **Statement specializations: 159 rows of the closure.** Their Lean statement is the source statement
  at a universe instance (a level forced to the image of `Set`); each instance is accepted by Rocq's
  kernel (`source_instances.json`); none is a requested root. This is a real difference from the
  source: such a dependency is less general in Lean. It does not affect the five roots' statements.
* Definitional preprocessing, re-derived independently by the auditor: ζ of recursive lets;
  δβ-inlining of constants receiving the fixpoint; δ-inlining of `Set`-motive constants (reported per
  row); ι-reduction of matches on the decreasing argument.
* Generated proof terms that implement lowerings (no replacement proofs): accessibility certificates;
  cast repairs (the transported source proof is every leaf).
* Source preparation: the M5 sealed-implementation and `ssr_have_upoly` preparation, unchanged.
  Prosa: the 5 compatibility patches, unchanged; the comparison with the original environment is
  compatibility evidence, not a semantic proof.
* Resource limits per declaration (deterministic, recorded): Lean recursion depth 8192 and 5× the
  default heartbeats, because reflection proofs evaluate the translated normalizers during the checks.

## 6. Results on the final implementation (commit 33ed468)

| Run | Commit | Result |
|---|---|---|
| strict gate `scripts/m6-finishtime-gate` | 33ed468 | **PASS**: five roots TRANSLATED_AND_CHECKED, VERIFIED, current; closure 1717; consumer OK (1715 accepted rows, 9591 recursor applications, 29680 instance levels, 0 problems); 159/159 source instances INSTANCE_OK (`reports/m6/finishtime_gate.json`) |
| `scripts/test-all` | 41dcc0a (implementation of 33ed468) | **18/18**, 361 checks, 0 failed (`reports/test_all.json`) |
| `scripts/test-m6-prosa` | 33ed468 | behavior61 (426), finishtime4 (123), holdout13_prosa (411), holdout14_mathcomp (132) **VERIFIED**; the original holdout20 request **15/20** (baseline 13/20), reported AUDIT_REJECTED, never VERIFIED; its 5 blocked roots need MathComp `leqif` (`prod` at `Prop`) or `bigop.big_const_seq` (a proof-local universe fact) (`reports/m6/m6_prosa_results.json`) |
| small `lia` theorems (`fixtures/lia`, five `lia` proofs over `nat` and `Z`) | dev, before the gate | VERIFIED, closure 1602 |
| `test-m6` | 41dcc0a | 38 checks: positives, 9 type-correct kernel-accepted/audit-rejected mutations, detector checks, 42/42 Rocq-vs-Lean computations |

**No historical positive was lost.** Earlier suites changed only where former rejections are now
supported: `M3Neg.evenR` (mutual), `M3Neg.half` (course-of-values), `M3Neg.rose_size` (nested),
Corelib `nth` (ι-generalized) — each now verified, the tests updated accordingly.

**Fresh holdouts after `m6-completion-freeze-1`** (`reports/m6/holdout_completion_selection.json`,
selected deterministically after the tag and committed before the single run;
`reports/m6/holdout_completion_results.json`):

| Request | Translated | Blocked by |
|---|---|---|
| 18 Prosa util lemmas (`prosa.util.{sum,div_mod,list}`, proofs with `lia`) | **9/18** translated and kernel-checked. As their own request the 9 are refused by verify: the dependency `Corelib.ssr.ssreflect_rw.nary_congruence` (needed by `sum_split_exhaustive_mutually_exclusive_preds` only) relies on an R2B-P relaxation whose Rocq source instance is rejected (`INSTANCE_REJECTED`), so the obligation fails closed. The other 8, as their own request: **VERIFIED**, closure 1895 (`fixtures/m6/regression/holdout_completion_prosa_verified8.json`, `runs/m6h-verified8`) | MathComp `div.edivn_rec`/`modn_rec` (recursion on the result of `subn`, a subterm only through a function's output — not supported); MathComp universe forms: `fintype.isFinite.axioms_`, `choice.PCanHasChoice`, `seq.mask_cat`, `bigop.big_const_seq`, `bigop.big_morph` |
| 8 MathComp `div` lemmas | **0/8** | `edivn_rec`/`modn_rec`, as above |

The holdouts show that the closure's rules are not yet general enough for MathComp's `div`
(non-structural subterm recursion through `subn`) and several MathComp universe shapes. These are
new, precise blockers for the next task, not regressions.

## 7. Counts (definitions and theorems separately)

| Set | Definitions | Theorems / opaque | Inductives | Total |
|---|---|---|---|---|
| five-root closure (gate) | 642 | 1005 | 70 | 1717 |
| `completes_at_finish_time` alone | | | | 1716 |
| unique declarations over the verified M6 runs (finishtime5, behavior61, finishtime4, holdout13, holdout14) | 773 | 1209 | 85 | 2067 (sum of closures 2809) |
| of which Prosa | 65 | 85 | 2 | 152 |

`reports/m6/unique_declarations.json`, `reports/m6/completion_progress.json`.

## 8. Reproduction and evidence

* **Clean checkout** (`scripts/m6-clean-reproduce 33ed468`,
  `reports/m6/clean_reproduction/`): fresh `git clone`, `lake build` from an empty `.lake`, the
  exporter plugin built by export, Prosa v0.6 rebuilt from the sha512-checked release with the
  patches, then the gate: **PASS**, closure 1717, 21 minutes. The exported IR is identical to the main
  run's except for one provenance record (the absolute paths of 5 Prosa `.vo` files, which name the
  checkout directory); every declaration line is byte-identical. Rebuilt: translator, exporter,
  Prosa. Reused: elan Lean v4.33.1, the opam switch `rocq930-mc` (Rocq 9.3.0, MathComp 2.6.0,
  MetaRocq), the opam cache entry of the Prosa release (checksum-verified).
* **Evidence archive** (`scripts/m6-package-evidence`): `rocq2lean-m6-evidence-33ed468.tar.gz`,
  64 MB, 318 files, archive sha256 `2e7995814430d3b5c9213cf0fe6cdd5b6c326e54cace8608bfdefa85eda12a9d`;
  the source tree of 33ed468, the lock, the gate's run directory (IR, contract, snapshot, round
  trip, source instances, translation report and manifest, Lean artifact `.lean/.olean/.ilean`,
  consumer result, audit, verify, logs), the fixed request, the gate/Prosa/test-all reports, the clean
  reproduction, the compatibility patches and Prosa's patch record, and `COMMANDS.md`. The archive
  is kept outside git (on the build machine, `reports/m6/evidence/`); its full sha256 inventory is
  committed (`reports/m6/evidence/package.json`).
* Binding: implementation tree sha256 `819383b9…`, source IR sha256 `45c0e04b…`, toolchain
  fingerprint `b3abee0c…` (`reports/m6/finishtime_gate.json`).

## 9. What remains outside this milestone

* Recursion through the nesting of a nested inductive, and the course-of-values, mutual and
  accessibility lowerings on nested or indexed inductives: rejected explicitly.
* Mutual fixpoints whose functions decrease at different positions or have different leading
  argument types (e.g. a separate global universe per `A : Type`).
* A cast on data whose conversion needs a fixpoint to unfold at open arguments (only proofs are
  repaired).
* Template-`Prop` support was not needed by the closure and was not started.

# Blocker reassessment under the statement-only policy

Input:
* every blocker known from the proof-transport work (`reports/prosa_inventory/blockers.json`, P0);
* the measured statement-mode corpus run (`TRANSLATION_RESULTS.json`).

"Protected blocked" counts the protected Prosa/Classic declarations that fail only because of the
blocker (transitively, `BLOCKED_DEPENDENCY`). Phase B's closure-only projection
(`blocker_reassessment.json`) is superseded by the measured verdicts below.

## Removed: only original proofs needed them (measured: absent from the statement closure)

| Blocker (proof transport) | Why it disappears |
|---|---|
| `mathcomp.boot.eqtype.Sub_spec`, `eqtype.insub_spec` (universe; cast annotation) | used only inside proofs |
| `bigop.big_const_seq`, `bigop.big_morph`, `seq.mask_cat` (proof-local universe levels) | opaque lemmas reached only from proofs |
| template `prod` at Prop: `ssrnat.leqif`, `ssrfun.pair_of_and`, `ssrnat.nat_of_add_pos` | reached only through proofs |
| `Corelib.Classes.Morphisms.normalization_done` (coinductive) | setoid-rewriting marker inside proofs |
| SProp eliminators (`*_sind`) | generated schemes, not reached |
| `lia` / micromega certificate closure | proof-only (part of the 4,966 eliminated declarations) |
| `Corelib.ssr.ssreflect_rw.nary_congruence` (R2B-P instance of its proof body rejected by Rocq) | Phase B reached it through a proof subterm inside a CoqEAL refinement definition; the exporter extracts that subterm as an obligation, so it leaves the closure |

## Resolved in statement mode (measured: translated and audited)

| Declaration | Old problem | Now |
|---|---|---|
| `mathcomp.boot.choice.PCanHasChoice` | proof-local level in a tactic-built body | opaque data: its type is the interface (sort inferred), a value is a proof task |
| `mathcomp.boot.fintype/isFinite.axioms_` | request-dependent template levels (fixed in P0) | translated and audited |
| `mathcomp.boot.ssrnat.find_ex_minn` | (statement mode, first run) recursion on a proof subterm | opaque data (`Qed`): its type is the interface, a value is a task; all five FinishTime roots validated |
| `prosa.behavior.schedule.State` | (first corpus run) only accepted with R2B-S on a protected declaration | R3G refinement: levels of the referenced `ProcessorState` taken as implicit parameters and read through R2F; no narrowing |

## Still blocking (measured)

| Declaration | Status | Protected blocked | Nature and next step |
|---|---|---|---|
| `mathcomp.boot.div.edivn_rec` | `UNSUPPORTED_FEATURE` | 694 | `fix` recursing on `m'` where `m - d = m'.+1`. Rocq's guard sees through `subn`, Lean's structural recursion does not. Needs a rule: lowering with a termination obligation (a proof task, never assumed); the exporter already records deferred termination |
| `mathcomp.boot.div.modn_rec` | `UNSUPPORTED_FEATURE` | 490 | same |
| `prosa.model.priority.definitions.JLFP_policy`, `FP_policy`, `JLDP_policy` | `UNIVERSE_REJECTED` | 447, 248, 225 | R3: argument `ssrbool.1105` for `eqtype.51` at the reference to `JobType`/`TaskType`; `1105 ≤ 51` is not entailed by the native graph. Known since P0; unchanged by the statement policy |
| `prosa.model.processor.ideal.processor_state__rocq2lean_obligation_{1,2}` | `UNIVERSE_REJECTED` | 280 | residual universe levels in the obligation statements not justified (the generic declaration is not valid for every value); to investigate |
| Classic `SporadicTaskset.taskset_of`, `Affinity.affinity`; modern `ArrivalCurvePrefix` | `INTERFACE_REJECTED` | 216, 189, 195 | the only accepted translation lowers the result sort (R2B-S) of a protected declaration; refused (no approved representation change) |
| MathComp `nmodule` HB structures (`BaseAddMagma_isAddMagma.axioms_`, `isNmodule.phant_axioms`, builder obligations) | `KERNEL_REJECTED`, `UNIVERSE_REJECTED` | 79 | `reverse_coercion` at a sort Lean cannot match without cumulativity; HB phantom levels solved below their facts |
| Classic `uni.basic.extraction_tdma.Task_T` | `UNSUPPORTED_FEATURE` | 12 | coinductive datatype: no rule |
| Classic `jlfp_instantiation`, `workload_bound`, `nonpr_reg`, `priority_inversion_is_bounded` definitions (5) | `UNIVERSE_REJECTED` | 3–12 each | R3 at references to `Equality.type` (`ssrbool.1105`/`1171`), same family as `JLFP_policy` |

Direct failures by kind, over the whole closure (343 declarations, mostly MathComp-internal):
* 319 `UNIVERSE_REJECTED`, 268 of them HB builder obligations referencing `hasChoice.axioms_`;
* 14 `INTERFACE_REJECTED`;
* 7 `KERNEL_REJECTED`;
* 3 `UNSUPPORTED_FEATURE`.

## Source assumptions

The 4 Classic `Admitted` facts (`tdma_rta_example`) are blocked by their dependencies:
* `WCRT` through `div_ceil`, `divn` and `edivn_rec`;
* `periodic_arrival_sequence` through `concrete_taskset` and `taskset_of`. When translated, they become proof tasks of kind
`source_assumption` and are never counted as proved.

The previous T1–T4 task order and its unlocked-root counts are not valid under this policy and are
not used.

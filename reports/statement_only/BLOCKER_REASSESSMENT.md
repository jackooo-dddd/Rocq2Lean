# Blocker reassessment under the statement-only policy

Input: every blocker known from the proof-transport work (`reports/prosa_inventory/blockers.json`,
P0), checked against the statement-only closure (`SCOPE_AND_DEPENDENCIES.md`). "Roots reaching"
counts protected Prosa/Classic declarations whose statement closure reaches the declaration. Data:
`blocker_reassessment.json`.

**Status of this assessment (Phase B).** It is a closure analysis. A blocker that is "still
required" is still *on the path*; whether it still *fails* in statement mode is settled by running
the statement translator (Phase C/D). The results are recorded in `TRANSLATION_RESULTS.json` and the
verdicts below are updated there.

## Removed: only original proofs needed them

| Blocker (proof transport) | Why it disappears |
|---|---|
| `mathcomp.boot.eqtype.Sub_spec`, `eqtype.insub_spec` (universe; cast annotation) | used only inside proofs (`insubP`-style reasoning); no statement or definition reaches them |
| `bigop.big_const_seq`, `bigop.big_morph`, `seq.mask_cat` (proof-local universe levels) | opaque lemmas reached only from proofs |
| template `prod` at Prop: `ssrnat.leqif`, `ssrfun.pair_of_and`, `ssrnat.nat_of_add_pos` | `leqif` is a definition but reached only through proofs |
| `Corelib.Classes.Morphisms.normalization_done` (coinductive) | setoid-rewriting marker inside proofs |
| SProp eliminators (`*_sind`, 11 schemes) | generated schemes, not reached |
| `lia` / micromega certificate closure | proof-only (part of the 4,571 eliminated declarations) |

## Only the statement matters now

| Declaration | Old problem | Now |
|---|---|---|
| `Corelib.ssr.ssreflect_rw.nary_congruence` | R2B-P instance of its *proof body* rejected by Rocq | reached as an obligation statement (via a CoqEAL refinement definition); its body is never translated, so the problem goes away; 438 modern / 744 Classic roots reach it |
| 4 Classic `Admitted` facts (`tdma_rta_example`) | source assumptions | statement tasks labelled as source assumptions; never counted as proved |

## Still required: datatypes and computation

| Declaration | Needed for | Roots reaching (modern / Classic) | Notes |
|---|---|---|---|
| `mathcomp.boot.fintype/isFinite.axioms_` | datatype, statement, computation | 1,118 / 708 | request-dependent failure fixed in P0 (template levels) |
| `mathcomp.boot.choice.PCanHasChoice` | computation (choice structure of countable types) | 437 / 744 | opaque data built by tactics; proof-local universe level in its body; re-test in statement mode |
| `mathcomp.boot.div.edivn_rec`, `modn_rec` | computation (`divn`, `modn`: hyperperiods, Classic arithmetic) | 165 / 530; 97 / 396 | recursion through `subn`: missing fixpoint rule, still a genuine blocker |
| Prosa `FP_policy`, `JLFP_policy`, `JLDP_policy` | statement, computation | 249; 448; 226 (modern) | universe entailment at references to `TaskType`/`JobType`; re-test in statement mode |
| `prosa.implementation.definitions.extrapolated_arrival_curve.ArrivalCurvePrefix` | datatype, statement | 196 / 0 | `INTERFACE_REJECTED`: needs R2B-S on a protected definition; requires an approved representation rule |
| `prosa.implementation.definitions.task.concrete_job` | statement | 48 / 0 | blocked by `ArrivalCurvePrefix` (P0) |
| Classic `extraction_tdma.Task_T` | statement | 0 / 13 | coinductive datatype: missing rule |

## Not yet known

The statement translator has not run on the whole closure yet. Statement translation removes all
proof-body universe problems, but it adds:
* obligation extraction for 300+ definitions;
* phantom-witness obligations in 121 statements.

New statement-level failures, if any, will appear in Phase C/D and be listed here.

The previous T1–T4 task order and its unlocked-root counts are not valid under this policy, and are
not used.

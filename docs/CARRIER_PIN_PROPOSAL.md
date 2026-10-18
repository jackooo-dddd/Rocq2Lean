# Proposal 3 (draft): a level free in the source, pinned by a packed carrier

Status: **draft, not adopted; experiment numbers to be filled in.** Prompted by stage B of proposal 2
(`docs/SOLVER_STAGE_B.md`): after the solver work, the largest remaining blockers of protected roots are one
shape, a *carrier* placed in a structure's carrier slot.

## 1. The shape

MathComp/HB structures (`Equality.type`, `Choice.type`, the HB mixins) carry their carrier type in a field of
sort `Type@{c}`. Rocq packs a concrete carrier `T : Type@{t}` there by cumulativity (`t ≤ c`); the instance is
a monomorphic constant at a global level `c` that the source leaves free above `t` (often `Set`).

Lean has no cumulativity: the carrier field of `S.type.{…, c, …}` holds exactly a `Type c`, so packing `T` at
level `t` forces `c := t` at that instance. Two refusals follow, both by the generality policy, not by typing:

* **statement specialization refused** (STATEMENT_FREE_LEVEL_PINNED): an unprotected statement mentions the
  instance with `c := t` although `c` is free in the source ("no applied argument determines it, the source
  graph does not force it"). Examples: `ssrint` (`int : Set` at `choice.299`, the GEL frontier), Classic
  `ts_obligation_1` (`fintype_ordinal` at `ssrbool.1169`), `slackless_interval_continuation`.
* **cross-declaration coupling**: a declaration that uses the instance at its own level identifies the carrier
  slot with it (`task.43 := max(u_51, u_21)`), and a generated prerequisite statement that fixed the carrier's
  level refuses the raised argument (the `eqn_task_arrivals_bound` obligation, 10 Prosa refinement roots).

## 2. The rule (candidate)

At a reference to a constant, an argument for a level `c` that is free in the source may be the level `t` of a
carrier packed at that position, when

1. the instance's carrier field is that carrier (syntactically, after the translation), and `t` is its level;
2. the source graph allows `c = t` (every fact on `c` holds with `c := t`; in particular `t ≤ c` is entailed);
3. the referring declaration is not protected (P0 unchanged: protected statements are never specialized);
4. the row reports the pin (`carrier_pins: [(constant, level, t)]`).

Correspondence: the Lean statement is the Rocq statement in the model `c := t` of the source graph, which
condition 2 makes a model. For a monomorphic Rocq constant this is an instance of the statement Rocq checked, not a
different one; the loss is generality at `c` only, and only where Lean cannot express the cumulative packing.

Independent audit: recompute (1) from the target term, (2) from the native facts, (3) from the pinned protection
list; reject a row whose pins are not all justified or not all reported.

## 3. Measured (experiment `R2L_EXP_NO_PIN`, the refusal disabled for unprotected statements; upper bound)

* GEL/HB frontier (16 declarations, 2,139 with closures; `solver-b` + the switch): the **6 `ssrint` members
  accepted** by the translator (the comMixin obligations 16/23/26/32, `mulz_addl`, `subz_ge0`); the other 10 fail
  as before (7 `order` binder levels / proof-local 119, 3 builders). The independent audit rejects exactly the
  pinned rows (7: the 6 and `choice.HB_unnamed_factory_57` obligation 1), as it should: it enforces the generality
  policy on its own. 32 previously claimed rows change (the relaxation was on every tier, so HB instances were
  accepted earlier with a pin instead of later without one; a rule would be a last tier only). GEL protected
  roots gained: 0 (they need the whole frontier).
* Non-GEL failing protected roots (126 roots, 1,887 declarations; `solver-b` + the switch): 54 protected roots
  claimed against S21b (25 with `solver-b` alone), 0 claimed rows lost. But the audit rejects 100 rows, 29 of
  them protected, and **every one of the 29 extra protected roots is among them**: a protected statement that
  mentions a pinned instance is itself specialized (P0). Audit-clean protected gain of the switch: **0**.
  The 29 by pinned level:

  | Pinned at | Level | Protected rows |
  |---|---|---|
  | `fintype_ordinal` `eqType`/`finType` instances (Classic `apa` examples: `ts_obligation_1`'s dependents) | `ssrbool.1169` | 11 |
  | `JobCost`, `JobArrival`, `concrete_task`'s `eqType` instance | `eqtype.58` (the class level) | 15 |
  | `TaskPriority`, `ConcreteMaxArrivals` | `arrival_curve.21`, `task.40` | 3 |

  Only the first group is a carrier pin (`'I_n : Set` packed at `1169`). The other 18 pin a structure's class
  level to `0`; those are lowering artifacts of the `Job` kind (proposal 2, `docs/SOLVER_STAGE_B.md` §6), not this
  rule's shape.

**Conclusion for the decision.** Under P0 as it stands (protected statements never specialized), the rule gains
unprotected rows (the 6 `ssrint` frontier members, HB instances, obligations) but no protected root on these
subsets: the GEL roots also need the 10 other frontier members, and the non-GEL roots that it would unblock are
protected statements about pinned instances. The protected gain needs a decision on P0 for carrier pins: may a
protected statement mention a structure instance at its concrete carrier's level (11 Classic roots here)?

The experiment disables the refusal entirely (an upper bound); the rule above allows only carrier pins.

## 4. Not covered

The cross-declaration coupling of §1 (second bullet) is not a pin at a reference; it needs the carrier slot of a
*definition* to stay at the carrier's level (`task.43 := u_21`), a solver choice across declarations (proposal 2,
stage C/D).

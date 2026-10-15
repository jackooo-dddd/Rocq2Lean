# R-CARRIER: per-operand carrier universe levels (experimental rule)

Status: **experimental**, on branch `rules-carrier`; approved as Option 2 for case B on 2026-10-14. It is
not merged until it has been reviewed. ITERATION_LOG entry 11.

## 1. The failures, reproduced

The fixture `fixtures/stmt/cb` uses the real exporter and translator on the real MathComp declarations,
plus two synthetic Prosa-shaped statements (`Cb.v`). The pre-change report is
`reports/statement_only/carrier/pre_fixture_report.json`.

| Row | Failure before | Mechanism (actual source and target terms) |
|---|---|---|
| `pair_nat_refl` / `pair_nat_in` (`prod_eqType T nat_eqType`, Classic `fp_rta_comp`'s shape) | refused (`Equality.type`'s carrier 51 pinned at 0) | `prod_eqType (T1 T2 : Equality.type)` names its two operands' free carrier classes with one parameter `u_51`. `nat_eqType : Equality.type.{_, 0, …}` (it packs `Nat : Type 0`) then forces the generic operand to 0. |
| `HB_unnamed_mixin_107` obligations 2/4/8 (`Countable.type`'s carrier 959 pinned) | refused | Through `SubType` (the next row). |
| `eqtype.insub` (`695 := 0` against `Set < 695`) | refused | `SubType.type`'s parameter `T : Type@{573}` is read under R2F as `max(u573, u577)`, because of the fact `577 ≤ 573` (the sub sort below the base carrier). The projection `SubType.sort` cannot invert the `max`, so it identifies the carriers (`573 := u577`); `Sub` then pins both to 0 by R2B-P. |
| `fintype.HB_unnamed_factory_57` (`551 := 0` against `Set < 551`, `1169 ≤ 551`) | refused | **Not a carrier coupling.** 551 is the body level of the motive `K : ordinal n → Type@{551}` given to `isSub.axioms_`'s field `Sub_rect` (whose motive level is 542; `551 = 542` in the source). In statement mode a class containing an *own* level was represented by that level; here that level is proof-local, so the class was never named and 551 was defaulted to 0. |

(Correction to entry 10, which grouped `factory_57` with the structure-carrier couplings: it is the
fourth row's mechanism.)

## 2. The rule

All three parts are derived mechanically from the source and from typing, without names or whitelists.

**P1: a parameter carrier is not raised by its own block's other levels.**
* The *carrier levels* of a non-template block are the global levels occurring as the final sort of a
  parameter binder's type in its arity (`Split.carrierLevels`, audit `carrier_levels`).
* For each such carrier `l` and each other global level `m` of the *same* block (a field sort, the result
  sort, …), a source fact `m ≤ l` does not raise `l` in any R2F reading, of the block or of a constant.
  These pairs (`Split.decoupledPairs`, audit `DECOUPLED`) are computed once from the source.
* Every other lower bound still applies, as do all upper bounds.
* Rationale: in `SubType`, the fact `577 ≤ 573` (sub sort ≤ base carrier) made the reading
  `T : Type (max u573 u577)`, which tied the operand's carrier to the structure's own field. A parameter
  level stands for its operand's argument `a ≤ l`, R3-checked at every use (the R-SPLIT/R3G-F principle).
* Effect: `SubType.type : (T : Type u573) → …` with `ssort : Type u577` independent; `SubType.sort`, `Sub`
  and `insub` keep both carriers generic.
* (Corpus run 1 used a broader P1, every carrier level minimal everywhere. It dropped bounds such as
  `task_T`'s `t ≤ a` and changed readings across MathComp and Prosa, so it was narrowed; entry 11.)

**P2: implicit operand split.**
* When a declaration's type (a statement's statement) contains several *distinct* free classes of
  arguments for the same source level `l`, each class gets its own copy `u_<l>__c<k>`, instead of all of
  them being named `u_l`. These are classes that typing did not unify: independent operands such as
  `prod_eqType`'s `T1` and `T2`.
* Classes that occur only in the value join the first copy.
* The copies lie below `l` and inherit `l`'s upper bounds, as R-SPLIT's copies do.
* References read every copy as `l` (R3: `a ≤ l`). The report field `level_copies` lists them.
* **Dependencies are preserved by construction.** Whatever typing relates is one class: a repeated
  carrier, a field and its projection, operands required equal (`prod_same`'s `e : T1 = T2`). The kernel
  rejects a forged split of such a dependency.
* `nat_eqType`'s carrier stays `Nat`. Nothing is lifted, and no `ULift` occurs anywhere in the
  translation.
* **Refinements found on the corpus (entry 11):**
  1. Classes are counted after peeling off the generated prerequisite-hypothesis binders. Their
     instances are the translator's choice, so they must not create operands.
  2. A post-pass after solving maps a remaining `u_l` of a split level to its first copy, merges copies
     that no longer occur in the type, and returns a level left with one copy to `u_l`.
  3. At a reference, an argument at a copy position stands for an argument `a ≤ l`. It is R3-checked
     (no raising), but not held to the shared-level coherence rule.
  4. In the generality check, a declaration owning a copy of a level owns the level, as an own level
     does.
  5. In the generality check, an argument `max (u_a, u_b, …)` of own parameters for a referenced level
     `l` is accepted when every `a`, `b`, … is *equal* to `l` in the source graph (`a ≤ l` and `l ≤ a`).
     Such an argument is a referenced declaration's R2F reading of equal levels, not a specialization:
     the source has one level there. Found at `HB_unnamed_mixin_109`'s obligation 13 (`SubType`'s 577
     at `max (u1053, u959)`, with 1053 = 959 = 577 in the source). Translator (`freeLevelRef`) and
     audit (`check_statement_generality`) implement it independently. Since entry 13 it holds in the
     general form of rule R: an argument equal to `l` at every model of the source facts (for example
     `max (u_a, u_b)` with `a = l` and `b ≤ l`) is accepted (docs/COHERENCE_READINGS.md §6).

**P3: a proof-local level never represents a class.** In statement mode, only own *type* levels represent
the class of reference arguments they belong to. A proof-local level is solved and fact-checked by R2S
(`factory_57`: `551 := u542`, with the source facts `Set < 542` and `1169 ≤ 542`). This is within the
approved C-1/R3G policy.

## 3. Correspondence (synthetic, `tests/statement/proofs/carrier_correspondence.lean`)

These proofs are about the synthetic fixture `CbSyn.v` (an eqType/subType hierarchy with MathComp's
universe shape). They were written by a Codex worker and reviewed; there are 17 theorems, all
axiom-free:
* a lift of an eqT to a higher carrier universe, with round trips and preservation of `eqop`;
* `prodEq` at independent operand universes `(a, b)` against `prodEq` at `max a b` applied to the
  lifted operands: a carrier bijection (both round trips), and preservation of the equality operation;
* the same with `natEq` as an operand at universe 0, against a generic `eqT` at `a+1` (`natEq`'s carrier
  stays `Nat`);
* `subT` at independent base and sort universes against its lift: sort round trips, and commutation of
  `sval` and `ssub` with the lift;
* `insubT` on the lifted structure at `up x` equals `Option.map up (insubT x)`, with its pending
  prerequisite as an explicit hypothesis.

These proofs support the rule; they are not a complete cross-language correctness theorem.

## 4. Independent checks

* **Audit:**
  * `carrier_levels` and `CARRIER_SET` give the minimal R2F reading, recomputed from the source.
  * The `level_copies` pre-pass checks that each copy is a fresh `l__c<k>` of an implicit level of the
    row, is reported among its implicit levels, and occurs in its target type (its statement).
  * Copies are registered with R-SPLIT's copy→level map, which gives the facts and the R3 reading at
    references.
  * The generality check accepts an own copy of the referenced level. Every other check is unchanged.
* **Consumer:** every copy is a universe parameter of the imported declaration and occurs in its type
  (or its statement).
* **Controls** (`tests/statement/check_carrier.py`, 19 checks):

  | Kind | Control | Result |
  |---|---|---|
  | Negative | Accidental pinning of a generic carrier | kernel-accepted, audit-rejected |
  | Negative | A structure-level copy relabelled as a carrier copy (incorrect identification) | kernel-accepted, audit-rejected |
  | Negative | Splitting a genuine dependency | rejected by the kernel |
  | Negative | Restoring the P1 coupling on `subT` | the forged row is kernel-accepted, audit-rejected |
  | Positive | Mixed nonzero universes on fixture and real declarations | accepted |
  | Positive | `natEq`'s carrier is `Nat` | holds |

## 5. Boundaries

* **P1** applies to non-template blocks' parameter carriers only. Template levels keep R5.
* **P2** applies to free classes of implicit levels in a declaration's type. Explicit source levels are
  R-SPLIT's domain (binder sorts).
* **Not covered:**
  * a block whose *field* has a carrier level defaulted by R3″ (fixture `holder`, entry 10). Since
    entry 14 this is covered by R3G for field-only classes (docs/COHERENCE_READINGS.md §7);
  * coherence refusals from R2F `max` readings of non-carrier levels (REFERENCE_COHERENCE);
  * protected ranges narrowed by other mechanisms (`JobReady`).
  * R2F readings of *source-equal* levels. Where the source makes two own levels equal, R2F reads both
    as `max (u_l, u_m)`. A referring declaration then sees arguments `max (?a, ?b)` that R3G cannot name.
    A definition defaults them (fixing e.g. `choice`'s sub-type Countable instance at carrier 0), and
    the specialization reaches a later statement as a refusal (`fintype.HB_unnamed_factory_66`'s
    obligation 1: `ordinal`'s 1169 at 0). Two repairs were tried and not kept:
    * one parameter per source-equal class at the definition (R2F-eq);
    * identifying the summands of such a `max` at the use (P4).
    In the corpus-wide facts these classes are large (one class has 232 levels, including `eqtype.51`,
    `choice.959`, `eqtype.577`, `ssrbool.1169` and `fintype.101`). Both repairs therefore merged
    independent Prosa carriers, which lost protected `schedule`/`service` rows to coherence refusals.
    Entry 11 records this as the next frontier.

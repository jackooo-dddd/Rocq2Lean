# Proposal (NOT adopted): rule Q, sort arguments of HB phantom checks

Status: **proposal awaiting a decision** (2026-10-15). Nothing here is implemented.

## 1. Measured frontier

The largest remaining group, after stage 3, blocks 79 protected roots, among them
`prosa.model.priority.gel.GEL`, `GEL_is_total`, `elf.ELF` and `generality.gel.pp_delta`. Each of these
roots needs **the same 315 failing MathComp declarations**: the HB builders and obligations of
`order`/`nmodule`. Classified on the complete frontier of `GEL` (run S3):

| Members | Shape |
|---|---|
| 306 | A level solved by typing violates a source fact (SOLUTION_FACT_VIOLATED), in a declaration whose type contains HB's phantom check `HB.structures.unify`. |
| 5 | HB `axioms_` blocks rejected by the kernel at `reverse_coercion`. Stage 4's δβ-inlining targets this shape; re-measured in entry 14. |
| 4 | Statement specializations (`HB_unnamed_factory_64` obligations). |

None of the 79 roots is unblocked unless the 306 are.

## 2. The mechanism (`Order.isPreorder.phant_Build`)

```
phant_Build (d) (T : Type@{4375}) (m) (Tlocal : Type@{4376}) …
  (s : Equality.type)
  (unif_arbitrary0 : HB.structures.unify Type@{4379} Type@{4380} Tlocal (Equality.sort s) msg) …
HB.structures.unify T1 T2 (t1 : T1) (t2 : T2) s := phantom T1 t1 -> phantom T2 t2      (Prop)
```

* Rocq type-checks `Tlocal : Type@{4379}` and `Equality.sort s : Type@{4380}` by cumulativity:
  `4376 ≤ 4379` and `51 ≤ 4380`. The source graph also makes **4379 = 4380**.
* Lean has no cumulativity. The only well-typed arguments are `Type u4376` and `Type u51'`, so typing
  solves `4379 := u4376` and `4380 := u51'`.
* The approved solving rule (R2S) then checks the native facts with these solutions. `4379 = 4380`
  fails, correctly, because the two solutions differ.
* No representation with one Lean level for 4379 and 4380 is well-typed unless `Tlocal`'s universe
  *is* `s`'s carrier. That would be a specialization.

The binder is a trivially true proposition, since `phantom T t` always has its constructor. The levels
4379 and 4380 occur only as the type arguments of that check.

## 3. The proposed rule Q

A sort `Type@{l}` written as a **type argument** of a reference, where the referenced parameter is
`T : Type@{…}` and the next argument is a term of type `T`, is translated *per occurrence*. It is
lowered to the level of that argument's own type: `Tlocal`'s universe.
* This is R3↓ (Rocq used `Type@{l}` with an argument of a lower level by cumulativity), applied to sort
  arguments instead of universe instances.
* Every such occurrence is R3-checked: the lowered level must be entailed ≤ `l`.
* Restricted to occurrences inside **proof binders** (binders whose type is a `Prop`). There the
  universe annotation of a type argument changes no quantification range of data.
* The level `l` itself is then no longer solved, so its facts constrain nothing: the source fact
  `4379 = 4380` relates two sorts that the Lean term no longer has.

## 4. Why this is a decision, not an implementation detail

* It relaxes R2S's fact obligation for these levels. They are not solved; their occurrences are lowered.
* In general, a proposition such as `P (Type@{l})` and its lowered form `P (Type@{a})` are *different*
  propositions.
* For HB's phantom `unify` they are equivalent: both sides are inhabited by the phantom constructor.
  A general rule must either:
  * (a) be restricted to arguments of definitions whose value is such a phantom. That criterion is
    recomputed from the source, but it is still a new semantic class; or
  * (b) accept that lowering inside a proof binder may change which proposition is assumed. Since the
    lowered proposition must still be kernel-checked against every use, a wrong one makes uses fail,
    not succeed. But a hypothesis that is *weaker* or *stronger* than the source's changes the meaning
    of the statement, which the protection policy forbids for protected statements.

## 5. Options

| Option | Rule | Expected effect | Correspondence obligation |
|---|---|---|---|
| Q-a | Phantom-only: lower sort arguments only inside applications of definitions whose body, after its λs, is a product of `phantom T t` propositions. | The 306 members; then the 79 roots, if the 9 others also clear. | For every phantom definition `D`, `D (Type u) … ↔ D (Type v) …`; both sides are provable by the phantom constructors, which is a synthetic proof per definition shape. |
| Q-b | General lowering in proof binders, R3-checked. | A superset of Q-a. | A weaker and harder argument: each lowered hypothesis must be shown equivalent. Not recommended. |
| — | Keep refusing. | The 79 roots stay blocked. | None. |

**Recommendation:** Q-a. It is narrow, re-derivable by the audit from the source (the body shape of the
phantom definition), and comes with a simple synthetic equivalence proof.

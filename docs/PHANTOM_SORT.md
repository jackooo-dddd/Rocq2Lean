# Rule Q-a: sort arguments of phantom checks, lowered per occurrence

Status: **Q-a adopted** (approved 2026-10-15, stage 5; ITERATION_LOG entry 15). **Q-b (general lowering in
proof binders) is not adopted.** Implementation: `Rocq2Lean/Translate.lean` (`phantomDefPairs?`,
`erasePhantomSorts`, the application site), `Rocq2Lean/Emit.lean` (tried first when it applies, then with
the ladder's variants); independent audit (`tools/audit.py`: `phantom_def_pairs`, `erase_phantom_sorts`,
the `phantom_sort` marker). Test: `scripts/test-phantom-sort`.

## 1. The frontier

The largest remaining group blocks the order/nmodule frontier, among them
`prosa.model.priority.gel.GEL`, `GEL_is_total` and `elf.ELF`: the HB builders, obligations and
`phant_*` constants of MathComp's `nmodule`, `order`, `preorder`, `algebraic_hierarchy`,
`numeric_hierarchy` and `ssrint`. At S9, **660 of the 714 direct failures** have HB's phantom check
`HB.structures.unify` in their type or value, and in each of them some level occurs only as a sort
argument of that check.

## 2. The mechanism (`Order.isPreorder.phant_Build`)

```
phant_Build (d) (T : Type@{4375}) (m) (Tlocal : Type@{4376}) …
  (s : Equality.type)
  (unif_arbitrary0 : HB.structures.unify Type@{4379} Type@{4380} Tlocal (Equality.sort s) msg) …
HB.structures.unify T1 T2 (t1 : T1) (t2 : T2) s := phantom T1 t1 -> phantom T2 t2      (Prop)
```

* Rocq type-checks `Tlocal : Type@{4379}` and `Equality.sort s : Type@{4380}` by cumulativity
  (`4376 ≤ 4379`, `51 ≤ 4380`); the source graph also makes `4379 = 4380`.
* Lean has no cumulativity. The only well-typed arguments are `Type u4376` and `Type u51'`, so plain typing
  solves `4379 := u4376` and `4380 := u51'`. The source fact `4379 = 4380` then fails (R2S), or a plain
  translation identifies the two carriers' levels, which narrows the binder ranges.

## 3. The rule

A **phantom definition** is a transparent monomorphic constant whose body, after its λs, is a chain of
non-dependent products of `phantom X x`. Here `phantom` is Corelib's `ssreflect_rw.phantom : ∀ T : Type,
T → Prop`, which has one constructor without fields; `X` is a λ-parameter whose type is a sort, and `x` is
a λ-parameter of type `X`. HB's `unify` is one. The criterion is recomputed from the source, independently,
by the translator and the audit.

The criterion also covers a **proof of a phantom check**: a monomorphic constant whose statement, after its
parameters, is such a chain (HB's `id_phant : ∀ T t, phantom T t → phantom T t`, which HB passes as the
proof of a `unify` hypothesis at the same common sort). An application of it is a proof of a phantom
proposition; its type is fixed by the (lowered) position it is used at, which the kernel checks, and
Lean's proof irrelevance makes any two proofs of it equal.

At every application of a phantom definition, a sort argument at a sort-parameter position becomes the
type of the paired value argument, per occurrence: `unify (Type u4376) (Type u51') Tlocal (sort s) msg`.
Levels that occurred **only** there are no longer the declaration's own levels: no parameter, no solution,
so no fact constrains them. The row reports them as `phantom_lowered`. When it applies, the rule is tried
first: its translation is strictly more general than a plain one, because every other level is translated
as before. The ladder's variants follow if it fails.

## 4. Why it is sound: equivalence

Every instance of a phantom check holds, because `fun _ => Phantom T2 t2` proves it. So any two instances,
at any sort arguments, are equivalent propositions: a hypothesis of a lowered check assumes exactly what
the source's assumes, and a statement with lowered checks is equivalent to the source statement. This is
what makes Q-a narrow. Q-b (general lowering in proof binders) has no such argument, because
`P (Type@{l})` and `P (Type@{a})` are different propositions in general, and it is not adopted.

`tests/statement/proofs/phantom_sort_equivalence.lean` (fixture `fixtures/stmt/phant`, axiom-free):
* `phantom_holds`, `unify_holds`: every instance holds.
* `unify_equiv`: any two instances are equivalent.
* `chk_hyp_equiv`: the lowered hypothesis is equivalent to the source's common-sort reading.
* `chk_hyp_dischargeable`, `chk_stmt_hyp_irrelevant`: the lowered hypothesis can always be discharged,
  and the statement does not depend on its proof.

## 5. What the audit verifies, independently

* The phantom definitions, recomputed from the source (`phantom_def_pairs`).
* The reported `phantom_lowered` levels are exactly the levels that disappear from the source when the
  phantom sort arguments are marked (`erase_phantom_sorts`). The row is then audited against the marked
  source.
* At a marked position, the target must be a sort. The kernel fixes which sort: the paired value's type.
* Protected rows with lowered checks are listed (`phantom_lowered_protected` in `audit.json`).

## 6. Negative controls (`scripts/test-phantom-sort`)

Each forgery is rejected:
* a lowered-level set that includes a carrier level (audit);
* a lowering reported where no phantom check is lowered (audit);
* a non-sort at a phantom sort position (kernel and audit);
* a sort that is not the value's type (kernel).

Unit controls cover the criterion: `unify` is a phantom definition; a non-phantom body, a declaration with
a phantom check in its type, and a phantom whose value is not of the sort parameter are not.

## 7. Measured effect

ITERATION_LOG entry 15 (subset on the GEL frontier; corpus run).

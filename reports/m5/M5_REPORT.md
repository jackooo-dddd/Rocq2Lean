# M5 — MathComp 2.6.0 / SSReflect foundation: report

**Status: M5 criteria met for an eqType + reflection fragment, sequences and finite sums.** This is
not complete MathComp support: the blockers are listed below.

**Toolchain.** Lean v4.33.1, Rocq 9.3.0, MetaRocq `c18395ad` (unpatched), MathComp 2.6.0. MathComp
is installed in a dedicated switch, `rocq930-mc`, built from the same pins
(architectural decision: `docs/ENVIRONMENT_M5.md`, investigation:
`reports/m5/environment_investigation.md`).

| Criterion | Result |
|---|---|
| MathComp 2.6.0 environment confirmed by compilation | `scripts/setup-switch-mc`; MathComp boot/order/ssreflect/algebra/finite-group 2.6.0 built by opam; lock and doctor validate it; M1–M4 rerun on it |
| Packed `eqType` preserved | `Equality.type` is translated as MathComp's HB structure: the primitive class record `Equality.axioms_` becomes a Lean structure; projections and the canonical `nat` instance are translated. No `DecidableEq` adapter; every instance is a translated MathComp term |
| A useful eqType + reflection fragment | `eqP`, `eq_refl`, `eq_sym`, `eqVneq`, `ssrnat.eqnP`, `eqnE`, `andP`, `orP`, `negP`, `idP`, `introT`, `elimT`, `iffP`: VERIFIED (closure 57) |
| Proofs with equality and sequences | `count_cat`, `filter_cat`, `size_cat`, `cat0s`, `cats0`, `catA`, `size_map`, `map_cat`, `count_filter`, `size_filter`, `has_count`, `all_count`, `count_predT`, `size_iota`, `index_iota`: VERIFIED (closure 93) |
| At least one finite-sum theorem | `big_nil`, `big_cons`, `mem_iota`, `mem_cat`: VERIFIED (closure 121), through the sealed `HB.lock` implementation of `bigop`. `big_cat`, `big_nat_recr`, `big_geq` and `big_ltn` also VERIFIED with the M6 rules (`runs/m5-big2v`) |
| Exact supported declarations | `reports/m5/supported_declarations.json`: 167 distinct accepted declarations, 98 from MathComp |
| No axioms or theorem-specific shortcuts | consumer: no axioms; every rule is generic and stated in `docs/` |
| Regressions | `test-all` 18/18 (M5 suite `test-m5`, 12 checks) |

## Classification of what was needed

| Mechanism | Kind |
|---|---|
| Primitive records (HB class records) → structure-like Lean inductives, primitive projections → `Expr.proj` | direct translation |
| `HB.lock` sealed modules (`bigop.body`/`unlock`) → the implementation as a transparent definition | lowering to an equivalent kernel expression; re-checked by Rocq's kernel in the prepared environment and in a fresh process |
| `ssr_have_upoly` (sort-polymorphic) → δβ-lowered at each use | lowering to an equivalent kernel expression; Rocq kernel re-check |
| Universe rules R2S, R2F, R3″ and R5S (M5), then R6, R2⁺, R3G, R2F-c and R8 (M6) | direct translation with independently audited universe obligations |
| Explicit kernel-checked adapters | none needed |
| Unsupported | below |

## Soundness fix found in M5

The fix lowering mapped branch references to the decreasing argument (and its index variables) to
the *outermost* call's argument. With that bug, `Nat.sub 3 3` computed `3`. The auditor had the
same misconception. Both were fixed: in a branch, these references now denote the constructor
application and its indices. The regression fixture is `fixtures/fixref` (`keep`, `subx`, `vlen`,
`Nat.sub`, by reflexivity). A type-correct mutation reproducing the old rule is kernel-accepted
and audit-rejected (`test-m5`). No previously accepted M1–M4 declaration changed
(`reports/m5/fix_lowering_changed_declarations.json`).

## Unsupported (with paths)

| Root | Blocked at | Cause |
|---|---|---|
| `fintype.card_bool`, `card_ord`, `big_ord_recr` | `eqtype` sub-type and fintype class records (`SubEquality … __to__eqtype_SubType_class`, `isFinite.axioms_`), `eqtype.Sub_spec` | universe instances of HB class records that Lean's unifier cannot solve (a `max` of two levels against one), and an R3 relation between levels 695 and 577 that the native graph does not entail |
| `bigop.big_const_seq`, `sum_nat_const` | `big_const_seq` | a proof-local level solved as a type level that violates the native fact `2716 ≤ 1120` |
| `seq.nth`, and with it `count_uniq_mem` users | `seq.nth` | fixpoint whose decreasing match is not outermost |

Next technical change: a universe-constraint solver for postponed `max` constraints under the
native facts (see the M6 report), then `brecOn`-style lowering for non-outermost decreasing
matches.

## Fresh holdouts

15 standard MathComp lemmas were chosen after the freeze tag `m6-freeze-1` and committed before
running (`reports/m6/holdout_selection.json`). `eqtype.eqxx` was excluded because in MathComp 2.6
it is a notation, not a declaration. The other 14 ran once on the frozen implementation, and
**14/14 are VERIFIED** (`reports/m6/holdout_results.json`):
- `ssrnat`: `addnC`, `addnA`, `addn0`, `add0n`, `leqnn`, `leq_addr`, `subnn`;
- `seq`: `size_rev`, `rev_cat`, `count_rev`, `take_drop`, `cat_take_drop`;
- `bigop`: `big_seq1`, `big_nat1`.

## Reproduce

```sh
./scripts/test-m5     # eqType/reflection, sequences, finite sums, fix soundness, prepared environment
./scripts/test-all    # 18 suites
```

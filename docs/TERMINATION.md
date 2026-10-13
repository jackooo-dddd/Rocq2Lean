# Termination lowering with explicit obligations (Task B)

Decision (2026-10-13, Q3(b)): recursion that the existing structural lowerings cannot express is
translated with an **explicit termination obligation** and an **unfolding-equation statement**, both
proof tasks for the Lean proving agent. Rocq2Lean never constructs a termination proof for a corpus
definition. The mathematical computation is preserved; every place where a dependent type or a
retained definition needs the definitional unfolding of such a recursion is identified (here, from
the source, by Rocq) and reported as a blocker. Definitional reduction, propositional equations and
compiled evaluation are measured separately.

## 1. What needs it

MathComp's `edivn_rec` and `modn_rec` (and everything that computes `%/` and `%%`):

    Definition edivn_rec d := fix loop m q {struct m} :=
      if m - d is m'.+1 then loop m' q.+1 else (q, m).

Rocq's guard condition accepts the call `loop m'` because it *reduces* `m - d` (`subn`, itself
structural) and sees that every result is `m` or a subterm of it, so `m'` is a strict subterm of `m`.
Lean's structural recursion has no such reduction: the call is not on a constructor field of `m`. The
structural lowering (M3c) and the course-of-values lowering (M6) both refuse it ("recursive call on a
term that is not a direct recursive constructor field"). Before B: `UNSUPPORTED_FEATURE`; 732
protected declarations blocked by these two definitions, 411 by them alone.

## 2. The lowering (`Rocq2Lean/Translate.lean`, `transFixWf`)

Statement mode only (proof-mode translations are unchanged), tried after M3c and M6 refused the
fixpoint. For `fix f P x Q {struct x} := B` with `x : I params` data, `I` without indices:

    λ P x Q, Acc.rec (C := I params) R (λ s _, ∀ G Q, T[s]) (λ s h ih, λ G Q, B′) x (wf Γ x) G Q

* **Call relation** `R y s := D₁ y s ∨ … ∨ Dₙ y s`, one disjunct per recursive call of the source
  body, `Dᵢ y s := ∃ ctxᵢ, y = aᵢ` with `aᵢ` the call's decreasing argument and `ctxᵢ` the call's
  local context (the M6 accessibility lowering's construction).
* **Convoy.** Every `match` of the body whose branches contain a recursive call carries its
  scrutinee's equation into its branches: `I.rec (λ z, e = z → RET) minors e (Eq.refl e)`, each minor
  binding `h : e = Cₖ fields`. `h` enters the call contexts, so `R` records *why* the argument
  decreases (`∃ q m' (h : subn s d = m'.+1), y = m'`). The branches compute exactly the source
  branches; `h` is only bound. (Lean-only recursor binders of the lowered matches are left out of the
  call contexts.)
* **Recursive calls** become `ih a cert` with `cert : R a s` built from the call's own context
  (`∃`-introductions with the context and `Eq.refl`): no termination reasoning, only packaging.
* **Well-foundedness** `wf : ∀ Γ, ∀ s, Acc R s` (Γ the locals `R` mentions) is **not constructed**:
  it is the **termination obligation**, a translator-generated leaf `<c>__rocq2lean_termination_<k>`
  whose statement `def Rocq.<c>__rocq2lean_termination_<k>.statement : Prop := ∀ Γ, ∀ s, Acc R s` is
  kernel-checked and becomes a hypothesis of the pending artifact `RocqPending.<c>` (and of everything
  that needs `c`), exactly like an extracted proof obligation. In assembly it is the obligation's
  final theorem.

The computed function is the source's: each step evaluates the source body; only the justification
of the recursion is abstracted. In Lean, `Acc.rec` reduces only when its major premise reduces to
`Acc.intro`, so with a hypothesis the definition does not unfold definitionally; after assembly it
unfolds as far as the supplied proof reduces (measured below).

## 3. The unfolding equation

For a constant whose body is `λ outer, fix f args := B` (the corpus cases), a second generated
statement, `<c>__rocq2lean_unfold_1`:

    ∀ outer args, c outer args = ⟦B⟧[f := c outer]

with `c` the translated constant (the pending artifact applied to its hypotheses while pending), and
`⟦B⟧` the source body translated as an ordinary term (plain matches, no convoy). It is Rocq's
definitional unfolding of the fixpoint, stated propositionally; its proof is a task (generalized over
the termination obligation, a proposition: Lean's definitional proof irrelevance makes it provable
for any proof of the obligation). Not generated for a fixpoint nested deeper in a body, or for a
definition with universe parameters (reported in the row's message instead).

## 4. Validation

* **Kernel**: every generated statement and the pending artifacts are kernel-checked. The pending
  artifact applies the obligation to `Γ` and the decreasing argument, so the kernel identifies the
  statement's `C` and `R` with the lowering's.
* **Consumer** (`Rocq2Lean/Verify.lean`): a generated row must be attached to an exported declaration
  by its name (`<decl>__rocq2lean_termination_<k>` / `<decl>__rocq2lean_unfold_<k>`) and kind.
* **Audit** (`tools/audit.py`, independent): `check_fix_acc(wf=True)` re-derives the lowering from the
  source fixpoint (carrier, call-relation shape: one `∃ ctx, y = a` disjunct per source call, motive,
  minor premise term by term with the convoy matches); the well-foundedness argument must be one of
  the declaration's *own* termination obligations (hypothesis or final theorem) applied to locals and
  the decreasing argument, and the obligations the lowering uses must be exactly the generated ones;
  prerequisites are recomputed with the generated leaves (a lowered constant needs its obligations, its
  equation needs what it needs). `check_termination_statement` checks the statement's shape and use;
  `check_unfolding_equation` restates the equation from the source (binder types, left side, right
  side = the source body with `f := c outer`, compared term by term).
* **Negative controls** (`scripts/test-termination`): a changed accumulator in the lowering's
  recursive call, and in the equation's right side: both kernel-accepted, both rejected by the audit.

## 5. Conversion dependence (`inventory/conversion_deps.py`, `Rocq2Lean CheckConversionDeps`)

Every constant whose dependency closure reaches a lowered definition is re-checked **in Rocq**: its
statement preparation (proof subterms extracted, kernel re-check) runs once in the prepared
environment and once with the lowered definitions' bodies removed. Refused only in the second =
**needs the unfolding** (`CONV_NEEDS`): its Lean translation cannot be kernel-checked against the
pending artifact, and it is reported as such (in the fixture: `t3 : T3 := 0` with
`T3 := match divr 7 2 with 3 => nat | _ => bool end`). The result is joined with the translation
outcome: a dependent that needs the unfolding must not be claimed, and every Lean kernel failure
among the dependents should be explained by such a need (`reports/statement_only/termination/
CONVERSION_DEPENDENCE.json`). No representation or transport strategy for these is implemented:
they are explicit blockers.

## 6. Computation, measured separately (fixture `fixtures/stmt/wf`, after assembly with test proofs)

| | result |
|---|---|
| definitional reduction, kernel (`decide +kernel`: `divr 7 2 = 3`) | **holds** — the kernel reduces `Acc.rec` through the supplied closed termination proof |
| definitional reduction, elaborator (`rfl`) | fails — the elaborator's defeq check does not unfold theorem proofs |
| conversion-dependent definition `t3 : T3 := 0` added through the kernel after assembly | **accepted** — but it depends on the supplied proof reducing (proof-dependent computation); assembly does not re-attempt it |
| propositional unfolding equation (`divr 7 2 = 3` from the assembled equation, by rewriting) | **holds** |
| compiled evaluation (`#eval divr 7 2`) | unsupported: no code is generated for kernel-added declarations (`Failed to find LCNF signature`), for every translated definition, not only lowered ones — reported, not a kernel failure |

So the blanket claim that well-founded recursion cannot compute is wrong for this encoding: with a
closed, axiom-free termination proof the kernel computes; with a hypothesis (pending) it cannot; with
a proof that uses axioms (`propext`) or opaque lemmas it may get stuck. A dependent that needs the
unfolding therefore remains a blocker until a strategy that does not depend on the shape of a
submitted proof is chosen.

## 7. Scope and limits

* Decreasing argument of an inductive without indices; matches enclosing recursive calls on
  inductives without indices; the call relation must not mention pending prerequisites; the
  termination statement must not involve universe-polymorphic levels. Each limit is a reported
  refusal (`UNSUPPORTED_FEATURE: termination lowering: …`).
* Exporter-marked deferred termination (`"termination": "deferred"`: a recursion on a proof subterm
  that became an obligation) is still refused (no corpus record has it).
* The relation `R` is the call relation, not a fixed order: provability of the obligation is the
  agent's task; an `R` that were too large would make it unprovable (never unsound), one too small is
  kernel-rejected (the certificates could not be built).

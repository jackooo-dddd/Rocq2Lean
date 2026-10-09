import Lean
import Rocq2Lean.IR

/-!
# Expression translation

`trans` maps a source IR term to a Lean `Expr`. Binders are opened with fresh free variables
(`withLocalDecl`/`withLetDecl`) so that Lean type inference is available where the source
leaves information implicit (the universe of a template-polymorphic inductive, cast
validation). Terms are closed again with `mkForallFVars`/`mkLambdaFVars`/`mkLetFVars`;
`usedLetOnly := false` keeps every source `let`.

Every failure is a structured `TransError` carrying a status and the node path.
-/

namespace Rocq2Lean

open Lean Meta
open IR (SortIR LevelExpr AName IndRef Relevance)

structure TransError where
  status : String
  msg : String
  path : List String
  deriving Inhabited, Repr

/-- How the universe arguments of a target inductive are determined. -/
inductive UnivRule where
  /-- The target has no universe parameters; the source instance must be empty. -/
  | mono
  /-- One universe parameter: the sort level of the type of argument `arg`
  (source template polymorphism, where Rocq computes the level from the arguments). -/
  | templateFromArg (arg : Nat)
  deriving Repr, Inhabited, BEq

/-- How a source inductive block is realised in Lean. -/
structure IndTarget where
  types : Array Name
  ctors : Array (Array Name)
  univ : UnivRule
  /-- Rule identifier: a bootstrap rule id, or `generated`. -/
  rule : String
  deriving Inhabited, Repr

structure GEnv where
  consts : Std.HashMap String Name := {}
  /-- Number of universe parameters of each accepted constant (generalized global levels). -/
  constLevels : Std.HashMap String Nat := {}
  /-- Source global level of each universe parameter of each accepted constant, by target name. -/
  constGlobals : Std.HashMap Name (Array String) := {}
  /-- Native universe facts of the export. -/
  facts : IR.UniverseFacts := { levels := #[], relations := #[] }
  inds : Std.HashMap String IndTarget := {}
  /-- Global universe names read directly as the level of a Lean `Sort` (adapter checks only). -/
  sortOverride : Std.HashMap String Level := {}
  deriving Inhabited

structure TCtx where
  genv : GEnv
  /-- Global monomorphic levels of the declaration being translated, as Lean universe
  parameters (`Type@{l+n} ↦ Sort (u_l + n + 1)`). -/
  globalLevels : Std.HashMap String Level := {}
  /-- `locals[k]` is the Lean value of the `k`-th enclosing source binder, outermost first;
  source `rel i` denotes `locals[locals.size - 1 - i]`. -/
  locals : Array Expr := #[]
  path : List String := []

abbrev TransM := ReaderT TCtx (ExceptT TransError MetaM)

def failT {α} (status msg : String) : TransM α := do
  throwThe TransError { status, msg, path := (← read).path }

def withPath {α} (seg : String) (x : TransM α) : TransM α :=
  withReader (fun c => { c with path := seg :: c.path }) x

def withLocal {α} (x : Expr) (k : TransM α) : TransM α :=
  withReader (fun c => { c with locals := c.locals.push x }) k

def liftMeta {α} (x : MetaM α) : TransM α := fun _ => ExceptT.lift x

/-! ## Names -/

/-- Lean name for a source key: `Rocq.` followed by its file components, module fields and
identifier (see `docs/IR_SPEC.md`, "Keys"). -/
def targetName (key : String) : Name :=
  let comps := (key.splitOn "/").flatMap (·.splitOn ".")
  comps.foldl Name.str `Rocq

/-- Module part of a key (everything before the final `.ident`). -/
def keyModule (key : String) : String :=
  match key.splitOn "." with
  | [] => key
  | comps => String.intercalate "." comps.dropLast

/-- Lean names for a generated inductive body and its constructors:
`Rocq.<module>.<type>` and `Rocq.<module>.<type>.<ctor>`. -/
def inductiveNames (mindKey : String) (body : String) (ctors : Array String) : Name × Array Name :=
  let t := targetName (keyModule mindKey ++ "." ++ body)
  (t, ctors.map (Name.str t))

def binderName (n : AName) : Name :=
  match n.name with
  | some s => Name.mkSimple s
  | none => .anonymous

/-! ## Universes -/

/-- Lean sort level of a source `Type@{u}` in the pilot fragment: `Set + n ↦ n + 1`, `max`
componentwise. Global monomorphic levels and polymorphic variables are rejected. -/
def transTypeLevel (u : Array LevelExpr) : TransM Level := do
  if u.isEmpty then failT "EXPORT_VALIDATION_FAILED" "empty algebraic universe"
  let parts ← u.mapM fun e => do
    match e.level with
    | .set => pure (Level.ofNat (e.offset + 1))
    | .global n =>
      match (← read).genv.sortOverride[n]? with
      | some l =>
        if e.offset == 0 then pure l
        else failT "UNSUPPORTED_FEATURE" s!"successor of adapter-bound level {n}"
      | none =>
        match (← read).globalLevels[n]? with
        | some l => pure (l.addOffset (e.offset + 1))
        | none => failT "UNSUPPORTED_FEATURE" s!"global universe {n} not generalized for this declaration"
    | .var i => failT "UNSUPPORTED_FEATURE" s!"universe-polymorphic level variable {i}"
  let mut acc := parts[0]!
  for l in parts[1:] do acc := mkLevelMax' acc l
  return acc.normalize

def transSort : SortIR → TransM Expr
  | .prop => pure (.sort .zero)
  | .sprop => failT "UNSUPPORTED_FEATURE" "SProp"
  | .type u => return .sort (← transTypeLevel u)

def checkRelevant (n : AName) : TransM Unit := do
  if n.rel == .irrelevant then failT "UNSUPPORTED_FEATURE" "SProp-irrelevant binder"

/-! ## Global references -/

def lookupInd (i : IndRef) : TransM IndTarget := do
  match (← read).genv.inds[i.mind]? with
  | some t =>
    unless i.idx < t.types.size do
      failT "EXPORT_VALIDATION_FAILED" s!"inductive body index {i.idx} out of range for {i.mind}"
    return t
  | none => failT "TRANSLATION_FAILED" s!"reference to inductive {i.mind}, which has no accepted translation"

def univArgs (mind : String) (t : IndTarget) (u : Array IR.Level) (args : Array Expr) :
    TransM (List Level) := do
  unless u.isEmpty do
    failT "UNSUPPORTED_FEATURE" s!"non-empty universe instance on {mind} (pilot supports monomorphic references only)"
  match t.univ with
  | .mono => pure []
  | .templateFromArg k =>
    if h : k < args.size then
      let l ← liftMeta (do instantiateLevelMVars (← getLevel args[k]))
      if l.hasMVar then failT "TRANSLATION_FAILED" s!"could not determine the universe of {mind}"
      pure [l.normalize]
    else
      failT "UNSUPPORTED_FEATURE" s!"{mind} used with fewer than {k + 1} arguments: its universe is undetermined"

/-! ## Terms -/

/-- Leading lambdas of a source term. -/
def peelLams : IR.Term → Array (AName × IR.Term) × IR.Term
  | .lam n t b => let (ls, r) := peelLams b; (#[(n, t)] ++ ls, r)
  | t => (#[], t)

def recursorOf (iname : Name) : TransM RecursorVal := do
  match (← getEnv).find? (iname.str "rec") with
  | some (.recInfo rv) =>
    unless rv.numMotives == 1 do failT "UNSUPPORTED_FEATURE" s!"elimination of a mutual or nested inductive ({iname})"
    return rv
  | _ => failT "TRANSLATION_FAILED" s!"no recursor {iname}.rec in the target environment"

/-- Binders of a minor premise: exactly `nfields` constructor fields, then exactly one recursive
result per recursive field (a field whose type is an application of `iname`). Functional
recursive fields (`… → I …`) are rejected. Continues with fields, recursive fields, results
and the remaining (motive-application) type. -/
def minorTelescope {α} (minorTy : Expr) (nfields : Nat) (iname : Name)
    (k : Array Expr → Array Expr → Array Expr → Expr → TransM α) : TransM α :=
  forallBoundedTelescope minorTy (some nfields) fun fields rest => do
    unless fields.size == nfields do failT "TRANSLATION_FAILED" "minor premise has too few field binders"
    let mut recFields := #[]
    for y in fields do
      let yt ← liftMeta do inferType y
      let functional ← liftMeta do forallTelescopeReducing yt fun zs body => do
        return !zs.isEmpty && (← whnf body).getAppFn.isConstOf iname
      if functional then failT "UNSUPPORTED_FEATURE" "functional recursive constructor field"
      if (← liftMeta do whnf yt).getAppFn.isConstOf iname then recFields := recFields.push y
    forallBoundedTelescope rest (some recFields.size) fun ihs res => do
      unless ihs.size == recFields.size do failT "TRANSLATION_FAILED" "minor premise has too few recursive results"
      k fields recFields ihs res

mutual

partial def trans (t : IR.Term) : TransM Expr := do
  match t with
  | .rel i =>
    let ls := (← read).locals
    if i < ls.size then pure ls[ls.size - 1 - i]!
    else failT "EXPORT_VALIDATION_FAILED" s!"de Bruijn index {i} out of scope (depth {ls.size})"
  | .var id => failT "UNSUPPORTED_FEATURE" s!"unresolved section variable {id}"
  | .evar .. => failT "UNSUPPORTED_FEATURE" "existential variable"
  | .sort s => transSort s
  | .cast c kind ty => withPath "cast" do
    let c' ← withPath "t" (trans c)
    let ty' ← withPath "ty" (trans ty)
    let ok ← liftMeta do isDefEq (← inferType c') ty'
    unless ok do failT "TRANSLATION_FAILED" s!"{kind} cast annotation is not convertible in Lean"
    pure c'
  | .prod n ty b => withPath "prod" do
    checkRelevant n
    let ty' ← withPath "ty" (trans ty)
    withLocalDecl (binderName n) .default ty' fun x => do
      let b' ← withPath "b" (withLocal x (trans b))
      mkForallFVars #[x] b'
  | .lam n ty b => withPath "lam" do
    checkRelevant n
    let ty' ← withPath "ty" (trans ty)
    withLocalDecl (binderName n) .default ty' fun x => do
      let b' ← withPath "b" (withLocal x (trans b))
      mkLambdaFVars #[x] b'
  | .letIn n v ty b => withPath "let" do
    checkRelevant n
    let ty' ← withPath "ty" (trans ty)
    let v' ← withPath "v" (trans v)
    withLetDecl (binderName n) ty' v' fun x => do
      let b' ← withPath "b" (withLocal x (trans b))
      mkLetFVars #[x] b' (usedLetOnly := false)
  | .app f args => withPath "app" do
    let args' ← args.mapIdxM fun k a => withPath s!"arg{k}" (trans a)
    let f' ← withPath "f" (transHead f args')
    pure (mkAppN f' args')
  | .const .. | .ind .. | .construct .. => transHead t #[]
  | .case ind npar _ puinst pparams pctx pret scrut brs =>
    withPath "case" (transCase ind npar puinst pparams pctx pret scrut brs)
  | .proj .. => failT "UNSUPPORTED_FEATURE" "primitive projection"
  | .fix defs idx => withPath "fix" (transFix defs idx)
  | .cofix .. => failT "UNSUPPORTED_FEATURE" "cofixpoint"
  | .prim k _ => failT "UNSUPPORTED_FEATURE" s!"primitive {k}"

/-- M3b: lower a source `match` to the kernel-generated recursor `I.rec`.

* parameters: the translated source parameters;
* motive: built in the recursor's own motive telescope (indices, then the major premise) from
  the source return clause, so it stays dependent; its universe is computed by Lean;
* minors: one per constructor, binding exactly the constructor fields (count from the
  kernel's recursor rules) and the recursive-result binders, which a plain `match` ignores;
* indices: read from the inferred type of the translated scrutinee (Rocq's `Case` does not
  store them).
-/
partial def transCase (ind : IndRef) (npar : Nat) (puinst : Array IR.Level) (pparams : Array IR.Term)
    (pctx : Array AName) (pret : IR.Term) (scrut : IR.Term) (brs : Array (Array AName × IR.Term)) :
    TransM Expr := do
  let tgt ← lookupInd ind
  let iname := tgt.types[ind.idx]!
  let rv ← recursorOf iname
  unless rv.numParams == npar && pparams.size == npar do
    failT "EXPORT_VALIDATION_FAILED" s!"case has {pparams.size} parameters, {iname}.rec expects {rv.numParams}"
  unless pctx.size == rv.numIndices + 1 do
    failT "EXPORT_VALIDATION_FAILED" s!"case return context has {pctx.size} binders, expected {rv.numIndices + 1}"
  unless brs.size == rv.numMinors do
    failT "EXPORT_VALIDATION_FAILED" s!"case has {brs.size} branches, {iname}.rec has {rv.numMinors} minors"
  let params ← pparams.mapIdxM fun k a => withPath s!"param{k}" (trans a)
  let indLvls ← univArgs ind.mind tgt puinst params
  let scrut' ← withPath "scrutinee" (trans scrut)
  let sty ← liftMeta do whnf (← inferType scrut')
  let sargs := sty.getAppArgs
  unless sty.getAppFn.isConstOf iname && sargs.size == npar + rv.numIndices do
    failT "TRANSLATION_FAILED" s!"scrutinee type is not an application of {iname}"
  let idx := sargs.extract npar sargs.size
  let large := rv.levelParams.length == indLvls.length + 1
  let recLvls (u : Level) := if large then u :: indLvls else indLvls
  let ty0 ← liftMeta do
    instantiateForall (← inferType (mkConst (iname.str "rec") (recLvls Level.zero))) params
  let .forallE _ motiveTy _ _ := ty0 | failT "TRANSLATION_FAILED" s!"unexpected type of {iname}.rec"
  let (motive, u) ← forallTelescopeReducing motiveTy fun xs _ => do
    unless xs.size == pctx.size do failT "TRANSLATION_FAILED" "motive arity differs from the case context"
    let ret ← withPath "return" (withReader (fun c => { c with locals := c.locals ++ xs }) (trans pret))
    let u ← liftMeta do instantiateLevelMVars (← getLevel ret)
    return (← mkLambdaFVars xs ret, u.normalize)
  if !large && u != Level.zero then
    failT "UNSUPPORTED_FEATURE" s!"elimination of {iname} into a non-Prop sort is not available in Lean"
  let recConst := mkConst (iname.str "rec") (recLvls u)
  let mut ty ← liftMeta do instantiateForall (← inferType recConst) (params.push motive)
  let mut minors : Array Expr := #[]
  for k in [0:rv.numMinors] do
    let .forallE _ minorTy rest _ ← liftMeta (whnf ty) | failT "TRANSLATION_FAILED" s!"{iname}.rec: missing minor {k}"
    let (bctx, bbody) := brs[k]!
    let nfields := rv.rules[k]!.nfields
    unless bctx.size == nfields do
      failT "UNSUPPORTED_FEATURE" s!"branch {k}: {bctx.size} binders for {nfields} fields (let-bound constructor arguments)"
    let minor ← minorTelescope minorTy nfields iname fun fields _ ihs _ => do
      let body ← withPath s!"branch{k}" (withReader (fun c => { c with locals := c.locals ++ fields }) (trans bbody))
      mkLambdaFVars (fields ++ ihs) body
    minors := minors.push minor
    ty := rest.instantiate1 minor
  return mkAppN recConst (params ++ #[motive] ++ minors ++ idx ++ #[scrut'])

/-- Replace each recursive call `f P… y rest` by `ih_y rest'`, where `y` is a direct recursive
constructor field. Parameters before the decreasing argument must be the function's own
parameters, except index variables of the decreasing argument, which must be the
corresponding index of `y`'s type. Any other occurrence of `f` is rejected. -/
partial def replaceRecCalls (f : FVarId) (P : Array Expr) (idxPos : Array (Option Nat))
    (fieldIH : Array (Expr × Expr × Array Expr)) (e : Expr) : TransM Expr := do
  let go := replaceRecCalls f P idxPos fieldIH
  match e with
  | .app .. =>
    let fn := e.getAppFn
    let args := e.getAppArgs
    if fn.isFVarOf f then
      let r := P.size
      unless args.size ≥ r + 1 do failT "UNSUPPORTED_FEATURE" "recursive call without its decreasing argument"
      let y := args[r]!
      let some (_, ih, yIdx) := fieldIH.find? (·.1 == y)
        | failT "UNSUPPORTED_FEATURE" "recursive call on a term that is not a direct recursive constructor field"
      for i in [0:r] do
        match idxPos[i]! with
        | none =>
          unless args[i]! == P[i]! do
            failT "UNSUPPORTED_FEATURE" s!"recursive call changes parameter {i}, which precedes the decreasing argument"
        | some j =>
          unless args[i]! == yIdx[j]! do
            failT "UNSUPPORTED_FEATURE" s!"recursive call passes index argument {i} different from the field's index"
      return mkAppN ih (← (args.extract (r + 1) args.size).mapM go)
    return mkAppN (← go fn) (← args.mapM go)
  | .lam n t b bi => return .lam n (← go t) (← go b) bi
  | .forallE n t b bi => return .forallE n (← go t) (← go b) bi
  | .letE n t v b nd => return .letE n (← go t) (← go v) (← go b) nd
  | .mdata d b => return .mdata d (← go b)
  | .proj sn i b => return .proj sn i (← go b)
  | .fvar id => if id == f then failT "UNSUPPORTED_FEATURE" "recursive function used other than in a call" else pure e
  | _ => pure e

/-- Open the leading source lambdas of a fixpoint body with their translated source types. -/
partial def withSourceLams (lams : Array (AName × IR.Term)) (base : Array Expr) (i : Nat) (acc : Array Expr)
    (k : Array Expr → TransM Expr) : TransM Expr := do
  if h : i < lams.size then
    let (n, t) := lams[i]
    let t' ← withPath s!"lam{i}" (withReader (fun c => { c with locals := base ++ acc }) (trans t))
    withLocalDecl (binderName n) .default t' fun a => withSourceLams lams base (i + 1) (acc.push a) k
  else k acc

/-- M3c: lower a single structurally recursive `fix` to the decreasing argument's recursor.

Source shape: `fix f a₀ … a_{n-1} {struct a_r} := match a_r with … end`. Target:
`λ P x Q, I.rec params (λ idx x, ∀ Q, T) minors idx x Q` with `P = a₀…a_{r-1}`, `x = a_r`,
`Q = a_{r+1}…`. The motive is function-valued over `Q`, so arguments after the decreasing one
may change in recursive calls; index variables of `x` are generalized. Each minor binds the
fields, the recursive results and its own `Q`; recursive calls on fields become the
corresponding recursive results (`replaceRecCalls`). The source `match`'s return clause is
not used: the motive is determined by the fixpoint's declared type. -/
partial def transFix (defs : Array (AName × IR.Term × IR.Term × Nat)) (fidx : Nat) : TransM Expr := do
  unless defs.size == 1 && fidx == 0 do failT "UNSUPPORTED_FEATURE" s!"mutual fixpoint ({defs.size} functions)"
  let (fname, fty, fbody, rarg) := defs[0]!
  let fty' ← withPath "type" (trans fty)
  let (lams, b) := peelLams fbody
  unless rarg < lams.size do
    failT "UNSUPPORTED_FEATURE" s!"decreasing argument {rarg} is not bound by the leading lambdas ({lams.size})"
  let .case cind cnpar _ _ _ _ _ (.rel sj) brs := b
    | failT "UNSUPPORTED_FEATURE" "fixpoint body is not a match on the decreasing argument"
  unless sj == lams.size - 1 - rarg do failT "UNSUPPORTED_FEATURE" "match scrutinee is not the decreasing argument"
  let outer := (← read).locals
  withLocalDecl (binderName fname) .default fty' fun fv => do
  withSourceLams lams (outer.push fv) 0 #[] fun as => do
    let P := as.extract 0 rarg
    let x := as[rarg]!
    let Q := as.extract (rarg + 1) as.size
    let T ← liftMeta (instantiateForall fty' as)
    let tgt ← lookupInd cind
    let iname := tgt.types[cind.idx]!
    let xty ← liftMeta do whnf (← inferType x)
    unless xty.getAppFn.isConstOf iname do
      failT "TRANSLATION_FAILED" "type of the decreasing argument is not the matched inductive"
    let rv ← recursorOf iname
    unless rv.numParams == cnpar && brs.size == rv.numMinors do
      failT "EXPORT_VALIDATION_FAILED" "match metadata disagrees with the recursor"
    let xargs := xty.getAppArgs
    let params := xargs.extract 0 rv.numParams
    let idx := xargs.extract rv.numParams xargs.size
    unless idx.all (P.contains ·) && idx.toList.eraseDups.length == idx.size do
      failT "UNSUPPORTED_FEATURE" "indices of the decreasing argument are not distinct earlier parameters"
    let idxPos : Array (Option Nat) := P.map fun p => idx.findIdx? (· == p)
    let indLvls := xty.getAppFn.constLevels!
    let QT ← mkForallFVars Q T
    let u := (← liftMeta do instantiateLevelMVars (← getLevel QT)).normalize
    let motive ← mkLambdaFVars (idx.push x) QT
    let large := rv.levelParams.length == indLvls.length + 1
    if !large && u != Level.zero then
      failT "UNSUPPORTED_FEATURE" s!"recursion on {iname} into a non-Prop sort is not available in Lean"
    let recConst := mkConst (iname.str "rec") (if large then u :: indLvls else indLvls)
    let mut ty ← liftMeta do instantiateForall (← inferType recConst) (params.push motive)
    let mut minors : Array Expr := #[]
    for k in [0:rv.numMinors] do
      let .forallE _ minorTy rest _ ← liftMeta (whnf ty) | failT "TRANSLATION_FAILED" s!"{iname}.rec: missing minor {k}"
      let (bctx, bbody) := brs[k]!
      let nfields := rv.rules[k]!.nfields
      unless bctx.size == nfields do
        failT "UNSUPPORTED_FEATURE" s!"branch {k}: let-bound constructor arguments"
      let minor ← minorTelescope minorTy nfields iname fun fields recFields ihs res => do
        let fieldIH ← (recFields.zip ihs).mapM fun (y, ih) => do
          let yt ← liftMeta do whnf (← inferType y)
          return (y, ih, yt.getAppArgs.extract rv.numParams yt.getAppArgs.size)
        let res ← liftMeta (whnf res)
        forallBoundedTelescope res (some Q.size) fun qs _ => do
          unless qs.size == Q.size do failT "TRANSLATION_FAILED" "minor result has fewer binders than the motive"
          let locals := outer ++ #[fv] ++ P ++ #[x] ++ qs ++ fields
          let body ← withPath s!"branch{k}" (withReader (fun c => { c with locals := locals }) (trans bbody))
          let body ← replaceRecCalls fv.fvarId! P idxPos fieldIH body
          mkLambdaFVars (fields ++ ihs ++ qs) body
      minors := minors.push minor
      ty := rest.instantiate1 minor
    let res ← mkLambdaFVars as (mkAppN (mkAppN recConst (params ++ #[motive] ++ minors ++ idx ++ #[x])) Q)
    if res.containsFVar fv.fvarId! then
      failT "UNSUPPORTED_FEATURE" "recursive function escapes the supported call pattern"
    return res

/-- Translate an application head. `args` are the already-translated arguments, needed when
the target's universe is computed from them. -/
partial def transHead (f : IR.Term) (args : Array Expr) : TransM Expr := do
  match f with
  | .const c u =>
    unless u.isEmpty do failT "UNSUPPORTED_FEATURE" s!"non-empty universe instance on constant {c}"
    match (← read).genv.consts[c]? with
    | some n =>
      -- Universe parameters of a generalized constant are instantiated by fresh level
      -- metavariables, solved by Lean's unifier after translation (`solveLevels`).
      let k := (← read).genv.constLevels[c]?.getD 0
      let lvls ← liftMeta do (List.range k).mapM fun _ => mkFreshLevelMVar
      pure (mkConst n lvls)
    | none => failT "TRANSLATION_FAILED" s!"reference to constant {c}, which has no accepted translation"
  | .ind i u =>
    let t ← lookupInd i
    return mkConst t.types[i.idx]! (← univArgs i.mind t u args)
  | .construct i c u =>
    let t ← lookupInd i
    let cs := t.ctors[i.idx]!
    unless c < cs.size do
      failT "EXPORT_VALIDATION_FAILED" s!"constructor index {c} out of range for {i.mind}"
    return mkConst cs[c]! (← univArgs i.mind t u args)
  | _ => trans f

end

/-- Translate a closed term and check that no free or meta variable escapes. -/
def transClosed (t : IR.Term) : TransM Expr := do
  let e ← instantiateMVars (← trans t)
  if e.hasFVar then failT "TRANSLATION_FAILED" "translated term has escaping free variables"
  if e.hasExprMVar then failT "TRANSLATION_FAILED" "translated term has unresolved metavariables"
  return e

def runTrans {α} (genv : GEnv) (x : TransM α) (globalLevels : Std.HashMap String Level := {}) :
    MetaM (Except TransError α) :=
  (x { genv, globalLevels }).run

/-! ## Universe generalization -/

/-- Global level names occurring in a source term (in sorts). -/
partial def globalsOf (t : IR.Term) (acc : Std.HashSet String := {}) : Std.HashSet String :=
  let sortG (s : SortIR) (acc : Std.HashSet String) : Std.HashSet String :=
    match s with
    | .type u => u.foldl (fun a e => match e.level with | .global n => a.insert n | _ => a) acc
    | _ => acc
  let go := fun (t : IR.Term) (a : Std.HashSet String) => globalsOf t a
  match t with
  | .sort s => sortG s acc
  | .cast c _ ty => go ty (go c acc)
  | .prod _ a b | .lam _ a b => go b (go a acc)
  | .letIn _ v ty b => go b (go ty (go v acc))
  | .app f args => args.foldl (fun a x => go x a) (go f acc)
  | .evar _ args => args.foldl (fun a x => go x a) acc
  | .case _ _ _ _ ps _ r c brs =>
    brs.foldl (fun a b => go b.2 a) (go c (go r (ps.foldl (fun a x => go x a) acc)))
  | .proj _ _ _ c => go c acc
  | .fix ds _ | .cofix ds _ => ds.foldl (fun a (_, ty, b, _) => go b (go ty a)) acc
  | _ => acc

/-- Lean universe parameter for a source global level: `u_` followed by the level name with
`.` replaced by `_` (e.g. `Corelib.Init.Logic.8 ↦ u_Corelib_Init_Logic_8`). -/
def levelParamName (n : String) : Name := Name.mkSimple ("u_" ++ n.replace "." "_")

/-- Level metavariables of an expression. -/
partial def levelMVarsOf (e : Expr) : StateM (Array LMVarId) Unit := do
  let lv (l : Level) : StateM (Array LMVarId) Unit := do
    for m in (l.collectMVars {}).toArray do
      unless (← get).contains m do modify (·.push m)
  match e with
  | .sort l => lv l
  | .const _ ls => ls.forM lv
  | .app f a => do levelMVarsOf f; levelMVarsOf a
  | .lam _ t b _ | .forallE _ t b _ => do levelMVarsOf t; levelMVarsOf b
  | .letE _ t v b _ => do levelMVarsOf t; levelMVarsOf v; levelMVarsOf b
  | .mdata _ b | .proj _ _ b => levelMVarsOf b
  | _ => pure ()

/-- `a + k ≤ b` is entailed by the native facts (`Set` included): `k = 0` needs `≤`, `k = 1`
needs `<`, larger offsets need a chain of strict steps. -/
partial def entails (f : IR.UniverseFacts) (a b : String) (k : Nat) : Bool :=
  if k == 0 then a == b || f.rel a b == "le" || f.rel a b == "lt"
  else if k == 1 then f.rel a b == "lt"
  else (("Set" :: f.levels.toList).any fun c => f.rel a c == "lt" && entails f c b (k - 1))

/-- Normal form `max(c, p₁ + k₁, …)` of a level without `imax`/metavariables. -/
partial def levelNF : Level → Option (Nat × List (Name × Nat))
  | .zero => some (0, [])
  | .param p => some (0, [(p, 0)])
  | .succ l => do let (c, ps) ← levelNF l; some (c + 1, ps.map fun (p, k) => (p, k + 1))
  | .max a b => do
    let (c1, p1) ← levelNF a
    let (c2, p2) ← levelNF b
    some (max c1 c2, p2.foldl (fun acc (p, k) =>
      match acc.find? (·.1 == p) with
      | some (_, k') => acc.map fun (q, j) => if q == p then (q, max k k') else (q, j)
      | none => acc ++ [(p, k)]) p1)
  | _ => none

/-- Universe obligation (docs/UNIVERSE_TRANSLATION.md, rule R3) for one reference: the target
universe argument `σ` for the referenced constant's parameter standing for source level `l`. -/
def checkInstantiation (f : IR.UniverseFacts) (own : Array String) (l : String) (σ : Level) :
    Except String Unit := do
  if own.contains l then
    unless σ.normalize == .param (levelParamName l) do
      throw s!"coherence: source level {l} is shared with the referring declaration, so its argument must be u_{l}, not {σ}"
    return
  let some (c, ps) := levelNF σ.normalize | throw s!"argument {σ} for {l} is outside the supported level fragment"
  unless entails f "Set" l c do throw s!"argument {σ}: Set + {c} ≤ {l} is not entailed by the source universe graph"
  for (p, k) in ps do
    let some m := own.find? (fun g => levelParamName g == p)
      | throw s!"argument {σ} mentions {p}, which is not a parameter of the referring declaration"
    unless entails f m l k do throw s!"argument {σ}: {m} + {k} ≤ {l} is not entailed by the source universe graph"

/-- All constant occurrences of `e` with their universe arguments. -/
partial def constOccurrences (e : Expr) (acc : Array (Name × List Level) := #[]) : Array (Name × List Level) :=
  match e with
  | .const c ls => acc.push (c, ls)
  | .app f a => constOccurrences a (constOccurrences f acc)
  | .lam _ t b _ | .forallE _ t b _ => constOccurrences b (constOccurrences t acc)
  | .letE _ t v b _ => constOccurrences b (constOccurrences v (constOccurrences t acc))
  | .mdata _ b | .proj _ _ b => constOccurrences b acc
  | _ => acc

/-- Check every universe argument at every reference to a generalized constant in `e`;
returns the number of checked arguments. -/
def checkUniverseObligations (genv : GEnv) (own : Array String) (e : Expr) : Except String Nat := do
  let mut n := 0
  for (c, ls) in constOccurrences e do
    if let some globals := genv.constGlobals[c]? then
      unless globals.size == ls.length do throw s!"{c}: {ls.length} universe arguments for {globals.size} parameters"
      for l in globals, σ in ls do
        match checkInstantiation genv.facts own l σ with
        | .ok () => n := n + 1
        | .error msg => throw s!"reference to {c}: {msg}"
  return n

/-- Solve the universe metavariables introduced at references to generalized constants:
type-check with Lean's checker (which unifies universe levels; terms are not changed) and
unify the value's type with the declared type; any level left unconstrained is set to `0`.
The kernel re-checks the result. -/
def solveLevels (ty val : Expr) : MetaM (Expr × Expr × Array String × Nat) := do
  let mut diags : Array String := #[]
  try Meta.check ty catch e => diags := diags.push s!"Meta.check type: {← e.toMessageData.toString}"
  try Meta.check val catch e => diags := diags.push s!"Meta.check value: {← e.toMessageData.toString}"
  try
    unless ← withTransparency .all <| isDefEq (← inferType val) ty do
      diags := diags.push "value type not unified with the declared type by Meta.isDefEq"
  catch e => diags := diags.push s!"isDefEq: {← e.toMessageData.toString}"
  let ty ← instantiateMVars ty
  let val ← instantiateMVars val
  let ((), ms) := ((levelMVarsOf ty *> levelMVarsOf val).run #[])
  -- Residual levels are unconstrained by unification; they are defaulted to 0 and *recorded*,
  -- and must still pass the universe obligations (rule R3) like every other argument.
  for m in ms do assignLevelMVar m levelZero
  return (← instantiateMVars ty, ← instantiateMVars val, diags, ms.size)

end Rocq2Lean

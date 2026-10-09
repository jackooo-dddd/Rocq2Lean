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
  inds : Std.HashMap String IndTarget := {}
  /-- Global universe names read directly as the level of a Lean `Sort` (adapter checks only). -/
  sortOverride : Std.HashMap String Level := {}
  deriving Inhabited

structure TCtx where
  genv : GEnv
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
      | none => failT "UNSUPPORTED_FEATURE" s!"monomorphic global universe {n} (outside the pilot universe fragment)"
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
  | .case .. => failT "UNSUPPORTED_FEATURE" "match (Case lowering not enabled)"
  | .proj .. => failT "UNSUPPORTED_FEATURE" "primitive projection"
  | .fix .. => failT "UNSUPPORTED_FEATURE" "fixpoint (Fix lowering not enabled)"
  | .cofix .. => failT "UNSUPPORTED_FEATURE" "cofixpoint"
  | .prim k _ => failT "UNSUPPORTED_FEATURE" s!"primitive {k}"

/-- Translate an application head. `args` are the already-translated arguments, needed when
the target's universe is computed from them. -/
partial def transHead (f : IR.Term) (args : Array Expr) : TransM Expr := do
  match f with
  | .const c u =>
    unless u.isEmpty do failT "UNSUPPORTED_FEATURE" s!"non-empty universe instance on constant {c}"
    match (← read).genv.consts[c]? with
    | some n => pure (mkConst n)
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
  if e.hasMVar then failT "TRANSLATION_FAILED" "translated term has unresolved metavariables"
  return e

def runTrans {α} (genv : GEnv) (x : TransM α) : MetaM (Except TransError α) :=
  (x { genv }).run

end Rocq2Lean

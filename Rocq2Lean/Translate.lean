import Lean
import Rocq2Lean.IR

/-!
# Expression translation

`trans` maps a source IR term to a Lean `Expr`. Binders are opened with fresh free variables
(`withLocalDecl`/`withLetDecl`) so that Lean type inference is available where the source
leaves information implicit (the universe of a template-polymorphic inductive, cast
validation). Terms are closed again by plain de Bruijn abstraction (`bindFVars`, not
`mkLambdaFVars`, which β-reduces binder types containing universe metavariables);
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
  /-- A generated inductive whose source global levels became `n` Lean universe parameters
  (docs/UNIVERSE_TRANSLATION.md, R2T/R5): references get fresh level metavariables, solved by
  Lean's unifier from the arguments and re-checked (template levels: determined by the template
  parameters' sorts, R5; other global levels: R3 against the native universe graph). -/
  | params (n : Nat) (template : Bool)
  deriving Repr, Inhabited, BEq

/-- How a source inductive block is realised in Lean. -/
structure IndTarget where
  types : Array Name
  ctors : Array (Array Name)
  univ : UnivRule
  /-- Rule identifier: a bootstrap rule id, or `generated`. -/
  rule : String
  /-- Template inductives: positions (regular order) of the parameters binding template levels. -/
  templateParamPos : Array Nat := #[]
  /-- A primitive record translated to a structure-like inductive (projections allowed). -/
  isStructure : Bool := false
  /-- Indices of the universe parameters that are template levels (R5: instantiated from the
  arguments); the others are generalized non-template levels (R3 at references). -/
  templateLevelIdx : Array Nat := #[]
  deriving Inhabited, Repr

structure GEnv where
  consts : Std.HashMap String Name := {}
  /-- Number of universe parameters of each accepted constant (generalized global levels). -/
  constLevels : Std.HashMap String Nat := {}
  /-- Source global level of each universe parameter of each accepted constant, by target name. -/
  constGlobals : Std.HashMap Name (Array String) := {}
  /-- Template levels of the translated template inductives (R5, exempt from R3). -/
  templateLevels : Std.HashSet String := {}
  /-- Native universe facts of the export. -/
  facts : IR.UniverseFacts := { levels := #[], relations := #[] }
  inds : Std.HashMap String IndTarget := {}
  /-- Global universe names read directly as the level of a Lean `Sort` (adapter checks only). -/
  sortOverride : Std.HashMap String Level := {}
  /-- R6: universe-polymorphic constants (source key / target name ↦ number of universe variables,
  which are the target's first universe parameters `v_0 … v_{k-1}`). -/
  constPoly : Std.HashMap String Nat := {}
  polyByTarget : Std.HashMap Name Nat := {}
  /-- R8: motive levels of accepted constants (target name ↦ source levels whose parameter is a
  sort level, `Type@{l} ↦ Sort u_l`). -/
  admitting : Std.HashMap Name (Array String) := {}
  deriving Inhabited

structure TCtx where
  genv : GEnv
  /-- Global monomorphic levels of the declaration being translated, as Lean universe
  parameters (`Type@{l+n} ↦ Sort (u_l + n + 1)`). -/
  globalLevels : Std.HashMap String Level := {}
  /-- R6: the Lean levels standing for the universe variables `var i` of a universe-polymorphic
  declaration being translated (its parameters `v_i`). -/
  polyLevels : Array Level := #[]
  /-- R2⁺: read every source universe through its fact-reduced form (`factReduceUniverse`). -/
  factReduce : Bool := false
  /-- R8: own levels translated as sort levels (`Type@{l + n} ↦ Sort (u_l + n)`, admitting Prop). -/
  admitLevels : Array String := #[]
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

/-- `a + k ≤ b` is entailed by the native facts (`Set` included): `k = 0` needs `≤`, `k = 1`
needs `<`, larger offsets need a chain of strict steps. -/
partial def entails (f : IR.UniverseFacts) (a b : String) (k : Nat) : Bool :=
  if k == 0 then a == b || f.rel a b == "le" || f.rel a b == "lt"
  else if k == 1 then f.rel a b == "lt"
  else (("Set" :: f.levels.toList).any fun c => f.rel a c == "lt" && entails f c b (k - 1))

/-- R2⁺ (docs/UNIVERSE_TRANSLATION.md): drop a summand `Set + k` of an algebraic universe when
another summand `l + j` is at least as large under the native facts (`k ≤ j`, every level being
≥ `Set`, or `Set + (k - j) ≤ l` entailed). In Rocq the two universes are *equal*; in Lean the
dropped summand would be a sort floor that the value need not reach (Rocq types `Prop` at
`Type@{Set+1}`, Lean at `Sort 1`). Used only on a retry after the kernel rejected R2. -/
def factReduceUniverse (f : IR.UniverseFacts) (u : Array LevelExpr) : Array LevelExpr :=
  u.filter fun e => match e.level with
    | .set => !(u.any fun e' => match e'.level with
        | .global n => e.offset ≤ e'.offset || entails f "Set" n (e.offset - e'.offset)
        | .var _ => e.offset ≤ e'.offset
        | .set => false)
    | _ => true

/-- Lean sort level of a source `Type@{u}` in the pilot fragment: `Set + n ↦ n + 1`, `max`
componentwise. Global monomorphic levels and polymorphic variables are rejected. -/
def transTypeLevel (u : Array LevelExpr) : TransM Level := do
  if u.isEmpty then failT "EXPORT_VALIDATION_FAILED" "empty algebraic universe"
  let ctx ← read
  let u := if ctx.factReduce then factReduceUniverse ctx.genv.facts u else u
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
        | some l =>
          -- R8: a motive level's parameter is the sort level itself (it may be 0: Prop)
          if (← read).admitLevels.contains n then pure (l.addOffset e.offset)
          else pure (l.addOffset (e.offset + 1))
        | none => failT "UNSUPPORTED_FEATURE" s!"global universe {n} not generalized for this declaration"
    | .var i =>
      -- R6: a universe variable of the polymorphic declaration being translated
      match (← read).polyLevels[i]? with
      | some l => pure (l.addOffset (e.offset + 1))
      | none => failT "UNSUPPORTED_FEATURE" s!"universe-polymorphic level variable {i} outside a polymorphic declaration"
  let mut acc := parts[0]!
  for l in parts[1:] do acc := mkLevelMax' acc l
  return acc.normalize

/-- R6: Lean level of one level of a source universe instance (the *level*, not the sort above it):
`Set ↦ 0`, `var i ↦ v_i`, a global level ↦ the referring declaration's own variable for it
(R2S; it is one of its own levels). Consistent with `transTypeLevel`: `Type@{l} ↦ Sort (ι l + 1)`. -/
def transInstLevel : IR.Level → TransM Level
  | .set => pure .zero
  | .var i => do
    match (← read).polyLevels[i]? with
    | some l => pure l
    | none => failT "UNSUPPORTED_FEATURE" s!"universe variable {i} in an instance outside a polymorphic declaration"
  | .global n => do
    if (← read).genv.sortOverride.contains n then
      failT "UNSUPPORTED_FEATURE" s!"adapter-bound level {n} in a universe instance"
    match (← read).globalLevels[n]? with
    | some l => pure l
    | none => failT "UNSUPPORTED_FEATURE" s!"global universe {n} in an instance is not generalized for this declaration"

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

/-- Universe arguments at a reference to a declaration whose parameters stand for the source global
levels `globals` (in parameter order): a level that is also one of the referring declaration's own
levels is *the same level* in monomorphic Rocq, so the reference uses the referring declaration's
own variable for it (coherence by construction, R3/R2S); any other level gets a fresh metavariable,
solved from the arguments and checked by R3 (no raising). -/
def sharedOrFreshLevels (globals : Array String) : TransM (List Level) := do
  let own := (← read).globalLevels
  globals.toList.mapM fun l => match own[l]? with
    | some v => pure v
    | none => liftMeta mkFreshLevelMVar

def univArgs (mind : String) (t : IndTarget) (u : Array IR.Level) (args : Array Expr) (target : Name := .anonymous) :
    TransM (List Level) := do
  unless u.isEmpty do
    failT "UNSUPPORTED_FEATURE" s!"non-empty universe instance on {mind} (pilot supports monomorphic references only)"
  match t.univ with
  | .mono => pure []
  | .params n false =>
    match (← read).genv.constGlobals[target]? with
    | some gs => if gs.size == n then sharedOrFreshLevels gs else liftMeta do (List.range n).mapM fun _ => mkFreshLevelMVar
    | none => liftMeta do (List.range n).mapM fun _ => mkFreshLevelMVar
  | .params n true =>
    -- template levels: fresh (R5, from the arguments); other levels: shared or fresh (R3)
    let gs := (← read).genv.constGlobals[target]?.getD #[]
    let own := (← read).globalLevels
    (List.range n).mapM fun k => do
      if t.templateLevelIdx.contains k || gs.size != n then liftMeta mkFreshLevelMVar
      else match own[gs[k]!]? with
        | some v => pure v
        | none => liftMeta mkFreshLevelMVar
  | .templateFromArg k =>
    if h : k < args.size then
      -- The level may still contain metavariables (proof-local levels, R2B; references to
      -- generalized constants): they are solved with the rest of the declaration (`solveLevels`),
      -- and any left unassigned must be justified (R3′).
      let l ← liftMeta (do instantiateLevelMVars (← getLevel args[k]))
      pure [l.normalize]
    else
      failT "UNSUPPORTED_FEATURE" s!"{mind} used with fewer than {k + 1} arguments: its universe is undetermined"

/-- R5: a template inductive is translated at the template defaults' quality Type; an argument for a
template parameter that is a proposition (a Prop-quality instance in Rocq) is rejected explicitly. -/
def checkTemplateArgs (mind : String) (t : IndTarget) (args : Array Expr) : TransM Unit := do
  for k in t.templateParamPos do
    if h : k < args.size then
      -- the codomain sort of the argument's type (the argument itself for `Type@{l}`, the result
      -- of the type family for an arity parameter)
      let l ← liftMeta do
        forallTelescopeReducing (← inferType args[k]) fun _ b => do
          match ← whnf b with
          | .sort s => instantiateLevelMVars s
          | _ => pure (Level.succ .zero)
      if l.normalize == .zero then
        failT "UNSUPPORTED_FEATURE" (s!"template inductive {mind} instantiated at quality Prop: parameter {k} receives a " ++
          "proposition (a Prop instance, or Rocq's Prop ≤ Type cumulativity), which Lean cannot express without a lift")

/-- Instantiate assigned *universe-level* metavariables only, without touching term structure.
(`instantiateMVars` also β-reduces applications whose head becomes or is a λ once metavariables
in it are instantiated, which would change the translated term: a source `(fun _ => nat) l` must
stay a β-redex in the target.) Translated terms contain no expression metavariables. -/
partial def instLevelMVars (e : Expr) : MetaM Expr := do
  if !e.hasLevelMVar then return e
  match e with
  | .sort l => return .sort (← instantiateLevelMVars l)
  | .const n ls => return .const n (← ls.mapM instantiateLevelMVars)
  | .app f a => return .app (← instLevelMVars f) (← instLevelMVars a)
  | .lam n t b bi => return .lam n (← instLevelMVars t) (← instLevelMVars b) bi
  | .forallE n t b bi => return .forallE n (← instLevelMVars t) (← instLevelMVars b) bi
  | .letE n t v b nd => return .letE n (← instLevelMVars t) (← instLevelMVars v) (← instLevelMVars b) nd
  | .mdata d b => return .mdata d (← instLevelMVars b)
  | .proj sn i b => return .proj sn i (← instLevelMVars b)
  | _ => return e

/-- Close `e` over the free variables `xs` (lambdas, foralls, or lets for let-bound locals) by plain
de Bruijn abstraction of the local declarations, keeping every `let`. Unlike `mkLambdaFVars`/
`mkForallFVars`, it never rewrites the binder types (those instantiate metavariables and β-reduce
types that mention universe metavariables, which would change the translated term). -/
def bindFVars (isLambda : Bool) (xs : Array Expr) (e : Expr) : MetaM Expr := do
  let mut r := e.abstract xs
  for i' in [0:xs.size] do
    let i := xs.size - 1 - i'
    let d ← xs[i]!.fvarId!.getDecl
    let ty := d.type.abstractRange i xs
    r := match d with
      | .ldecl (value := v) .. => .letE d.userName ty (v.abstractRange i xs) r false
      | _ => if isLambda then .lam d.userName ty r d.binderInfo else .forallE d.userName ty r d.binderInfo
  return r

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
def minorTelescope {α} (minorTy : Expr) (nfields : Nat) (iname : Name) (params : Array Expr)
    (k : Array Expr → Array Expr → Array Expr → Expr → TransM α) : TransM α :=
  forallBoundedTelescope minorTy (some nfields) fun fields rest => do
    unless fields.size == nfields do failT "TRANSLATION_FAILED" "minor premise has too few field binders"
    -- A field is recursive iff its type is the inductive applied to the *same* parameters (a field
    -- `list A` of a constructor of `list (list A)` mentions `list` but is not recursive).
    let isRec (t : Expr) : MetaM Bool := do
      let t ← whnf t
      unless t.getAppFn.isConstOf iname && t.getAppNumArgs ≥ params.size do return false
      (t.getAppArgs.extract 0 params.size).zip params |>.allM fun (a, b) => isDefEq a b
    let mut recFields := #[]
    for y in fields do
      let yt ← liftMeta do inferType y
      let functional ← liftMeta do forallTelescopeReducing yt fun zs body => do
        return !zs.isEmpty && (← isRec body)
      if functional then failT "UNSUPPORTED_FEATURE" "functional recursive constructor field"
      if ← liftMeta (isRec yt) then recFields := recFields.push y
    forallBoundedTelescope rest (some recFields.size) fun ihs res => do
      unless ihs.size == recFields.size do failT "TRANSLATION_FAILED" "minor premise has too few recursive results"
      k fields recFields ihs res

/-- Positions `i < r` of a fixpoint's leading arguments that some recursive call changes, read
from the source syntax: `depth` counts the binders between the fix binder and `t`, so the function
is `rel depth` and the i-th leading lambda is `rel (depth - 1 - i)` (once `depth ≥ nl`). -/
partial def changedParams (t : IR.Term) (nl r depth : Nat) (acc : Std.HashSet Nat := {}) : Std.HashSet Nat :=
  let go (u : IR.Term) (d : Nat) (a : Std.HashSet Nat) := changedParams u nl r (depth + d) a
  match t with
  | .app f args =>
    let acc := match f with
      | .rel j =>
        if j == depth && depth ≥ nl then
          (List.range (min r args.size)).foldl (fun a i =>
            match args[i]! with
            | .rel k => if k + 1 + i == depth then a else a.insert i
            | _ => a.insert i) acc
        else acc
      | _ => acc
    args.foldl (fun a x => go x 0 a) (go f 0 acc)
  | .prod _ ty b | .lam _ ty b => go b 1 (go ty 0 acc)
  | .letIn _ v ty b => go b 1 (go ty 0 (go v 0 acc))
  | .cast c _ ty => go ty 0 (go c 0 acc)
  | .case _ _ _ _ ps pctx ret c brs =>
    brs.foldl (fun a (ctx, b) => go b ctx.size a) (go c 0 (go ret pctx.size (ps.foldl (fun a x => go x 0 a) acc)))
  | .fix ds _ | .cofix ds _ => ds.foldl (fun a (_, ty, b, _) => go b ds.size (go ty 0 a)) acc
  | .evar _ args => args.foldl (fun a x => go x 0 a) acc
  | .proj _ _ _ c => go c 0 acc
  | _ => acc

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
      bindFVars false #[x] b'
  | .lam n ty b => withPath "lam" do
    checkRelevant n
    let ty' ← withPath "ty" (trans ty)
    withLocalDecl (binderName n) .default ty' fun x => do
      let b' ← withPath "b" (withLocal x (trans b))
      bindFVars true #[x] b'
  | .letIn n v ty b => withPath "let" do
    checkRelevant n
    let ty' ← withPath "ty" (trans ty)
    let v' ← withPath "v" (trans v)
    withLetDecl (binderName n) ty' v' fun x => do
      let b' ← withPath "b" (withLocal x (trans b))
      bindFVars true #[x] b'
  | .app f args => withPath "app" do
    let args' ← args.mapIdxM fun k a => withPath s!"arg{k}" (trans a)
    let f' ← withPath "f" (transHead f args')
    let e := mkAppN f' args'
    -- Universe arguments left as metavariables at a reference (generalized constants, generated
    -- inductives with level parameters) are solved here from the argument types when possible,
    -- so that later lowering sees concrete levels; `solveLevels` finishes and the kernel re-checks.
    if f'.isConst && f'.constLevels!.any (·.hasMVar) then
      liftMeta do try Meta.check e catch _ => pure ()
    liftMeta (instLevelMVars e)
  | .const .. | .ind .. | .construct .. => transHead t #[]
  | .case ind npar _ puinst pparams pctx pret scrut brs =>
    withPath "case" (transCase ind npar puinst pparams pctx pret scrut brs)
  | .proj ind npars arg t => withPath "proj" do
    -- M5: a primitive projection of a primitive record (a generated structure-like inductive)
    -- becomes Lean's kernel projection `Expr.proj` on the same field.
    let tgt ← lookupInd ind
    unless tgt.rule == "generated" && tgt.isStructure do
      failT "UNSUPPORTED_FEATURE" s!"projection of {ind.mind}, which is not a translated primitive record"
    let some (.inductInfo iv) := (← getEnv).find? tgt.types[ind.idx]!
      | failT "TRANSLATION_FAILED" s!"no inductive {tgt.types[ind.idx]!} in the target environment"
    unless iv.numParams == npars do
      failT "EXPORT_VALIDATION_FAILED" s!"projection of {ind.mind} with {npars} parameters, the record has {iv.numParams}"
    return .proj tgt.types[ind.idx]! arg (← trans t)
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
  let scrut' ← withPath "scrutinee" (trans scrut)
  let sty ← liftMeta do whnf (← instLevelMVars (← inferType scrut'))
  -- Inductives with level parameters: the recursor's inductive levels are those of the
  -- scrutinee's type (kernel-forced); otherwise from the universe rule.
  let indLvls ← match tgt.univ with
    | .params .. => if sty.getAppFn.isConstOf iname then pure sty.getAppFn.constLevels!
                    else failT "TRANSLATION_FAILED" s!"scrutinee type is not an application of {iname}"
    | _ => univArgs ind.mind tgt puinst params
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
    return (← bindFVars true xs ret, u.normalize)
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
    let minor ← minorTelescope minorTy nfields iname params fun fields _ ihs _ => do
      let body ← withPath s!"branch{k}" (withReader (fun c => { c with locals := c.locals ++ fields }) (trans bbody))
      bindFVars true (fields ++ ihs) body
    minors := minors.push minor
    ty := rest.instantiate1 minor
  return mkAppN recConst (params ++ #[motive] ++ minors ++ idx ++ #[scrut'])

/-- Replace each recursive call `f P… y rest` by `ih_y rest'`, where `y` is a direct recursive
constructor field. Parameters before the decreasing argument must be the function's own
parameters, except index variables of the decreasing argument, which must be the
corresponding index of `y`'s type. Any other occurrence of `f` is rejected. -/
partial def replaceRecCalls (f : FVarId) (P : Array Expr) (idxPos : Array (Option Nat))
    (fieldIH : Array (Expr × Expr × Array Expr)) (gpos : Array Nat) (e : Expr) : TransM Expr := do
  let go := replaceRecCalls f P idxPos fieldIH gpos
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
        if gpos.contains i then continue          -- generalized: passed to the recursive result
        match idxPos[i]! with
        | none =>
          unless args[i]! == P[i]! do
            failT "UNSUPPORTED_FEATURE" s!"recursive call changes parameter {i}, which precedes the decreasing argument"
        | some j =>
          unless args[i]! == yIdx[j]! do
            failT "UNSUPPORTED_FEATURE" s!"recursive call passes index argument {i} different from the field's index"
      return mkAppN ih ((← gpos.mapM fun i => go args[i]!) ++ (← (args.extract (r + 1) args.size).mapM go))
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
    -- Leading arguments that recursive calls change (other than indices of the decreasing
    -- argument) are generalized in the motive: λ P x Q, I.rec params (λ idx x, ∀ G Q, T) … idx x G Q.
    let gpos := (changedParams fbody lams.size rarg 0).toArray.qsort (· < ·) |>.filter (idxPos[·]!.isNone)
    let G := gpos.map (P[·]!)
    for i in [0:rarg] do
      unless gpos.contains i do
        let t ← liftMeta do instantiateMVars (← inferType P[i]!)
        if G.any (t.containsFVar ·.fvarId!) then
          failT "UNSUPPORTED_FEATURE" s!"argument {i} depends on an argument that recursive calls change"
    if G.any (xty.containsFVar ·.fvarId!) then
      failT "UNSUPPORTED_FEATURE" "the decreasing argument's type depends on an argument that recursive calls change"
    let indLvls := xty.getAppFn.constLevels!
    let QT ← bindFVars false (G ++ Q) T
    let u := (← liftMeta do instantiateLevelMVars (← getLevel QT)).normalize
    let motive ← bindFVars true (idx.push x) QT
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
      let minor ← minorTelescope minorTy nfields iname params fun fields recFields ihs res => do
        let fieldIH ← (recFields.zip ihs).mapM fun (y, ih) => do
          let yt ← liftMeta do whnf (← inferType y)
          return (y, ih, yt.getAppArgs.extract rv.numParams yt.getAppArgs.size)
        let res ← liftMeta (whnf res)
        forallBoundedTelescope res (some (G.size + Q.size)) fun gqs _ => do
          unless gqs.size == G.size + Q.size do failT "TRANSLATION_FAILED" "minor result has fewer binders than the motive"
          let gs := gqs.extract 0 G.size
          let qs := gqs.extract G.size gqs.size
          -- The recursor runs this branch at every recursion depth: here the decreasing argument
          -- *is* the constructor applied to the fields, and the index variables of its type are
          -- that application's indices (not the outermost call's arguments).
          let xk := mkAppN (mkConst tgt.ctors[cind.idx]![k]! indLvls) (params ++ fields)
          let xkIdx ← liftMeta do
            let t ← whnf (← inferType xk)
            pure (t.getAppArgs.extract rv.numParams t.getAppArgs.size)
          let P' := Id.run do
            let mut P' := P
            for i in gpos, g in gs do P' := P'.set! i g
            for i in [0:P.size] do
              if let some j := idxPos[i]! then P' := P'.set! i xkIdx[j]!
            return P'
          let locals := outer ++ #[fv] ++ P' ++ #[xk] ++ qs ++ fields
          let body ← withPath s!"branch{k}" (withReader (fun c => { c with locals := locals }) (trans bbody))
          let body ← replaceRecCalls fv.fvarId! P' idxPos fieldIH gpos body
          bindFVars true (fields ++ ihs ++ gs ++ qs) body
      minors := minors.push minor
      ty := rest.instantiate1 minor
    let res ← bindFVars true as (mkAppN (mkAppN recConst (params ++ #[motive] ++ minors ++ idx ++ #[x])) (G ++ Q))
    if res.containsFVar fv.fvarId! then
      failT "UNSUPPORTED_FEATURE" "recursive function escapes the supported call pattern"
    return res

/-- Translate an application head. `args` are the already-translated arguments, needed when
the target's universe is computed from them. -/
partial def transHead (f : IR.Term) (args : Array Expr) : TransM Expr := do
  match f with
  | .const c u =>
    let genv := (← read).genv
    -- R6: a universe-polymorphic constant takes its source instance, level by level, as its first
    -- universe arguments; a monomorphic one must be referenced with the empty instance.
    let kp := genv.constPoly[c]?.getD 0
    unless u.size == kp do
      if kp == 0 then failT "UNSUPPORTED_FEATURE" s!"non-empty universe instance on constant {c}"
      else failT "EXPORT_VALIDATION_FAILED" s!"instance of {u.size} levels for polymorphic constant {c} with {kp} universe variables"
    let poly ← u.toList.mapM transInstLevel
    match genv.consts[c]? with
    | some n =>
      -- Universe parameters of a generalized constant: the referring declaration's own variable for
      -- a shared source level, otherwise a fresh metavariable solved by Lean's unifier (`solveLevels`).
      let k := genv.constLevels[c]?.getD 0 - kp
      let lvls ← match genv.constGlobals[n]? with
        | some gs => if gs.size == k then sharedOrFreshLevels gs else liftMeta do (List.range k).mapM fun _ => mkFreshLevelMVar
        | none => liftMeta do (List.range k).mapM fun _ => mkFreshLevelMVar
      pure (mkConst n (poly ++ lvls))
    | none => failT "TRANSLATION_FAILED" s!"reference to constant {c}, which has no accepted translation"
  | .ind i u =>
    let t ← lookupInd i
    checkTemplateArgs i.mind t args
    return mkConst t.types[i.idx]! (← univArgs i.mind t u args t.types[i.idx]!)
  | .construct i c u =>
    let t ← lookupInd i
    let cs := t.ctors[i.idx]!
    unless c < cs.size do
      failT "EXPORT_VALIDATION_FAILED" s!"constructor index {c} out of range for {i.mind}"
    checkTemplateArgs i.mind t args
    return mkConst cs[c]! (← univArgs i.mind t u args cs[c]!)
  | _ => trans f

end

/-- Translate a closed term and check that no free or meta variable escapes. -/
def transClosed (t : IR.Term) : TransM Expr := do
  let e ← instLevelMVars (← trans t)
  if e.hasFVar then failT "TRANSLATION_FAILED" "translated term has escaping free variables"
  if e.hasExprMVar then failT "TRANSLATION_FAILED" "translated term has unresolved metavariables"
  return e

def runTrans {α} (genv : GEnv) (x : TransM α) (globalLevels : Std.HashMap String Level := {})
    (polyLevels : Array Level := #[]) (factReduce : Bool := false) (admitLevels : Array String := #[]) :
    MetaM (Except TransError α) :=
  (x { genv, globalLevels, polyLevels, factReduce, admitLevels }).run

/-! ## Universe generalization -/

/-- Global level names occurring in a source term: in sorts and (R6) in universe instances. -/
partial def globalsOf (t : IR.Term) (acc : Std.HashSet String := {}) : Std.HashSet String :=
  let sortG (s : SortIR) (acc : Std.HashSet String) : Std.HashSet String :=
    match s with
    | .type u => u.foldl (fun a e => match e.level with | .global n => a.insert n | _ => a) acc
    | _ => acc
  let instG (u : Array IR.Level) (acc : Std.HashSet String) : Std.HashSet String :=
    u.foldl (fun a l => match l with | .global n => a.insert n | _ => a) acc
  let go := fun (t : IR.Term) (a : Std.HashSet String) => globalsOf t a
  match t with
  | .sort s => sortG s acc
  | .const _ u | .ind _ u | .construct _ _ u => instG u acc
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

/-- R8: levels that occur in a source type only as the codomain sort `Type@{l}` (one summand,
offset 0) of a binder type with at least one argument — motive-like binders `K : X → Type@{l}`,
which Rocq instantiates with Prop-valued families by cumulativity. Any other occurrence (another
sort, an instance) disqualifies the level. -/
partial def motiveLevels (ty : IR.Term) : Array String := Id.run do
  let rec codomain (t : IR.Term) (n : Nat) : Option (Nat × String) :=
    match t with
    | .prod _ _ b => codomain b (n + 1)
    | .sort (.type #[{ level := .global l, offset := 0 }]) => if n ≥ 1 then some (n, l) else none
    | _ => none
  -- (motive occurrences, other occurrences)
  let rec go (t : IR.Term) (acc : Std.HashSet String × Std.HashSet String) : Std.HashSet String × Std.HashSet String :=
    let (mot, oth) := acc
    match t with
    | .sort (.type u) => (mot, u.foldl (fun a e => match e.level with | .global n => a.insert n | _ => a) oth)
    | .const _ u | .ind _ u | .construct _ _ u =>
      (mot, u.foldl (fun a l => match l with | .global n => a.insert n | _ => a) oth)
    | .prod _ a b =>
      match codomain a 0 with
      | some (_, l) =>
        -- walk the domains of the motive's type, not its final sort
        let rec doms (t : IR.Term) (acc : Std.HashSet String × Std.HashSet String) :=
          match t with
          | .prod _ d r => doms r (go d acc)
          | _ => acc
        go b (doms a (mot.insert l, oth))
      | none => go b (go a acc)
    | .lam _ a b => go b (go a acc)
    | .letIn _ v a b => go b (go a (go v acc))
    | .app f args => args.foldl (fun a x => go x a) (go f acc)
    | .cast c _ a => go a (go c acc)
    | .case _ _ _ _ ps _ r c brs => brs.foldl (fun a b => go b.2 a) (go c (go r (ps.foldl (fun a x => go x a) acc)))
    | .proj _ _ _ c => go c acc
    | .fix ds _ | .cofix ds _ => ds.foldl (fun a (_, t, b, _) => go b (go t a)) acc
    | _ => acc
  let (mot, oth) := go ty ({}, {})
  return (mot.toArray.filter (!oth.contains ·)).qsort (· < ·)

/-- Lean universe parameter for a source global level: `u_` followed by the level name with
`.` replaced by `_` (e.g. `Corelib.Init.Logic.8 ↦ u_Corelib_Init_Logic_8`). -/
def levelParamName (n : String) : Name := Name.mkSimple ("u_" ++ n.replace "." "_")

/-- R6: Lean universe parameter for the `i`-th universe variable of a polymorphic declaration. -/
def polyParamName (i : Nat) : Name := Name.mkSimple s!"v_{i}"

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
def checkInstantiation (f : IR.UniverseFacts) (own : Array String) (l : String) (σ : Level)
    (body : Std.HashMap String Level := {}) (cAdmit : Bool := false) (ownAdmit : Array String := #[])
    (allowLift : Bool := false) : Except String Unit := do
  -- R8: a motive-level parameter stands for (image of the source level) + 1; `shift` converts the
  -- referring declaration's level for `l` into the referenced parameter's convention
  let dAdmit := ownAdmit.contains l
  if dAdmit && !cAdmit then
    throw s!"coherence: source level {l} is a motive level of the referring declaration but not of the referenced one"
  let shift (x : Level) : Level := if cAdmit && !dAdmit then x.succ else x
  if let some s := body[l]? then
    unless σ.normalize == (shift s).normalize do
      throw s!"coherence: source level {l} is a proof-local level of the referring declaration, solved as {s}; the argument must be the same, not {σ}"
    return
  if own.contains l then
    unless σ.normalize == (shift (.param (levelParamName l))).normalize do
      throw s!"coherence: source level {l} is shared with the referring declaration, so its argument must be u_{l}, not {σ}"
    return
  let some (c, ps) := levelNF σ.normalize | throw s!"argument {σ} for {l} is outside the supported level fragment"
  -- R8: for a motive-level parameter the argument 0 is Prop (always admissible), c ≥ 1 is Set + (c-1)
  unless (cAdmit && c == 0) || entails f "Set" l (if cAdmit then c - 1 else c) do
    throw s!"argument {σ}: Set + {c} ≤ {l} is not entailed by the source universe graph"
  for (p, k) in ps do
    let some m := own.find? (fun g => levelParamName g == p)
      | throw s!"argument {σ} mentions {p}, which is not a parameter of the referring declaration"
    -- effective offset between the referring level m and the referenced level l (R8 conventions)
    let e : Int := k + (if ownAdmit.contains m then 1 else 0) - (if cAdmit then 1 else 0)
    -- no raising (m + e ≤ l); in the cumulativity tier only (R3↑, reported per declaration), also the
    -- referring declaration's own level m itself (effective offset 0) where the source has l ≤ m:
    -- Rocq used c's level-l value at level m by upward cumulativity
    unless entails f m l e.toNat || (allowLift && e == 0 && entails f l m 0) do
      throw s!"argument {σ}: {m} + {k} ≤ {l} is not entailed by the source universe graph, nor is {l} ≤ {m} (with offset 0)"

/-- Summands `(source level, offset)` of a target level over the declaration's parameters, read
back as source levels (`u_l ↦ l`, constant `c ↦ Set + c`). -/
def sourceSummands (typeLevels : Array String) (σ : Level) (admit : Array String := #[]) :
    Except String (List (String × Nat)) := do
  let some (c, ps) := levelNF σ.normalize | throw s!"level {σ} is outside the supported level fragment"
  let ps ← ps.mapM fun (p, k) => do
    let some m := typeLevels.find? (fun g => levelParamName g == p)
      | throw s!"level {σ} mentions {p}, which is not a parameter of the declaration"
    -- R8: a motive-level parameter u_m is one above the image of m, so u_m + k reads as m + k + 1
    pure (m, if admit.contains m then k + 1 else k)
  return ("Set", c) :: ps

/-- `max lhs + k ≤ max rhs` is entailed by the native facts: every summand of the left side is
below some summand of the right side. -/
def summandsLeq (f : IR.UniverseFacts) (lhs rhs : List (String × Nat)) (k : Nat) : Bool :=
  lhs.all fun (a, i) => (a == "Set" && i + k == 0) || rhs.any fun (b, j) =>
    if i + k ≤ j then entails f a b 0 || a == "Set" else entails f a b (i + k - j)

/-- Rule R2B (docs/UNIVERSE_TRANSLATION.md): a proof-local level `m` (in the body, not the type) is
solved by Lean's unifier as `σ m`; every native fact between `m` and `Set`, a type level or another
proof-local level must still hold with each proof-local level read as its solution. -/
def checkBodyLevel (f : IR.UniverseFacts) (typeLevels : Array String) (sol : Std.HashMap String Level)
    (m : String) (admit : Array String := #[]) (propOffset : Bool := false) : Except String Unit := do
  let summ (x : String) : Except String (List (String × Nat)) :=
    match sol[x]? with
    | some σ => do
      -- R8: a solved motive level's solution is one above its image
      let ss ← sourceSummands typeLevels σ admit
      pure (if admit.contains x then ss.map fun (a, k) => (a, k - 1) else ss)
    | none => pure [(x, 0)]
  let mine (x : String) := x == "Set" || typeLevels.contains x || sol.contains x
  for (a, r, b) in f.relations do
    unless (a == m || b == m) && mine a && mine b do continue
    -- R2B-P (cumulativity tier only, reported per declaration): Rocq types Prop at Type@{Set+1}, Lean
    -- at Sort 1 (the image of Set), so a fact `Set < m` may stem from Prop alone; it is then checked
    -- as `Set ≤ m` (the kernel checks the typing itself)
    let k := if r == "lt" && !(propOffset && a == "Set") then 1 else 0
    unless summandsLeq f (← summ a) (← summ b) k do
      throw s!"proof-local level {m} solved as {sol[m]?}: native fact {a} {r} {b} does not hold for the solution"

/-- Minimal-model default of an unconstrained proof-local level `m` (R2B/R3′): the least level
satisfying its native lower bounds from `Set` and the type levels (`Set < m` gives 1, `l ≤ m`
gives `u_l`, `l < m` gives `u_l + 1`). -/
def minimalModelLevel (f : IR.UniverseFacts) (typeLevels : Std.HashMap String Level) (m : String) : Level := Id.run do
  let mut acc : Level := .zero
  for (a, r, b) in f.relations do
    unless b == m do continue
    let k := if r == "lt" then 1 else 0
    if a == "Set" then acc := mkLevelMax' acc (Level.ofNat k)
    else if let some v := typeLevels[a]? then acc := mkLevelMax' acc (v.addOffset k)
  return acc.normalize

/-- Rule R2F (inductives): the Lean level standing for each own source level `l` of an inductive
block is `ι l = max (u_l, ι m + k …)` over the native facts `m ≤ l` (k = 0) / `m < l` (k = 1)
between own levels (facts with `Set` are not used, as in R2). Every such fact then holds for all
values of the parameters. Mutually `≤` levels (equal in the source) contribute their parameters
directly; the remaining strict/one-way edges form a DAG, so the recursion terminates. -/
partial def ownLevelInterp (f : IR.UniverseFacts) (own : Array String) : Std.HashMap String Level := Id.run do
  let leq (a b : String) := f.rel a b == "le" || f.rel a b == "lt"
  let rec go (fuel : Nat) (l : String) : Level :=
    match fuel with
    | 0 => .param (levelParamName l)
    | fuel + 1 => Id.run do
      let mut acc : Level := .param (levelParamName l)
      for m in own do
        if m == l || !leq m l then continue
        let k := if f.rel m l == "lt" then 1 else 0
        if leq l m then acc := mkLevelMax' acc ((Level.param (levelParamName m)).addOffset k)   -- equal levels
        else acc := mkLevelMax' acc ((go fuel m).addOffset k)
      return acc.normalize
  let mut out : Std.HashMap String Level := {}
  for l in own do out := out.insert l (go (own.size + 1) l)
  return out

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
def checkUniverseObligations (genv : GEnv) (own : Array String) (e : Expr)
    (body : Std.HashMap String Level := {}) (ownAdmit : Array String := #[]) (allowLift : Bool := false) :
    Except String Nat := do
  let mut n := 0
  for (c, ls) in constOccurrences e do
    if let some globals := genv.constGlobals[c]? then
      -- R6: the first universe arguments of a polymorphic constant are its instance, not R3 obligations
      let ls := ls.drop (genv.polyByTarget[c]?.getD 0)
      unless globals.size == ls.length do throw s!"{c}: {ls.length} universe arguments for {globals.size} parameters"
      for l in globals, σ in ls do
        if genv.templateLevels.contains l then continue      -- R5, not R3
        let cAdmit := (genv.admitting[c]?.getD #[]).contains l
        match checkInstantiation genv.facts own l σ body cAdmit ownAdmit allowLift with
        | .ok () => n := n + 1
        | .error msg => throw s!"reference to {c}: {msg}"
  return n

/-- Solve the universe metavariables introduced at references to generalized constants:
type-check with Lean's checker (which unifies universe levels; terms are not changed) and
unify the value's type with the declared type; any level left unconstrained is set to `0`.
The kernel re-checks the result. -/
def solveLevels (ty val : Expr) (dflt : LMVarId → MetaM Level := fun _ => pure .zero) (beforeDefault : MetaM Unit := pure ()) :
    MetaM (Expr × Expr × Array String × List Name × Expr × Expr × List Level) := do
  let mut diags : Array String := #[]
  try Meta.check ty catch e => diags := diags.push s!"Meta.check type: {← e.toMessageData.toString}"
  try Meta.check val catch e => diags := diags.push s!"Meta.check value: {← e.toMessageData.toString}"
  try
    unless ← withTransparency .all <| isDefEq (← inferType val) ty do
      diags := diags.push "value type not unified with the declared type by Meta.isDefEq"
  catch e => diags := diags.push s!"isDefEq: {← e.toMessageData.toString}"
  -- Own type levels still unassigned after unification become universe parameters (R2S).
  beforeDefault
  let ty ← instLevelMVars ty
  let val ← instLevelMVars val
  let ((), ms) := ((levelMVarsOf ty *> levelMVarsOf val).run #[])
  -- Residual levels are unconstrained by unification; they are defaulted to 0 and *recorded*,
  -- must still pass the universe obligations (rule R3) like every other argument, and are only
  -- accepted with a justification: the caller kernel-checks the generic variant returned here,
  -- in which each residual is a fresh universe parameter (`u_residual_i`).
  let ps := (List.range ms.size).map fun i => Name.mkSimple s!"u_residual_{i}"
  let sub (l : Level) : Option Level := match l with
    | .mvar id => (ms.findIdx? (· == id)).map fun i => .param ps[i]!
    | _ => none
  let gty := ty.replaceLevel sub
  let gval := val.replaceLevel sub
  let ds ← ms.toList.mapM dflt
  for m in ms, d in ds do assignLevelMVar m d
  return (← instLevelMVars ty, ← instLevelMVars val, diags, ps, gty, gval, ds)

end Rocq2Lean

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
  /-- M6: number of non-uniform source parameters (after the uniform ones); in Lean they are the
  first indices of the inductive (Rocq's case binds them as parameters: convoy lowering). -/
  nonUniform : Nat := 0
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

/-- M6 accessibility lowering (`transFixAcc`): the recursive calls of the fixpoint being lowered.
Inside `Acc.rec`'s minor premise the decreasing argument is the proof component of the carrier
element `s`; a call `f … a …` becomes `ih ⟨j, a⟩ ?c …`, where `?c : R ⟨j, a⟩ s` is filled once the
call-graph relation `R` is known (`sites` records each call's local context, pair and hole). -/
structure AccSite where
  f : FVarId
  s : Expr
  ih : Expr
  R : Expr
  nP : Nat
  idxPos : Array (Option Nat)
  gpos : Array Nat
  expected : Array Expr
  hasIdx : Bool
  nparams : Nat
  idxTy : Expr
  idxLvl : Level
  fam : Expr
  /-- fvars of the context of `Acc.rec`'s minor premise (not part of a call's own context) -/
  base : Array FVarId
  /-- first pass: the call sites' disjuncts `D_c = λ y s, ∃ ctx_c, y = ⟨j_c, a_c⟩` are collected;
  second pass: `ds` are known and each call proves its own disjunct -/
  collect : Bool
  dsRef : IO.Ref (Array Expr)
  ds : Array Expr
  counter : IO.Ref Nat

structure TCtx where
  genv : GEnv
  /-- M6: the accessibility-lowered fixpoint whose recursive calls are being translated. -/
  accSite : Option AccSite := none
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


/-! ## M6: accessibility lowering (structural recursion on a proof, into data) -/

/-- `⟨j, a⟩ : Σ' i, I params i` (an inductive with one index) or `a` itself (no index). -/
def accMk (hasIdx : Bool) (idxTy fam : Expr) (idxLvl : Level) (j a : Expr) : Expr :=
  if hasIdx then mkAppN (mkConst ``PSigma.mk [idxLvl, .zero]) #[idxTy, fam, j, a] else a

/-- The carrier element of a proof `a : I params j`. -/
def accPairOf (hasIdx : Bool) (nparams : Nat) (idxTy fam : Expr) (idxLvl : Level) (a : Expr) : MetaM Expr := do
  if !hasIdx then return a
  let ty ← whnf (← inferType a)
  let some j := ty.getAppArgs[nparams]? | throwError "accessibility lowering: proof without index"
  return accMk hasIdx idxTy fam idxLvl j a

/-- Binder names without macro scopes (hygienic names such as `mkArrow`'s `x✝` do not survive the
report's string round trip; binder names carry no meaning). -/
partial def eraseBinderScopes : Expr → Expr
  | .lam n t b bi => .lam n.eraseMacroScopes (eraseBinderScopes t) (eraseBinderScopes b) bi
  | .forallE n t b bi => .forallE n.eraseMacroScopes (eraseBinderScopes t) (eraseBinderScopes b) bi
  | .letE n t v b nd => .letE n.eraseMacroScopes (eraseBinderScopes t) (eraseBinderScopes v) (eraseBinderScopes b) nd
  | .app f a => .app (eraseBinderScopes f) (eraseBinderScopes a)
  | .mdata d b => .mdata d (eraseBinderScopes b)
  | .proj s i b => .proj s i (eraseBinderScopes b)
  | e => e

/-- Right-nested disjunction `D₀ ∨ (D₁ ∨ …)`; `False` when empty. -/
def mkDisj : List Expr → Expr
  | [] => mkConst ``False
  | [d] => d
  | d :: ds => mkApp2 (mkConst ``Or) d (mkDisj ds)

/-- Proof of `mkDisj ds` from a proof `h` of its `r`-th disjunct. -/
def mkDisjIntro : List Expr → Nat → Expr → Expr
  | [_], _, h => h
  | d :: ds, 0, h => mkApp3 (mkConst ``Or.inl) d (mkDisj ds) h
  | d :: ds, r + 1, h => mkApp3 (mkConst ``Or.inr) d (mkDisj ds) (mkDisjIntro ds r h)
  | [], _, h => h

/-- `∃ x₁, … ∃ xₙ, body` over local variables (dependencies handled by abstraction). -/
def mkExistsFVars (xs : Array Expr) (body : Expr) : MetaM Expr := do
  let mut b := body
  for x in xs.reverse do
    let ty ← inferType x
    b := mkApp2 (mkConst ``Exists [← getLevel ty]) ty (← mkLambdaFVars #[x] b)
  return b

/-- A proof of `∃ x₁ … xₙ, y = y` (as built by `mkExistsFVars`) with witnesses `ws` and `Eq.refl`. -/
partial def mkExistsIntro (prop : Expr) (ws : List Expr) (refl : Expr) : MetaM Expr := do
  match ws with
  | [] => return refl
  | w :: ws =>
    let prop ← whnfR prop
    let #[α, p] := prop.getAppArgs | throwError "accessibility lowering: unexpected existential"
    let lvl := prop.getAppFn.constLevels!
    let inner ← mkExistsIntro ((p.beta #[w])) ws refl
    return mkAppN (mkConst ``Exists.intro lvl) #[α, p, w, inner]

/-- A recursive call `f args` of an accessibility-lowered fixpoint: `ih ⟨j, a⟩ ⟨ctx, rfl⟩ G Q`. -/
def accCallSite (ac : AccSite) (args : Array Expr) : TransM Expr := do
  unless args.size ≥ ac.nP + 1 do failT "UNSUPPORTED_FEATURE" "recursive call without its decreasing argument"
  let a := args[ac.nP]!
  let mut gs : Array Expr := #[]
  for i in [0:ac.nP] do
    if ac.gpos.contains i then gs := gs.push args[i]!
    else if ac.idxPos[i]!.isNone then
      unless ← liftMeta (isDefEq args[i]! ac.expected[i]!) do
        failT "UNSUPPORTED_FEATURE" s!"recursive call changes parameter {i}, which precedes the decreasing argument"
  if a.containsFVar ac.ih.fvarId! || a.containsFVar ac.f || a.hasExprMVar then
    failT "UNSUPPORTED_FEATURE" "accessibility lowering: nested recursive call in the decreasing argument"
  let pr ← liftMeta (accPairOf ac.hasIdx ac.nparams ac.idxTy ac.fam ac.idxLvl a)
  -- the call's own context: every local introduced after Acc.rec's minor premise (let-bound
  -- locals are unfolded in the argument instead)
  let lctx ← getLCtx
  let ctx := lctx.getFVars.filter fun v => !ac.base.contains v.fvarId! && !(lctx.get! v.fvarId!).isLet
  -- R's disjunct quantifies over the call's context; let-bound locals of that context are unfolded
  -- there (only there: the call itself keeps the source term)
  let unfoldLets (e : Expr) : Expr := Id.run do
    let mut e := e
    for _ in [0:lctx.numIndices] do
      let e' := e.replace fun x => match x with
        | .fvar id => match lctx.find? id with
          | some (.ldecl (value := v) ..) => some v
          | _ => none
        | _ => none
      if e' == e then break
      e := e'
    return e
  let prZ := unfoldLets pr
  let cTy ← liftMeta (inferType pr)
  let cLvl ← liftMeta (getLevel cTy)
  let c ← ac.counter.modifyGet fun n => (n, n + 1)
  let cert ← if ac.collect then do
      let d ← liftMeta <| withLocalDecl `y .default cTy fun y => do
        mkLambdaFVars #[y, ac.s] (← mkExistsFVars ctx (mkApp3 (mkConst ``Eq [cLvl]) cTy y prZ))
      if d.containsFVar ac.ih.fvarId! || d.containsFVar ac.f then
        failT "UNSUPPORTED_FEATURE" "accessibility lowering: a recursive call's context mentions the recursion"
      ac.dsRef.modify (·.push d)
      pure (mkSort .zero)                                    -- (first pass: the term is discarded)
    else do
      let some dc := ac.ds[c]? | failT "TRANSLATION_FAILED" "accessibility lowering: call sites differ between passes"
      let inst := ac.ds.toList.map fun d => d.beta #[pr, ac.s]
      let ex ← liftMeta (mkExistsIntro (dc.beta #[pr, ac.s]) ctx.toList (mkApp2 (mkConst ``Eq.refl [cLvl]) cTy pr))
      pure (mkDisjIntro inst c ex)
  return mkAppN ac.ih (#[pr, cert] ++ gs ++ args.extract (ac.nP + 1) args.size)

/-- `symm e : b = a` from `e : a = b`, with `Eq.rec` only. -/
def mkEqSymm (lvl : Level) (α a b e : Expr) : Expr :=
  let mot := Expr.lam `z α (Expr.lam `w (mkApp3 (mkConst ``Eq [lvl]) α a (.bvar 0)) (mkApp3 (mkConst ``Eq [lvl]) α (.bvar 1) a) .default) .default
  mkAppN (mkConst ``Eq.rec [.zero, lvl]) #[α, a, mot, mkApp2 (mkConst ``Eq.refl [lvl]) α a, b, e]

/-- Proof of `Acc R ⟨j, t⟩` for a term `t : I params j` evaluated at a constructor of the carrier
(the well-foundedness proof): a recursive field of that constructor (its induction hypothesis,
`rf`), a recursor application generalized over its major, indices and extra arguments and proved
branch by branch (into `Prop`), or a β/ζ/δ/ι step. Mirrors Rocq's guard condition. -/
partial def accCert (mkGoal : Expr → MetaM Expr) (t : Expr) (rf : Array (Expr × Expr)) : TransM Expr := do
  let t := t.headBeta.consumeMData
  if let some (_, ih) := rf.find? (·.1 == t) then return ih
  match t with
  | .letE _ _ v b _ => return ← accCert mkGoal (b.instantiate1 v) rf
  | _ => pure ()
  let t' ← liftMeta (whnfCore t)
  if t' != t then return ← accCert mkGoal t' rf
  let fn := t.getAppFn
  if let .const c ls := fn then
    match (← getEnv).find? c with
    | some (.recInfo rv) =>
      let args := t.getAppArgs
      let np := rv.numParams; let nm := rv.numMinors; let ni := rv.numIndices
      let base := np + 1 + nm + ni + 1
      unless args.size ≥ base do failT "UNSUPPORTED_FEATURE" "accessibility lowering: partial recursor application"
      let ps := args.extract 0 np
      let mot := args[np]!
      let mins := args.extract (np + 1) (np + 1 + nm)
      let idxs := args.extract (np + 1 + nm) (np + 1 + nm + ni)
      let maj := args[base - 1]!
      let extras := args.extract base args.size
      let indLvlCount := (← liftMeta (getConstInfoInduct rv.getMajorInduct)).levelParams.length
      let large := rv.levelParams.length == indLvlCount + 1
      let lsNew := if large then Level.zero :: ls.tail else ls
      -- generalized motive λ idxs' z, ∀ extras', Acc R ⟨_, R.rec … idxs' z extras'⟩
      let newMot ← liftMeta <| forallBoundedTelescope (← inferType mot) (some (ni + 1)) fun iz _ => do
        forallBoundedTelescope (← whnf (mkAppN mot iz)) (some extras.size) fun ex' _ => do
          let t' := mkAppN (mkConst rv.name ls) (ps ++ #[mot] ++ mins ++ iz ++ ex')
          mkLambdaFVars iz (← mkForallFVars ex' (← mkGoal t'))
      let newRec := mkConst rv.name lsNew
      let mut ty ← liftMeta do instantiateForall (← inferType newRec) (ps.push newMot)
      let mut minors : Array Expr := #[]
      for k in [0:nm] do
        let .forallE _ minorTy rest _ ← liftMeta (whnf ty) | failT "TRANSLATION_FAILED" "certificate: missing minor"
        let nf := rv.rules[k]!.nfields
        let minor ← forallTelescopeReducing minorTy fun xs _ => do
          let fields := xs.extract 0 nf
          let mut nih := 0
          for q in [nf:xs.size] do
            if (← liftMeta (inferType xs[q]!)).getAppFn == newMot then nih := nih + 1 else break
          let ihs := xs.extract nf (nf + nih)
          let ex := xs.extract (nf + nih) xs.size
          let origIhs ← ihs.mapM fun h => do
            let a := (← liftMeta (inferType h)).getAppArgs
            pure (mkAppN (mkConst rv.name ls) (ps ++ #[mot] ++ mins ++ a))
          let tk := (mkAppN mins[k]! (fields ++ origIhs ++ ex)).headBeta
          let rfk := rf.map fun (r, ih) => match extras.findIdx? (· == r) with
            | some q => (ex[q]!, ih) | none => (r, ih)
          let cert ← accCert mkGoal tk rfk
          liftMeta (mkLambdaFVars xs cert)
        minors := minors.push minor
        ty := rest.instantiate1 minor
      return mkAppN newRec (ps ++ #[newMot] ++ minors ++ idxs ++ #[maj] ++ extras)
    | some ci =>
      if let some v := ci.value? (allowOpaque := true) then
        return ← accCert mkGoal ((v.instantiateLevelParams ci.levelParams ls).beta t.getAppArgs) rf
    | none => pure ()
  failT "UNSUPPORTED_FEATURE"
    s!"accessibility lowering: a recursive call's argument is not a structural subterm ({fn.constName?.getD `_})"


/-- Eliminate `h : ∃ x₁ … xₙ, y = PR` (a call site's disjunct at a constructor of the carrier) into
`Acc R y`: the witnesses are the call's context, and `Acc R PR` is `accCert` of the call's argument. -/
partial def accElimExists (C : Expr) (cLvl : Level) (R y : Expr) (hasIdx : Bool)
    (pairOf : Expr → MetaM Expr) (rf : Array (Expr × Expr)) (E h : Expr) : TransM Expr := do
  let goal := mkApp3 (mkConst ``Acc [cLvl]) C R y
  let E ← liftMeta (whnfR E)
  if E.isAppOfArity ``Exists 2 then
    let α := E.getArg! 0
    let p := E.getArg! 1
    let lvl := E.getAppFn.constLevels!
    let minor ← withLocalDecl `w .default α fun w => do
      let pw := p.beta #[w]
      withLocalDecl `hw .default pw fun hw => do
        liftMeta (mkLambdaFVars #[w, hw] (← accElimExists C cLvl R y hasIdx pairOf rf pw hw))
    return mkAppN (mkConst ``Exists.rec lvl) #[α, p, .lam `_ E goal .default, minor, h]
  if E.isAppOfArity ``Eq 3 then
    let PR := E.getArg! 2
    let a := if hasIdx then (if PR.isAppOfArity ``PSigma.mk 4 then PR.getArg! 3 else .proj ``PSigma 1 PR) else PR
    let accP ← accCert (fun t => do pure (mkApp3 (mkConst ``Acc [cLvl]) C R (← pairOf t))) a rf
    let mot := Expr.lam `z C (Expr.lam `w (mkApp3 (mkConst ``Eq [cLvl]) C PR (.bvar 0))
      (mkApp3 (mkConst ``Acc [cLvl]) C R (.bvar 1)) .default) .default
    return mkAppN (mkConst ``Eq.rec [.zero, cLvl]) #[C, PR, mot, accP, y, mkEqSymm cLvl C y PR h]
  failT "TRANSLATION_FAILED" "accessibility lowering: unexpected shape of a call site's disjunct"

/-- Eliminate `hy : D_i y sk ∨ … ∨ D_n y sk` into `Acc R y`. -/
partial def accElimDisj (C : Expr) (cLvl : Level) (R y sk : Expr) (hasIdx : Bool) (pairOf : Expr → MetaM Expr)
    (rf : Array (Expr × Expr)) (ds : Array Expr) (i : Nat) (hy : Expr) : TransM Expr := do
  let goal := mkApp3 (mkConst ``Acc [cLvl]) C R y
  let Di := ds[i]!.beta #[y, sk]
  if i + 1 == ds.size then return ← accElimExists C cLvl R y hasIdx pairOf rf Di hy
  let rest := mkDisj ((ds.toList.drop (i + 1)).map fun d => d.beta #[y, sk])
  let l ← withLocalDecl `ha .default Di fun ha => do
    liftMeta (mkLambdaFVars #[ha] (← accElimExists C cLvl R y hasIdx pairOf rf Di ha))
  let r ← withLocalDecl `hb .default rest fun hb => do
    liftMeta (mkLambdaFVars #[hb] (← accElimDisj C cLvl R y sk hasIdx pairOf rf ds (i + 1) hb))
  return mkAppN (mkConst ``Or.rec) #[Di, rest, .lam `_ (mkApp2 (mkConst ``Or) Di rest) goal .default, l, r, hy]

/-- `wf : ∀ s : C, Acc R s`, by `I.rec` into `Prop`: at each constructor `C_k fields` of the carrier,
`Acc.intro`, and every `y` related to it is a call argument evaluated there (`accElimDisj`). -/
def accWf (iname : Name) (indLvls : List Level) (rv : RecursorVal) (params : Array Expr) (hasIdx : Bool)
    (idxTy : Expr) (idxLvl : Level) (fam C : Expr) (cLvl : Level) (R : Expr) (ds : Array Expr) : TransM Expr := do
  let np := rv.numParams; let ni := rv.numIndices
  let mk := accMk hasIdx idxTy fam idxLvl
  let pairOf := accPairOf hasIdx np idxTy fam idxLvl
  let recC := mkConst (iname.str "rec") indLvls
  let ty0 ← liftMeta do instantiateForall (← inferType recC) params
  let .forallE _ motTy _ _ := ty0 | failT "TRANSLATION_FAILED" s!"unexpected type of {iname}.rec"
  let motive ← liftMeta <| forallBoundedTelescope motTy (some (ni + 1)) fun xs _ => do
    let z := if hasIdx then mk xs[0]! xs[ni]! else xs[ni]!
    mkLambdaFVars xs (mkApp3 (mkConst ``Acc [cLvl]) C R z)
  let mut ty ← liftMeta do instantiateForall (← inferType recC) (params.push motive)
  let mut minors : Array Expr := #[]
  for k in [0:rv.numMinors] do
    let .forallE _ minorTy rest _ ← liftMeta (whnf ty) | failT "TRANSLATION_FAILED" s!"{iname}.rec: missing minor {k}"
    let nf := rv.rules[k]!.nfields
    let minor ← forallTelescopeReducing minorTy fun xs _ => do
      let fields := xs.extract 0 nf
      let ihs := xs.extract nf xs.size
      let mut rf : Array (Expr × Expr) := #[]
      let mut q := 0
      for fl in fields do
        let fty ← liftMeta do whnf (← inferType fl)
        if fty.getAppFn.isConstOf iname then
          if h : q < ihs.size then
            rf := rf.push (fl, ihs[q])
            q := q + 1
      let ctorApp := mkAppN (mkConst rv.rules[k]!.ctor indLvls) (params ++ fields)
      let cIdx := (← liftMeta do whnf (← inferType ctorApp)).getAppArgs.extract np (np + ni)
      let sk := if hasIdx then mk cIdx[0]! ctorApp else ctorApp
      let pf ← withLocalDecl `y .default C fun y => do
        withLocalDecl `hy .default (mkApp2 R y sk) fun hy => do
          let body ← accElimDisj C cLvl R y sk hasIdx pairOf rf ds 0 hy
          liftMeta (mkLambdaFVars #[y, hy] body)
      liftMeta (mkLambdaFVars xs (mkAppN (mkConst ``Acc.intro [cLvl]) #[C, R, sk, pf]))
    minors := minors.push minor
    ty := rest.instantiate1 minor
  liftMeta <| withLocalDecl `s .default C fun s => do
    let (ixs, mj) := if hasIdx then (#[Expr.proj ``PSigma 0 s], Expr.proj ``PSigma 1 s) else (#[], s)
    mkLambdaFVars #[s] (mkAppN recC (params ++ #[motive] ++ minors ++ ixs ++ #[mj]))

/-- Open the binders of a fixpoint type `fty` at the values of `Acc.rec`'s minor premise: index
positions ↦ `fst s`, generalized positions ↦ fresh locals, other leading positions ↦ `P`, the
decreasing position ↦ `snd s`, trailing positions ↦ fresh locals. -/
partial def accWalk {α} (fty : Expr) (n rarg : Nat) (P : Array Expr) (idxPos : Array (Option Nat)) (gpos : Array Nat)
    (fstS sndS : Expr) (i : Nat) (vals fresh : Array Expr) (k : Array Expr → Array Expr → Expr → TransM α) : TransM α := do
  if i == n then return ← k vals fresh fty
  let fty ← if fty.isForall then pure fty else liftMeta (whnf fty)
  let .forallE nm d bd bi := fty | failT "TRANSLATION_FAILED" "accessibility lowering: fixpoint type has too few binders"
  let go (v : Expr) (fresh : Array Expr) := accWalk (bd.instantiate1 v) n rarg P idxPos gpos fstS sndS (i + 1) (vals.push v) fresh k
  if i < rarg then
    if idxPos[i]!.isSome then go fstS fresh
    else if gpos.contains i then withLocalDecl nm bi d fun g => go g (fresh.push g)
    else go P[i]! fresh
  else if i == rarg then go sndS fresh
  else withLocalDecl nm bi d fun q => go q (fresh.push q)

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
    -- M6: a recursive call of an accessibility-lowered fixpoint
    if let .rel i := f then
      if let some ac := (← read).accSite then
        let ls := (← read).locals
        if i < ls.size && ls[ls.size - 1 - i]!.isFVarOf ac.f then
          return ← accCallSite ac args'
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
  if tgt.nonUniform > 0 then
    return ← transCaseNU tgt ind npar puinst pparams pctx pret scrut brs
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

/-- M6: a `match` on an inductive with one non-uniform parameter `u` (a Lean index). Rocq's case
binds `u` as a parameter: every branch is typed at `u`. Lean's recursor generalizes the index, so
the match is lowered with a convoy equation (only `Eq.rec`):

    I.rec P (λ i' idx h, ∀ e : i' = u, RET[idx, a0 := cast h e]) minors u idx x (Eq.refl u)
    minor_k = λ i' fs' ihs e,
      (Eq.rec (motive := λ y _, ∀ fs : FT y, motive y (idx_k y fs) (C P y fs)) (λ fs e₀, B fs) i' (symm e)) fs' e

where `cast h e = Eq.rec (motive := λ y _, I P y idx) h u e` and `symm e = Eq.rec (motive :=
λ y _, y = u) (Eq.refl u) i' e`... (built with `u` on the left: `e : u = i'`, see below). `B fs` is
the source branch at `u`; it has the expected type because `cast (C P u fs) e₀` reduces to
`C P u fs` for `e₀ : u = u` (Lean's K-like reduction of `Eq`). Each constructor must conclude with
the non-uniform parameter as its own variable (Rocq's parameter discipline). -/
partial def transCaseNU (tgt : IndTarget) (ind : IndRef) (npar : Nat) (puinst : Array IR.Level)
    (pparams : Array IR.Term) (pctx : Array AName) (pret : IR.Term) (scrut : IR.Term)
    (brs : Array (Array AName × IR.Term)) : TransM Expr := do
  let iname := tgt.types[ind.idx]!
  let rv ← recursorOf iname
  let k := tgt.nonUniform
  unless k == 1 do failT "UNSUPPORTED_FEATURE" s!"match on an inductive with {k} non-uniform parameters"
  let nu := npar - k
  unless rv.numParams == nu && pparams.size == npar do
    failT "EXPORT_VALIDATION_FAILED" s!"case has {pparams.size} parameters, {iname}.rec expects {rv.numParams} + {k} non-uniform"
  let nridx := pctx.size - 1                      -- Rocq indices
  unless rv.numIndices == k + nridx && brs.size == rv.numMinors do
    failT "EXPORT_VALIDATION_FAILED" s!"case shape differs from {iname}.rec"
  let params ← (pparams.extract 0 nu).mapIdxM fun j a => withPath s!"param{j}" (trans a)
  let u ← withPath s!"param{nu}" (trans pparams[nu]!)
  let scrut' ← withPath "scrutinee" (trans scrut)
  let sty ← liftMeta do whnf (← instLevelMVars (← inferType scrut'))
  unless sty.getAppFn.isConstOf iname && sty.getAppNumArgs == nu + k + nridx do
    failT "TRANSLATION_FAILED" s!"scrutinee type is not an application of {iname}"
  let indLvls := sty.getAppFn.constLevels!
  let sargs := sty.getAppArgs
  let idx := sargs.extract (nu + k) sargs.size
  let U ← liftMeta do inferType u
  let uLvl ← liftMeta do getLevel U
  -- the sort level of the inductive (the cast's motive)
  let iLvl ← liftMeta do getLevel sty
  let eqTy (a b : Expr) := mkApp3 (mkConst ``Eq [uLvl]) U a b
  -- e : u = i'  (u on the left, so that eliminating e substitutes i' := u in the branches)
  -- cast (h : I P i' idx) (e : u = i') : I P u idx  :=  Eq.rec (λ y _, I P y idx → I P u idx)? — we
  -- transport *back* along e: via symm e : i' = u, built as Eq.rec (λ y _, y = u) (refl u) i' e.
  let symmOf (i' e : Expr) : Expr :=
    mkAppN (mkConst ``Eq.rec [0, uLvl]) #[U, u, Expr.lam `y U (Expr.lam `w (eqTy u (.bvar 0)) (eqTy (.bvar 1) u) .default) .default,
      mkApp2 (mkConst ``Eq.refl [uLvl]) U u, i', e]
  let castOf (i' : Expr) (idxv : Array Expr) (h e : Expr) : MetaM Expr := do
    -- Eq.rec {a := i'} (λ y _, I P y idx) h {b := u} (symm e)
    let mot := Expr.lam `y U (Expr.lam `w (eqTy i' (.bvar 0)) (mkAppN (mkConst iname indLvls) (params ++ #[.bvar 1] ++ idxv)) .default) .default
    return mkAppN (mkConst ``Eq.rec [iLvl, uLvl]) #[U, i', mot, h, u, symmOf i' e]
  let large := rv.levelParams.length == indLvls.length + 1
  -- motive' (built in the recursor's motive telescope: i', idx, h)
  let ty0 ← liftMeta do instantiateForall (← inferType (mkConst (iname.str "rec") (if large then Level.zero :: indLvls else indLvls))) params
  let .forallE _ motiveTy _ _ := ty0 | failT "TRANSLATION_FAILED" s!"unexpected type of {iname}.rec"
  let (motive, v) ← forallTelescopeReducing motiveTy fun xs _ => do
    unless xs.size == 1 + nridx + 1 do failT "TRANSLATION_FAILED" "motive arity differs from the case context"
    let i' := xs[0]!
    let idxv := xs.extract 1 (1 + nridx)
    let h := xs[xs.size - 1]!
    withLocalDecl `e .default (eqTy u i') fun e => do
      let a0 ← liftMeta (castOf i' idxv h e)
      let ret ← withPath "return" (withReader (fun c => { c with locals := c.locals ++ idxv ++ #[a0] }) (trans pret))
      let body ← bindFVars false #[e] ret
      let v ← liftMeta do instantiateLevelMVars (← getLevel body)
      return (← bindFVars true xs body, v.normalize)
  if !large && v != Level.zero then
    failT "UNSUPPORTED_FEATURE" s!"elimination of {iname} into a non-Prop sort is not available in Lean"
  let recConst := mkConst (iname.str "rec") (if large then v :: indLvls else indLvls)
  let mut ty ← liftMeta do instantiateForall (← inferType recConst) (params.push motive)
  let mut minors : Array Expr := #[]
  for kk in [0:rv.numMinors] do
    let .forallE _ minorTy rest _ ← liftMeta (whnf ty) | failT "TRANSLATION_FAILED" s!"{iname}.rec: missing minor {kk}"
    let (bctx, bbody) := brs[kk]!
    let nfields := rv.rules[kk]!.nfields                 -- k + Rocq fields
    unless bctx.size + k == nfields do
      failT "UNSUPPORTED_FEATURE" s!"branch {kk}: {bctx.size} binders for {nfields - k} fields (let-bound constructor arguments)"
    let ctorC := mkConst tgt.ctors[ind.idx]![kk]! indLvls
    let minor ← minorTelescope minorTy nfields iname params fun fields _ ihs _ => do
      let i' := fields[0]!
      -- Rocq's discipline: the constructor concludes at its own non-uniform variable
      let cty ← liftMeta do whnf (← inferType (mkAppN ctorC (params ++ fields)))
      unless cty.getAppArgs[nu]? == some i' do
        failT "UNSUPPORTED_FEATURE" s!"constructor {kk} does not conclude at its non-uniform parameter"
      withLocalDecl `e .default (eqTy u i') fun e => do
        -- motiveE := λ y w, ∀ fs : FT y, motive y (idx_k y fs) (C P y fs)
        let ctorTyAt (y : Expr) : MetaM Expr := do instantiateForall (← inferType ctorC) (params.push y)
        let motE ← withLocalDecl `y .default U fun y => withLocalDecl `w .default (eqTy u y) fun w => do
          let fty ← liftMeta (ctorTyAt y)
          let body ← liftMeta <| forallBoundedTelescope fty (some (nfields - k)) fun fs concl => do
            let concl ← whnf concl
            let idxk := concl.getAppArgs.extract (nu + k) concl.getAppArgs.size
            mkForallFVars fs (mkAppN motive (#[y] ++ idxk ++ #[mkAppN ctorC (params ++ #[y] ++ fs)]))
          bindFVars true #[y, w] body
        -- refl := λ fs e₀, B fs   (fields at u, the source branch translated there)
        let reflT ← liftMeta (ctorTyAt u)
        let reflE ← forallBoundedTelescope reflT (some (nfields - k)) fun fs _ => do
          withLocalDecl `e0 .default (eqTy u u) fun e0 => do
            let b ← withPath s!"branch{kk}" (withReader (fun c => { c with locals := c.locals ++ fs }) (trans bbody))
            bindFVars true (fs.push e0) b
        let motLvl ← liftMeta do
          withLocalDecl `y .default U fun y => withLocalDecl `w .default (eqTy u y) fun w => do
            getLevel (← whnf (mkApp2 motE y w))
        let elim := mkAppN (mkConst ``Eq.rec [motLvl.normalize, uLvl]) #[U, u, motE, reflE, i', e]
        let body := mkAppN elim (fields.extract 1 fields.size |>.push e)
        bindFVars true (fields ++ ihs ++ #[e]) body
    minors := minors.push minor
    ty := rest.instantiate1 minor
  return mkAppN recConst (params ++ #[motive] ++ minors ++ #[u] ++ idx ++ #[scrut', mkApp2 (mkConst ``Eq.refl [uLvl]) U u])

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
    | transFixAcc defs        -- M6: structural recursion on a proof, into data (else the same rejection)
  unless sj == lams.size - 1 - rarg do return ← transFixAcc defs
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
      -- M6: structural recursion on a proof into data: accessibility lowering
      return ← transFixAcc defs
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

/-- M6 accessibility lowering: a structurally recursive `fix` whose decreasing argument is a proof
(a `Prop` inductive without large elimination, e.g. MathComp `acc_nat`) and whose result is data.
Lean cannot eliminate such a proof into `Type`, so the fixpoint is lowered to `Acc.rec` over the
carrier `C = Σ' i, I params i` (or `I params`) and the call-graph relation of the body:

    λ as, Acc.rec (r := R) (λ s _, ∀ G Q, T[s]) (λ s h ih, λ G Q, body′) ⟨j, x⟩ (wf ⟨j, x⟩) G Q
    R y s := ∨_c ∃ ctx_c, y = ⟨j_c, a_c⟩        (one disjunct per recursive call site c)
    wf : ∀ s, Acc R s   by I.rec into Prop

`body′` is the source body with each recursive call `f … a_c …` replaced by `ih ⟨j_c, a_c⟩ ⟨ctx_c, rfl⟩
…`. The well-foundedness proof evaluates each call argument at every constructor of the carrier
and proves `Acc R` of it from the constructor's induction hypotheses (`accCert`): Rocq's guard
condition, replayed as a proof. `R`, `wf` and the certificates are propositions or proofs; the
computation is `body′` under `Acc.rec`, which unfolds exactly when the proof is a constructor. -/
partial def transFixAcc (defs : Array (AName × IR.Term × IR.Term × Nat)) : TransM Expr := do
  let notMatch : TransM Expr := failT "UNSUPPORTED_FEATURE" "fixpoint body is not a match on the decreasing argument"
  let (fname, fty, fbody, rarg) := defs[0]!
  let fty' ← withPath "type" (trans fty)
  let (lams, b) := peelLams fbody
  unless rarg < lams.size do return ← notMatch
  let outer := (← read).locals
  withLocalDecl (binderName fname) .default fty' fun fv => do
  withSourceLams lams (outer.push fv) 0 #[] fun as => do
    let P := as.extract 0 rarg
    let x := as[rarg]!
    let Q := as.extract (rarg + 1) as.size
    let xty ← liftMeta do whnf (← inferType x)
    let .const iname indLvls := xty.getAppFn | notMatch
    let some (.inductInfo iv) := (← getEnv).find? iname | notMatch
    let rv ← recursorOf iname
    let large := rv.levelParams.length == indLvls.length + 1
    let T ← liftMeta (instantiateForall fty' as)
    let Tl ← liftMeta do instantiateLevelMVars (← getLevel T)
    unless !large && Tl.normalize != .zero && (← liftMeta (isProp xty)) do return ← notMatch
    let xargs := xty.getAppArgs
    let params := xargs.extract 0 iv.numParams
    let idx := xargs.extract iv.numParams xargs.size
    unless idx.size ≤ 1 do failT "UNSUPPORTED_FEATURE" "accessibility lowering: decreasing argument with several indices"
    unless idx.all (P.contains ·) do
      failT "UNSUPPORTED_FEATURE" "indices of the decreasing argument are not distinct earlier parameters"
    let idxPos : Array (Option Nat) := P.map fun p => idx.findIdx? (· == p)
    let gpos := (changedParams fbody lams.size rarg 0).toArray.qsort (· < ·) |>.filter (idxPos[·]!.isNone)
    let G := gpos.map (P[·]!)
    for i in [0:rarg] do
      unless gpos.contains i do
        let t ← liftMeta do instantiateMVars (← inferType P[i]!)
        if G.any (t.containsFVar ·.fvarId!) then
          failT "UNSUPPORTED_FEATURE" s!"argument {i} depends on an argument that recursive calls change"
    if G.any (xty.containsFVar ·.fvarId!) then
      failT "UNSUPPORTED_FEATURE" "the decreasing argument's type depends on an argument that recursive calls change"
    -- carrier
    let hasIdx := idx.size == 1
    let (idxTy, idxLvl) ← if hasIdx then liftMeta (do let t ← inferType idx[0]!; pure (t, ← getLevel t))
      else pure (mkSort .zero, Level.zero)
    let fam ← if hasIdx then liftMeta (withLocalDecl `i .default idxTy fun i =>
        mkLambdaFVars #[i] (mkAppN (mkConst iname indLvls) (params.push i)))
      else pure (mkAppN (mkConst iname indLvls) params)
    let C := if hasIdx then mkApp2 (mkConst ``PSigma [idxLvl, .zero]) idxTy fam else fam
    let cLvl ← liftMeta (getLevel C)
    let mk := accMk hasIdx idxTy fam idxLvl
    let fstOf (s : Expr) : Expr := .proj ``PSigma 0 s
    let sndOf (s : Expr) : Expr := if hasIdx then .proj ``PSigma 1 s else s
    let pairOf := accPairOf hasIdx iv.numParams idxTy fam idxLvl
    let RTy := mkForall `y .default C (mkForall `s .default C (mkSort .zero))
    withLocalDecl `R .default RTy fun Rv => do
    let accTy (R s : Expr) := mkApp3 (mkConst ``Acc [cLvl]) C R s
    -- Acc.rec's minor premise  λ s h ih, λ G Q, body′ (two passes: collect the call sites' disjuncts,
    -- then translate with R known)
    let dsRef ← IO.mkRef (#[] : Array Expr)
    let minorWith (R : Expr) (collect : Bool) (ds : Array Expr) : TransM Expr := do
      let motive ← withLocalDecl `s .default C fun s => withLocalDecl `acc .default (accTy R s) fun acc =>
        accWalk fty' as.size rarg P idxPos gpos (fstOf s) (sndOf s) 0 #[] #[] fun _ fresh body => do
          bindFVars true #[s, acc] (← bindFVars false fresh body)
      withLocalDecl `s .default C fun s => do
        let hTy ← liftMeta <| withLocalDecl `y .default C fun y => do mkForallFVars #[y] (← mkArrow (mkApp2 R y s) (accTy R y))
        withLocalDecl `h .default hTy fun h => do
        let ihTy ← liftMeta <| withLocalDecl `y .default C fun y => withLocalDecl `hy .default (mkApp2 R y s) fun hy =>
          mkForallFVars #[y, hy] (mkApp2 motive y (mkApp2 h y hy))
        withLocalDecl `ih .default ihTy fun ih => do
        let baseF := (← getLCtx).getFVarIds
        let counter ← IO.mkRef 0
        accWalk fty' as.size rarg P idxPos gpos (fstOf s) (sndOf s) 0 #[] #[] fun vals fresh _ => do
          let site : AccSite := { f := fv.fvarId!, s, ih, R, nP := rarg, idxPos, gpos, expected := vals,
                                  hasIdx, nparams := iv.numParams, idxTy, idxLvl, fam, base := baseF,
                                  collect, dsRef, ds, counter }
          let body ← withPath "body" (withReader (fun c => { c with locals := outer ++ #[fv] ++ vals, accSite := some site }) (trans b))
          bindFVars true #[s, h, ih] (← bindFVars true fresh body)
    let _ ← minorWith Rv true #[]
    let ds ← dsRef.get
    if ds.isEmpty then failT "UNSUPPORTED_FEATURE" "accessibility lowering: no recursive call"
    -- the call-graph relation  R y s := D₁ y s ∨ … ∨ Dₙ y s
    let Rdef ← liftMeta <| withLocalDecl `y .default C fun y => withLocalDecl `s .default C fun sv => do
      mkLambdaFVars #[y, sv] (mkDisj (ds.toList.map fun d => d.beta #[y, sv]))
    let intro ← minorWith Rdef false ds
    let motive ← withLocalDecl `s .default C fun s => withLocalDecl `acc .default (accTy Rdef s) fun acc =>
      accWalk fty' as.size rarg P idxPos gpos (fstOf s) (sndOf s) 0 #[] #[] fun _ fresh body => do
        bindFVars true #[s, acc] (← bindFVars false fresh body)
    let uM ← liftMeta do
      withLocalDecl `s .default C fun s => withLocalDecl `acc .default (accTy Rdef s) fun acc => do
        pure (← getLevel (← whnf (mkApp2 motive s acc))).normalize
    -- well-foundedness  wf : ∀ s, Acc R s   by I.rec into Prop
    let wf ← accWf iname indLvls rv params hasIdx idxTy idxLvl fam C cLvl Rdef ds
    let major := if hasIdx then mk idx[0]! x else x
    let accRec := mkAppN (mkConst ``Acc.rec [uM, cLvl]) #[C, Rdef, motive, intro, major, mkApp wf major]
    let res := eraseBinderScopes (← bindFVars true as (mkAppN accRec (G ++ Q)))
    if res.containsFVar fv.fvarId! || res.containsFVar Rv.fvarId! then
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
  -- binder names without macro scopes (hygienic names inherited from Lean's own declarations, e.g.
  -- the recursor types' `a✝`, do not survive the report's string round trip; names carry no meaning)
  let e := eraseBinderScopes (← instLevelMVars (← trans t))
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

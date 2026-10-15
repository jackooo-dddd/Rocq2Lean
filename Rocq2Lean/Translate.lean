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
  /-- Statement mode: a pending validation artifact (`RocqPending.*`) whose first parameters are
  hypotheses for these unproved leaves (in order). -/
  pendingHyps : Array String := #[]
  deriving Inhabited, Repr

structure GEnv where
  consts : Std.HashMap String Name := {}
  /-- Number of universe parameters of each accepted constant (generalized global levels). -/
  constLevels : Std.HashMap String Nat := {}
  /-- Source global level of each universe parameter of each accepted constant, by target name. -/
  constGlobals : Std.HashMap Name (Array String) := {}
  /-- R3G-F (docs/RESULT_SORT_LEVELS.md): for an accepted inductive type (by target name), the source
  levels that occur in its declaration only in its result sort (and its own R3G-F implicit levels). -/
  resultOnly : Std.HashMap Name (Array String) := {}
  /-- R3G-F: for each translated source declaration, the result-sort implicit levels of the blocks in its
  dependency closure (itself included). A declaration reads these minimally where they are implicit;
  the set depends only on the declaration's own dependencies, never on unrelated blocks. -/
  rsClosure : Std.HashMap String (Std.HashSet String) := {}
  /-- R-CARRIER P1 (docs/CARRIER_LEVELS.md): the parameter carrier levels of every exported block
  (`Split.carrierLevels`), computed once from the source; read minimally in every R2F reading. -/
  carrierSet : Std.HashSet String := {}
  /-- R-CARRIER P1 (narrowed): (carrier, other level of the same block) pairs (`Split.decoupledPairs`). -/
  decoupled : Std.HashSet (String × String) := {}
  /-- R-CARRIER P2: implicit levels with several free classes in a declaration's type are named per class. -/
  carrierSplit : Bool := true
  /-- R-CARRIER P2: per target, the universe-parameter positions that are copies (`l__c<k>`): an argument
  there stands for an argument `a ≤ l`, never for a shared `l` itself (R3 entailment, no coherence). -/
  copyPositions : Std.HashMap Name (Array Bool) := {}
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
  /-- M6: source bodies of the export's transparent monomorphic constants (δβ-inlining of a
  constant to which a fixpoint passes itself, `inlineRecArgs`). -/
  irBodies : Std.HashMap String IR.Term := {}
  /-- M6: transparent monomorphic constants with a `Set`-motive binder (`P : … → Set`), whose uses at
  a `Prop`-valued family (Rocq's `Prop ≤ Set`) can only be translated through their body. -/
  setMotive : Std.HashSet String := {}
  /-- Entry 14: erasing polymorphic definitions (`erasingPolyBody?`) and their bodies. -/
  erasingPoly : Std.HashMap String IR.Term := {}
  /-- Rule Q-a (docs/PHANTOM_SORT.md): phantom definitions (`phantomDefPairs?`) and their
  (sort parameter, value parameter) index pairs. -/
  phantomDefs : Std.HashMap String (Array (Nat × Nat)) := {}
  /-- Rule Q-a: the phantom definitions that are proofs of phantom checks (HB's `id_phant`). -/
  phantomProofs : Std.HashSet String := {}
  /-- Rule P gate (speed, exact): source declarations whose dependency closure reaches a definition
  translated with a lifted value, and their target names (with `PULift`): a lifted type can only arise by
  unfolding one of them, so only terms mentioning one can need a coercion. -/
  liftReach : Std.HashSet String := {}
  liftTargets : Std.HashSet Name := {}
  /-- Timing (entry 14): the attempts of the declaration being translated (tier label, ms, status). -/
  tierLog : Option (IO.Ref (Array (String × Nat × String))) := none
  /-- P0: protected public interface (pinned Prosa/Classic inventory, bound in the export contract):
  these declarations keep their full source statement — no R2B-S result-sort lowering and no R2B-P
  specialization of a statement level — whether they are requested roots or dependencies. -/
  protectedNames : Std.HashSet String := {}
  /-- Statement mode: constants available only as statements (theorems, extracted obligations, opaque
  data: their proof or value is a task for the Lean proving agent): source key ↦ (statement constant,
  the hypotheses of that constant when it is itself a pending artifact, as leaf keys). -/
  leafStmt : Std.HashMap String (Name × Array String) := {}
  /-- Rule H: the targets of `leafStmt` (proof tasks' statements, the types of prerequisite hypotheses). -/
  leafStmtTargets : Std.HashSet Name := {}
  /-- Statement mode: definitions validated as pending artifacts (`RocqPending.*`, abstracted over the
  unproved prerequisites they need): source key ↦ (artifact, its hypotheses as leaf keys, in order). -/
  pendingDefs : Std.HashMap String (Name × Array String) := {}
  /-- Statement mode (the IR header's mode): enables the statement-mode-only rules (R3G pick on a
  level some of whose arguments are already determined expressions). -/
  stmtMode : Bool := false
  /-- Assembly (docs/ASSEMBLY.md): the validated statement library is imported; a declaration it
  already contains is matched against the imported one (identical, or rejected) instead of added. -/
  reuseExisting : Bool := false
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
  /-- B (termination lowering, `transFixWf`): a `match` whose branches contain a recursive call
  records the equation `scrutinee = C fields` in its branches (convoy), so that the call relation
  sees why the argument decreases. -/
  convoy : Bool := false
  /-- B: recursor binders introduced inside the lowered body that the source cannot see (the
  recursive results of a lowered match's minor premises); left out of the call contexts. -/
  hidden : Option (IO.Ref (Array FVarId)) := none

/-- M6 course-of-values recursion (`transFix` in `cov` mode): the fixpoint being lowered and the
known results `r_z : Motive' z` (`Motive' z = PProd (M z) (Below z)`) of its subterms `z`; a
`match` on such a `z` carries `r_z` into its branches (`transCaseCov`). -/
structure CovSite where
  f : FVarId
  iname : Name
  params : Array Expr
  motive : Expr
  results : Array (Expr × Expr)
  P : Array Expr
  idxPos : Array (Option Nat)
  gpos : Array Nat
  nparams : Nat

structure TCtx where
  genv : GEnv
  /-- M6 course-of-values recursion (see `CovSite`). -/
  cov : Option CovSite := none
  /-- M6: the accessibility-lowered fixpoint whose recursive calls are being translated. -/
  accSite : Option AccSite := none
  /-- M6 ι-generalized fix lowering: inside minor `k`, the decreasing argument is the constructor
  application `C_k fields`; a `match` whose scrutinee translates to exactly that application is
  ι-reduced to its branch `k` (with the branch's fields := `fields`). Entries: (C_k fields, k, fields). -/
  iota : Array (Expr × Nat × Array Expr) := #[]
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
  /-- R3↓ (cumulativity tier): references take fresh level metavariables even for levels shared with
  the declaration, so Lean's unifier instantiates them at their arguments' levels (`PolC.{0} Z` where
  Rocq uses `PolC@{l} Z` with `Z : Set ≤ Type@{l}`); each argument is checked not to raise (R3). -/
  lowerShared : Bool := false
  /-- Coherence by unification (docs/COHERENCE_READINGS.md §6): references take a fresh level
  metavariable per occurrence for a level shared with the declaration, recorded here with its source
  level; after translation, every one left free is bound back to the declaration's own variable for it
  (`rebindShared`), so only typing (e.g. a referenced definition's R2F reading `max (u_l, …)`) gives an
  occurrence another argument. The obligations are then checked as on a plain tier (no lowering). -/
  sharedFresh : Option (IO.Ref (Array (LMVarId × String))) := none
  /-- `locals[k]` is the Lean value of the `k`-th enclosing source binder, outermost first;
  source `rel i` denotes `locals[locals.size - 1 - i]`. -/
  locals : Array Expr := #[]
  path : List String := []
  /-- Statement mode, pending validation: the hypothesis metavariables created for unproved
  prerequisites (synthetic opaque, never assigned by unification), with the leaf key each stands for;
  abstracted into binders before the kernel check. `none` outside pending validation. -/
  hyps : Option (IO.Ref (Array (MVarId × String))) := none
  /-- The source key of the declaration being translated (names translator-generated leaves). -/
  declKey : String := ""
  /-- P3 retry tier: a prerequisite hypothesis is reused only at a type equal *without* assigning any
  level metavariable (each other use gets its own hypothesis; duplicates are collapsed after solving). -/
  hypExact : Bool := false
  /-- Rule P, term level (docs/PROP_LIFT.md §3): where a cast or an application argument mismatches
  only by a lift, `PULift.up` / `PULift.down` is inserted (counted here; `none` outside rule P's tier). -/
  propCoerce : Option (IO.Ref Nat) := none
  /-- Rule Q-a: at an application of a phantom definition, a sort argument at a sort-parameter position
  is the type of the paired value argument (per occurrence). -/
  phantomLower : Bool := false

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

/-- Statement mode: the pending validation artifact of a declaration (never part of the accepted
library `Rocq.*`). -/
def pendingTargetName (key : String) : Name :=
  let comps := (key.splitOn "/").flatMap (·.splitOn ".")
  comps.foldl Name.str `RocqPending

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

/-- R3G-F: the result-sort implicit levels in the dependency closure of `deps` (source names). -/
def GEnv.rsOfDeps (genv : GEnv) (deps : Array String) : Std.HashSet String :=
  deps.foldl (fun acc d => ((genv.rsClosure[d]?).getD {}).fold (·.insert ·) acc) {}

/-- `a + k ≤ b` is entailed by the native facts (`Set` included): `k = 0` needs `≤`, `k = 1`
needs `<`, larger offsets need a chain of strict steps. -/
partial def entails (f : IR.UniverseFacts) (a b : String) (k : Nat) : Bool :=
  if k == 0 then a == b || f.rel a b == "le" || f.rel a b == "lt"
  else if k == 1 then f.rel a b == "lt"
  else if f.ltSucc.isEmpty && !f.relations.isEmpty then
    (("Set" :: f.levels.toList).any fun c => f.rel a c == "lt" && entails f c b (k - 1))
  -- the strict successors of `a` are exactly the `c` with `a < c` (indexed once per export)
  else (f.ltSucc.getD a #[]).any fun c => entails f c b (k - 1)

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
    | some l =>
      -- (an instance level stays the image of the source level: the audit requires exactly that; an
      -- erasing polymorphic definition is δβ-inlined instead, entry 14)
      pure l
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
  -- (coherence by unification first, also on the R3↓ tier: the occurrences are recorded and rebound)
  if let some ref := (← read).sharedFresh then
    return ← globals.toList.mapM fun l => do
      let v ← liftMeta mkFreshLevelMVar
      -- (every occurrence is recorded, own or not: a class whose lowest level is not an own level is
      -- left to R3G, `rebindShared`)
      if let .mvar m := v then ref.modify (·.push (m, l))
      pure v
  if (← read).lowerShared then return ← liftMeta do globals.toList.mapM fun _ => mkFreshLevelMVar
  globals.toList.mapM fun l => match own[l]? with
    | some v => pure v
    | none => liftMeta mkFreshLevelMVar

/-- Universe arguments of a reference to an accepted or pending target `n` (its source levels shared
with the referring declaration, otherwise fresh). -/
def levelsOf (n : Name) : TransM (List Level) := do
  match (← read).genv.constGlobals[n]? with
  | some gs => sharedOrFreshLevels gs
  | none => pure []

/-- Pending validation: the hypothesis standing for leaf `l` in the declaration being translated —
one shared hypothesis per leaf (a data leaf such as an opaque interface must be the same term
everywhere it occurs), created at its first use with type `d`. -/
def hypFor (ref : IO.Ref (Array (MVarId × String))) (l : String) (d : Expr) : TransM Expr := do
  -- P3 (ITERATION_LOG entry 8): one hypothesis per *instance* of a prerequisite — an existing
  -- hypothesis of the leaf is reused only at its own type (definitional equality, which may still
  -- unify free universe levels of the use with it); a prerequisite needed at another instance gets its
  -- own hypothesis `h_<leaf>__<k>`. A hypothesis is never reused at a different type.
  let same := (← ref.get).filter (·.2 == l)
  -- (same instance: the statement constant's universe arguments unify, then the arguments are
  -- definitionally equal; comparing different instances by `isDefEq` alone would unfold the statement)
  let sameInst (t : Expr) : MetaM Bool := do
    match t.getAppFn, d.getAppFn with
    | .const n1 us1, .const n2 us2 =>
      if n1 != n2 || us1.length != us2.length || t.getAppNumArgs != d.getAppNumArgs then return false
      let s ← saveState
      if (← (us1.zip us2).allM fun (a, b) => isLevelDefEq a b) &&
         (← (t.getAppArgs.zip d.getAppArgs).allM fun (x, y) => isDefEq x y) then return true
      s.restore
      return false
    | _, _ => isDefEq t d
  let exact := (← read).hypExact
  for (m, _) in same do
    let t ← m.getType
    if ← liftMeta (if exact then withNewMCtxDepth (isDefEq t d) else sameInst t) then return mkMVar m
  -- (a prerequisite with hypotheses of its own is applied to the hypotheses of its prerequisites at
  -- this instance, resolved the same way; the audit checks each binder's structure)
  -- a deterministic binder name (the artifact's hypothesis binders are abstracted from these
  -- metavariables; a hygienic name would differ between the declaration and its residual record)
  let base := "h_" ++ l.map fun ch => if ch == '.' || ch == '/' then '_' else ch
  let nm := if same.isEmpty then base else s!"{base}__{same.size + 1}"
  -- (a hypothesis is a closed proposition: it is created outside every local scope of the translation,
  -- so abstracting a scope — an accessibility lowering's call context, `div.gcdn` — never drags the
  -- scope's locals into it through the metavariable's context)
  let m ← liftMeta (if d.hasFVar then mkFreshExprMVar (some d) .syntheticOpaque (Name.mkSimple nm)
    else withLCtx {} {} (mkFreshExprMVar (some d) .syntheticOpaque (Name.mkSimple nm)))
  ref.modify (·.push (m.mvarId!, l))
  pure m

/-- Pending validation: apply a pending artifact `e` to the hypotheses of the leaves of its telescope
(shared per leaf; registered in `ref` with their leaf keys). -/
def applyHyps (ref : IO.Ref (Array (MVarId × String))) (e : Expr) (leaves : Array String) : TransM Expr := do
  let mut e := e
  let mut t ← liftMeta (inferType e)
  for l in leaves do
    t ← liftMeta (whnfD t)
    match t with
    | .forallE _ d b _ =>
      let m ← hypFor ref l d
      e := mkApp e m
      t := b.instantiate1 m
    | _ => failT "TRANSLATION_FAILED" "pending artifact has fewer hypotheses than recorded"
  return e

/-- Statement mode: a reference to (a type or constructor of) a pending inductive applied to its
leading hypothesis parameters (the shared hypotheses of the declaration being translated). -/
def pendingIndArgs (t : IndTarget) (e : Expr) : TransM Expr := do
  if t.pendingHyps.isEmpty then return e
  match (← read).hyps with
  | some ref => applyHyps ref e t.pendingHyps
  | none => failT "TRANSLATION_FAILED" "reference to a pending inductive outside pending validation"

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

def recursorOf (iname : Name) (nested : Bool := false) : TransM RecursorVal := do
  match (← getEnv).find? (iname.str "rec") with
  | some (.recInfo rv) =>
    -- M6: a nested (single-type) inductive only where the caller supplies trivial auxiliary
    -- motives and minors (`auxMotives`, `auxMinors`)
    let isNested := match (← getEnv).find? iname with
      | some (.inductInfo iv) => iv.isNested && iv.all.length == 1
      | _ => false
    unless rv.numMotives == 1 || (nested && isNested) do
      failT "UNSUPPORTED_FEATURE" s!"elimination of a mutual or nested inductive ({iname})"
    return rv
  | _ => failT "TRANSLATION_FAILED" s!"no recursor {iname}.rec in the target environment"

/-- Number of minor premises of `iname.rec` for `iname`'s own constructors (the first ones). -/
def mainMinors (iname : Name) : TransM Nat := do
  match (← getEnv).find? iname with
  | some (.inductInfo iv) => return iv.ctors.length
  | _ => failT "TRANSLATION_FAILED" s!"{iname} is not an inductive type"

/-- M6 nested inductives with trivial auxiliary eliminations: after the main motive, Lean's recursor
of a nested inductive takes one motive per auxiliary type (`List ZArithProof`), and after the main
minors one minor per auxiliary constructor. When no recursion goes through the nesting they are
`λ …, PUnit` and `λ …, PUnit.unit` (at the motive's level). Consumed from `ty`. -/
def auxMotives (rv : RecursorVal) (lvl : Level) (ty : Expr) : MetaM (Array Expr × Expr) := do
  let mut ty := ty
  let mut ms : Array Expr := #[]
  for _ in [1:rv.numMotives] do
    let .forallE _ mTy rest _ ← whnf ty | throwError "nested recursor: missing auxiliary motive"
    let m ← forallTelescopeReducing mTy fun xs _ => mkLambdaFVars xs (mkConst ``PUnit [lvl])
    ms := ms.push m
    ty := rest.instantiate1 m
  return (ms, ty)

def auxMinors (n : Nat) (lvl : Level) (ty : Expr) : MetaM (Array Expr) := do
  let mut ty := ty
  let mut ms : Array Expr := #[]
  for _ in [0:n] do
    let .forallE _ mTy rest _ ← whnf ty | throwError "nested recursor: missing auxiliary minor"
    let m ← forallTelescopeReducing mTy fun xs _ => mkLambdaFVars xs (mkConst ``PUnit.unit [lvl])
    ms := ms.push m
    ty := rest.instantiate1 m
  return ms

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
    -- M6: a functional recursive field `y : ∀ zs, I params idx` (Acc's `∀ y, R y x → Acc y`) has the
    -- recursive result `ih : ∀ zs, motive idx (y zs)`
    let mut recFields := #[]
    for y in fields do
      let yt ← liftMeta do inferType y
      let functional ← liftMeta do forallTelescopeReducing yt fun zs body => do
        return !zs.isEmpty && (← isRec body)
      -- M6 nested inductive: a field of an auxiliary type (`List I`) also has a recursive result
      let nestedField ← liftMeta do
        let some (.inductInfo iv) := (← getEnv).find? iname | return false
        return iv.isNested && ((← instantiateMVars yt).find? (·.isConstOf iname)).isSome
      if functional || nestedField || (← liftMeta (isRec yt)) then recFields := recFields.push y
    forallBoundedTelescope rest (some recFields.size) fun ihs res => do
      unless ihs.size == recFields.size do failT "TRANSLATION_FAILED" "minor premise has too few recursive results"
      k fields recFields ihs res

/-- Positions `i < r` of a fixpoint's leading arguments that some recursive call changes, read
from the source syntax: `depth` counts the binders between the fix binder and `t`, so the function
is `rel depth` and the i-th leading lambda is `rel (depth - 1 - i)` (once `depth ≥ nl`). In a
mutual block of `nfun` functions, a call to any of them (`rel depth` … `rel (depth + nfun - 1)`) counts. -/
partial def changedParams (t : IR.Term) (nl r depth : Nat) (acc : Std.HashSet Nat := {}) (nfun : Nat := 1) :
    Std.HashSet Nat :=
  let go (u : IR.Term) (d : Nat) (a : Std.HashSet Nat) := changedParams u nl r (depth + d) a nfun
  match t with
  | .app f args =>
    let acc := match f with
      | .rel j =>
        if depth ≤ j && j < depth + nfun && depth ≥ nl then
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


/-! ## M6: IR substitution (δβ-inlining of higher-order recursive uses) -/

/-- Map the free `rel`s of an IR term: `f i k` for `rel i` with `i ≥ k` (`k` binders above). -/
partial def IR.Term.mapRels (f : Nat → Nat → IR.Term) (t : IR.Term) (k : Nat := 0) : IR.Term :=
  let go (u : IR.Term) (d : Nat) := u.mapRels f (k + d)
  match t with
  | .rel i => if i ≥ k then f i k else t
  | .evar ev args => .evar ev (args.map (go · 0))
  | .cast c kd ty => .cast (go c 0) kd (go ty 0)
  | .prod n ty b => .prod n (go ty 0) (go b 1)
  | .lam n ty b => .lam n (go ty 0) (go b 1)
  | .letIn n v ty b => .letIn n (go v 0) (go ty 0) (go b 1)
  | .app f args => .app (go f 0) (args.map (go · 0))
  | .case i np r pu ps pctx ret c brs =>
    .case i np r pu (ps.map (go · 0)) pctx (go ret pctx.size) (go c 0) (brs.map fun (ctx, b) => (ctx, go b ctx.size))
  | .proj i np a c => .proj i np a (go c 0)
  | .fix ds idx => .fix (ds.map fun (n, ty, b, r) => (n, go ty 0, go b ds.size, r)) idx
  | .cofix ds idx => .cofix (ds.map fun (n, ty, b, r) => (n, go ty 0, go b ds.size, r)) idx
  | _ => t

def IR.Term.liftRels (n : Nat) (t : IR.Term) : IR.Term := if n == 0 then t else t.mapRels fun i _ => .rel (i + n)

/-- `b[rel 0 := v]` for `b` under one binder (`v` in the context outside it). -/
def IR.Term.subst0 (b v : IR.Term) : IR.Term :=
  b.mapRels fun i k => if i == k then v.liftRels k else .rel (i - 1)

/-- Does `t` mention a free `rel` in `[lo, lo + n)` (counted at its top)? -/
partial def IR.Term.mentionsRels (t : IR.Term) (lo n : Nat) : Bool :=
  let go (u : IR.Term) (d : Nat) := u.mentionsRels (lo + d) n
  match t with
  | .rel i => lo ≤ i && i < lo + n
  | .evar _ args => args.any (go · 0)
  | .cast c _ ty => go c 0 || go ty 0
  | .prod _ ty b | .lam _ ty b => go ty 0 || go b 1
  | .letIn _ v ty b => go v 0 || go ty 0 || go b 1
  | .app f args => go f 0 || args.any (go · 0)
  | .case _ _ _ _ ps pctx ret c brs =>
    ps.any (go · 0) || go ret pctx.size || go c 0 || brs.any fun (ctx, b) => go b ctx.size
  | .proj _ _ _ c => go c 0
  | .fix ds _ | .cofix ds _ => ds.any fun (_, ty, b, _) => go ty 0 || go b ds.size
  | _ => false

/-- Does `t` use a function of a fixpoint block other than in a full call: `rel (lo + o)` bare, or
applied to fewer than `need[o]` arguments (`need[o]` = decreasing position + 1 of the function
bound at offset `o`; offset 0 is the block's last function)? -/
partial def IR.Term.partialRecUse (t : IR.Term) (lo : Nat) (need : Array Nat) : Bool :=
  let go (u : IR.Term) (d : Nat) := u.partialRecUse (lo + d) need
  let isFn (i : Nat) := lo ≤ i && i < lo + need.size
  match t with
  | .rel i => isFn i
  | .app (.rel i) args => (isFn i && args.size < need[i - lo]!) || args.any (go · 0)
  | .evar _ args => args.any (go · 0)
  | .cast c _ ty => go c 0 || go ty 0
  | .prod _ ty b | .lam _ ty b => go ty 0 || go b 1
  | .letIn _ v ty b => go v 0 || go ty 0 || go b 1
  | .app f args => go f 0 || args.any (go · 0)
  | .case _ _ _ _ ps pctx ret c brs =>
    ps.any (go · 0) || go ret pctx.size || go c 0 || brs.any fun (ctx, b) => go b ctx.size
  | .proj _ _ _ c => go c 0
  | .fix ds _ | .cofix ds _ => ds.any fun (_, ty, b, _) => go ty 0 || go b ds.size
  | _ => false

/-- Flatten nested applications `(f a) b ↦ f a b` (after substitution of an application for a head). -/
partial def IR.Term.flattenApps (t : IR.Term) : IR.Term :=
  let go (u : IR.Term) := u.flattenApps
  match t with
  | .app f args =>
    match go f with
    | .app g as => .app g (as ++ args.map go)
    | f' => .app f' (args.map go)
  | .evar ev args => .evar ev (args.map go)
  | .cast c kd ty => .cast (go c) kd (go ty)
  | .prod n ty b => .prod n (go ty) (go b)
  | .lam n ty b => .lam n (go ty) (go b)
  | .letIn n v ty b => .letIn n (go v) (go ty) (go b)
  | .case i np r pu ps pctx ret c brs =>
    .case i np r pu (ps.map go) pctx (go ret) (go c) (brs.map fun (ctx, b) => (ctx, go b))
  | .proj i np a c => .proj i np a (go c)
  | .fix ds idx => .fix (ds.map fun (n, ty, b, r) => (n, go ty, go b, r)) idx
  | .cofix ds idx => .cofix (ds.map fun (n, ty, b, r) => (n, go ty, go b, r)) idx
  | _ => t

/-- β-reduce `f args` as far as `f`'s leading lambdas go; the rest stay applied (flattened). -/
partial def IR.betaApp (f : IR.Term) (args : Array IR.Term) : IR.Term :=
  if h : 0 < args.size then
    match f with
    | .lam _ _ b => IR.betaApp (b.subst0 args[0]) (args.extract 1 args.size)
    | .app g as => .app g (as ++ args)
    | _ => .app f args
  else f

/-- Statement mode: ζ-normalization of a fixpoint body *before* any lowering (the audit's
`zeta_fix_lets`, same order): a `let` whose value mentions a function of the block (`rel` in
`[lo, lo + n)`) is inlined (definitional), so its uses become recursive calls, in every minor premise
alike (applying ζ per minor premise after ι-reduction kept such a `let` where ι removed the call). -/
partial def IR.Term.zetaFixLets (t : IR.Term) (lo n : Nat) : IR.Term :=
  let go (u : IR.Term) (d : Nat) := u.zetaFixLets (lo + d) n
  match t with
  | .letIn _ v _ b => if v.mentionsRels lo n then ((b.subst0 v).flattenApps).zetaFixLets lo n
      else match t with
        | .letIn nm v ty b => .letIn nm (go v 0) (go ty 0) (go b 1)
        | _ => t
  | .evar ev args => .evar ev (args.map (go · 0))
  | .cast c kd ty => .cast (go c 0) kd (go ty 0)
  | .prod nm ty b => .prod nm (go ty 0) (go b 1)
  | .lam nm ty b => .lam nm (go ty 0) (go b 1)
  | .app f args => .app (go f 0) (args.map (go · 0))
  | .case i np r pu ps pctx ret c brs =>
    .case i np r pu (ps.map (go · 0)) pctx (go ret pctx.size) (go c 0) (brs.map fun (ctx, b) => (ctx, go b ctx.size))
  | .proj i np a c => .proj i np a (go c 0)
  | .fix ds idx => .fix (ds.map fun (nm, ty, b, r) => (nm, go ty 0, go b ds.size, r)) idx
  | .cofix ds idx => .cofix (ds.map fun (nm, ty, b, r) => (nm, go ty 0, go b ds.size, r)) idx
  | _ => t

/-- A binder type `∀ xs, Set` with at least one argument (a `Set`-valued family). -/
partial def IR.Term.isSetFamily : IR.Term → Nat → Bool
  | .prod _ _ b, n => b.isSetFamily (n + 1)
  | .sort (.type u), n => n > 0 && u.size == 1 && u[0]!.level == .set && u[0]!.offset == 0
  | _, _ => false

/-- The source type `∀ …` has a binder of a `Set`-valued family (`well_founded_induction`'s `P`). -/
partial def IR.Term.hasSetMotive : IR.Term → Bool
  | .prod _ a b => a.isSetFamily 0 || b.hasSetMotive
  | _ => false

/-- Whether a source term mentions a universe variable (`var i`) in a sort or a universe instance. -/
partial def termHasUnivVar : IR.Term → Bool
  | .sort (.type u) => u.any fun e => (e.level matches .var _)
  | .const _ u | .ind _ u | .construct _ _ u => u.any fun x => (x matches .var _)
  | .cast t _ ty => termHasUnivVar t || termHasUnivVar ty
  | .prod _ a b | .lam _ a b => termHasUnivVar a || termHasUnivVar b
  | .letIn _ v t b => termHasUnivVar v || termHasUnivVar t || termHasUnivVar b
  | .app f as => termHasUnivVar f || as.any termHasUnivVar
  | .evar _ as => as.any termHasUnivVar
  | .case _ _ _ pu ps _ r c brs => pu.any (fun x => (x matches .var _)) || ps.any termHasUnivVar || termHasUnivVar r ||
      termHasUnivVar c || brs.any (termHasUnivVar ·.2)
  | .proj _ _ _ t => termHasUnivVar t
  | .fix defs _ | .cofix defs _ => defs.any fun (_, t, b, _) => termHasUnivVar t || termHasUnivVar b
  | _ => false

/-- δ-inlining of erasing polymorphic definitions (entry 14): a transparent universe-polymorphic
constant whose body, after its leading λs, mentions no universe variable (`reverse_coercion x' x := x'`).
Applied, its δβ-reduct is definitionally equal and carries none of the instance's levels. -/
def erasingPolyBody? (c : IR.ConstantDecl) : Option IR.Term := do
  unless c.bodyState == "transparent" do none
  unless (c.universes matches .polymorphic ..) do none
  let some b := c.body | none
  let rec peel : IR.Term → Nat → IR.Term × Nat
    | .lam _ _ t, n => peel t (n + 1)
    | t, n => (t, n)
  let (t, n) := peel b 0
  if n == 0 || termHasUnivVar t then none
  some b

/-- Rule T (docs/COINDUCTIVE.md): one body, and no constructor argument or index mentions the block.
The arguments are stored innermost first: `args[k]` lies under the block, the `npars` parameters and the
`args.size - 1 - k` earlier arguments; the indices under all arguments. -/
def nonRecursiveBlock (i : IR.InductiveDecl) : Bool :=
  i.bodies.size == 1 && i.bodies.all fun b => b.ctors.all fun c =>
    (Id.run do
      let mut ok := true
      for h : k in [0:c.args.size] do
        if c.args[k].type.mentionsRels (c.args.size - 1 - k + i.npars) i.bodies.size then ok := false
      return ok) &&
    c.indices.all fun x => !x.mentionsRels (c.args.size + i.npars) i.bodies.size

/-- Rule Q-a (docs/PHANTOM_SORT.md): a *phantom definition* is a transparent monomorphic constant whose
body, after its λs, is a chain of non-dependent products of `phantom X x` (Corelib's
`ssreflect_rw.phantom : ∀ T : Type, T → Prop`, one constructor without fields), each `X` a λ-bound
parameter whose type is a sort and `x` a λ-bound parameter of type `X` (HB's
`unify T1 T2 t1 t2 s := phantom T1 t1 → phantom T2 t2`). Returns the (sort, value) parameter pairs.
Every application of it is inhabited (by the constructors), whatever its sort arguments. -/
partial def phantomDefPairs? (c : IR.ConstantDecl) : Option (Array (Nat × Nat)) := do
  let .monomorphic := c.universes | none
  let isPh (t : IR.Term) : Bool := match t with
    | .app (.ind ⟨"Corelib.ssr.ssreflect_rw.phantom", 0⟩ _) _ => true
    | _ => false
  -- a phantom check (`unify`: the body after its λs), or a proof of one (`id_phant : ∀ T t, phantom T t →
  -- phantom T t`: the statement after its parameters)
  let rec peelL (t : IR.Term) (acc : Array IR.Term) : Array IR.Term × IR.Term :=
    match t with
    | .lam _ ty b => peelL b (acc.push ty)
    | t => (acc, t)
  let rec peelP (t : IR.Term) (acc : Array IR.Term) : Array IR.Term × IR.Term :=
    match t with
    | .prod _ ty b => if isPh ty then (acc, t) else peelP b (acc.push ty)
    | t => (acc, t)
  let (tys, b) ← match c.bodyState, c.body with
    | "transparent", some body => pure (peelL body #[])
    | _, _ => do
      let (tys, b) := peelP c.type #[]
      guard (isPh b || match b with | .prod _ ty _ => isPh ty | _ => false)
      pure (tys, b)
  let n := tys.size
  -- a factor at depth k (under k non-dependent products): `phantom (rel a) (rel v)`
  let factor (t : IR.Term) (k : Nat) : Option (Nat × Nat) := do
    let .app (.ind ⟨"Corelib.ssr.ssreflect_rw.phantom", 0⟩ _) args := t | none
    guard (args.size == 2)
    let .rel a := args[0]! | none
    let .rel v := args[1]! | none
    guard (k ≤ a && a < n + k && k ≤ v && v < n + k)
    let pa := n - 1 - (a - k)
    let pv := n - 1 - (v - k)
    let .sort _ := tys[pa]! | none
    -- the value parameter's type is the sort parameter (`rel j` under pv binders)
    let .rel j := tys[pv]! | none
    guard (j < pv && pv - 1 - j == pa)
    return (pa, pv)
  let rec chain (t : IR.Term) (k : Nat) (acc : Array (Nat × Nat)) : Option (Array (Nat × Nat)) :=
    match t with
    | .prod _ a rest =>
      if rest.mentionsRels 0 1 then none else
      match factor a k with
      | some p => chain rest (k + 1) (acc.push p)
      | none => none
    | t => (factor t k).map acc.push
  let ps ← chain b 0 #[]
  guard (!ps.isEmpty)
  return ps

/-- Rule Q-a: the sort arguments at the sort-parameter positions of phantom-definition applications,
replaced by `Prop` (a placeholder: the translation puts the type of the paired value there). Returns
the term and whether anything was replaced. -/
partial def erasePhantomSorts (pd : Std.HashMap String (Array (Nat × Nat))) (t : IR.Term) : IR.Term × Bool :=
  let go (u : IR.Term) := erasePhantomSorts pd u
  let goA (as : Array IR.Term) : Array IR.Term × Bool :=
    as.foldl (fun (acc, ch) x => let (y, c) := go x; (acc.push y, ch || c)) (#[], false)
  match t with
  | .app f args =>
    let (f', c1) := go f
    let (args', c2) := goA args
    match f with
    | .const d _ => match pd[d]? with
      | some pairs =>
        let (a, c3) := pairs.foldl (fun (a, ch) (si, _) =>
          match a[si]? with
          | some (.sort _) => (a.set! si (.sort .prop), true)
          | _ => (a, ch)) (args', false)
        (.app f' a, c1 || c2 || c3)
      | none => (.app f' args', c1 || c2)
    | _ => (.app f' args', c1 || c2)
  | .cast c kd ty => let (c', u1) := go c; let (ty', u2) := go ty; (.cast c' kd ty', u1 || u2)
  | .prod n ty b => let (a, u1) := go ty; let (b', u2) := go b; (.prod n a b', u1 || u2)
  | .lam n ty b => let (a, u1) := go ty; let (b', u2) := go b; (.lam n a b', u1 || u2)
  | .letIn n v ty b =>
    let (v', u1) := go v; let (ty', u2) := go ty; let (b', u3) := go b
    (.letIn n v' ty' b', u1 || u2 || u3)
  | .case i np r pu ps pctx ret c brs =>
    let (ps', u1) := goA ps; let (ret', u2) := go ret; let (c', u3) := go c
    let (brs', u4) := brs.foldl (fun (acc, ch) (ctx, b) => let (b', u) := go b; (acc.push (ctx, b'), ch || u)) (#[], false)
    (.case i np r pu ps' pctx ret' c' brs', u1 || u2 || u3 || u4)
  | .proj i np a c => let (c', u) := go c; (.proj i np a c', u)
  | .fix ds idx =>
    let (ds', u) := ds.foldl (fun (acc, ch) (n, ty, b, r) =>
      let (ty', u1) := go ty; let (b', u2) := go b; (acc.push (n, ty', b', r), ch || u1 || u2)) (#[], false)
    (.fix ds' idx, u)
  | _ => (t, false)

/-- M6 δ-inlining of `Set`-motive constants (a last tier): every application of a constant of
`names` is replaced by its source body β-reduced with the arguments (definitional). Returns the
term and the names actually inlined. -/
partial def inlineConsts (bodies : Std.HashMap String IR.Term) (names : Std.HashSet String) (t : IR.Term)
    (fuel : Nat := 8) : IR.Term × Std.HashSet String :=
  let go (u : IR.Term) := inlineConsts bodies names u fuel
  let goA (as : Array IR.Term) : Array IR.Term × Std.HashSet String :=
    as.foldl (fun (acc, used) x => let (y, u) := go x; (acc.push y, used.insertMany u)) (#[], ({} : Std.HashSet String))
  match t with
  | .app (.const c u) args =>
    let (args', used) := goA args
    match bodies[c]? with
    | some body => if fuel > 0 && names.contains c then
        let (r, u2) := inlineConsts bodies names (IR.betaApp body args').flattenApps (fuel - 1)
        (r, (used.insertMany u2).insert c)
      else (.app (.const c u) args', used)
    | none => (.app (.const c u) args', used)
  | .app f args => let (f', u1) := go f; let (as, u2) := goA args; (.app f' as, u1.insertMany u2)
  | .cast c kd ty => let (c', u1) := go c; let (ty', u2) := go ty; (.cast c' kd ty', u1.insertMany u2)
  | .prod n ty b => let (a, u1) := go ty; let (b', u2) := go b; (.prod n a b', u1.insertMany u2)
  | .lam n ty b => let (a, u1) := go ty; let (b', u2) := go b; (.lam n a b', u1.insertMany u2)
  | .letIn n v ty b =>
    let (v', u1) := go v; let (ty', u2) := go ty; let (b', u3) := go b
    (.letIn n v' ty' b', (u1.insertMany u2).insertMany u3)
  | .case i np r pu ps pctx ret c brs =>
    let (ps', u1) := goA ps; let (ret', u2) := go ret; let (c', u3) := go c
    let (brs', u4) := brs.foldl (fun (acc, used) (ctx, b) => let (b', u) := go b; (acc.push (ctx, b'), used.insertMany u)) (#[], ({} : Std.HashSet String))
    (.case i np r pu ps' pctx ret' c' brs', ((u1.insertMany u2).insertMany u3).insertMany u4)
  | .proj i np a c => let (c', u) := go c; (.proj i np a c', u)
  | .fix ds idx =>
    let (ds', u) := ds.foldl (fun (acc, used) (n, ty, b, r) =>
      let (ty', u1) := go ty; let (b', u2) := go b; (acc.push (n, ty', b', r), (used.insertMany u1).insertMany u2)) (#[], ({} : Std.HashSet String))
    (.fix ds' idx, u)
  | _ => (t, {})

/-- M6 δβ-inlining of higher-order recursive uses (Ring_polynom `Padd` passes itself to `PaddI` and
`PaddX`; Tauto `xcnf` passes `xcnf TX AF` to `mk_and`): in the body of a fixpoint block, an
application `c args` of a transparent monomorphic constant `c` some argument of which uses a function
of the block other than in a full call (`partialRecUse`) is replaced by `c`'s source body β-reduced with `args` (δβ,
definitional), so the recursive uses inside `c` become ordinary recursive calls that the structural
lowering checks (Rocq's guard checker unfolds `c` in the same way). Repeated up to `fuel` times. -/
partial def inlineRecArgs (bodies : Std.HashMap String IR.Term) (need : Array Nat) (t : IR.Term)
    (depth : Nat := 0) (fuel : Nat := 16) : IR.Term :=
  let go (u : IR.Term) (d : Nat) := inlineRecArgs bodies need u (depth + d) fuel
  match t with
  | .app (.const c u) args =>
    if fuel > 0 && args.any (·.partialRecUse depth need) then
      match bodies[c]? with
      | some body => inlineRecArgs bodies need (IR.betaApp body args).flattenApps depth (fuel - 1)
      | none => .app (.const c u) (args.map (go · 0))
    else .app (.const c u) (args.map (go · 0))
  | .evar ev args => .evar ev (args.map (go · 0))
  | .cast c kd ty => .cast (go c 0) kd (go ty 0)
  | .prod n ty b => .prod n (go ty 0) (go b 1)
  | .lam n ty b => .lam n (go ty 0) (go b 1)
  | .letIn n v ty b => .letIn n (go v 0) (go ty 0) (go b 1)
  | .app f args => .app (go f 0) (args.map (go · 0))
  | .case i np r pu ps pctx ret c brs =>
    .case i np r pu (ps.map (go · 0)) pctx (go ret pctx.size) (go c 0) (brs.map fun (ctx, b) => (ctx, go b ctx.size))
  | .proj i np a c => .proj i np a (go c 0)
  | .fix ds idx => .fix (ds.map fun (n, ty, b, r) => (n, go ty 0, go b ds.size, r)) idx
  | .cofix ds idx => .cofix (ds.map fun (n, ty, b, r) => (n, go ty 0, go b ds.size, r)) idx
  | _ => t

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
  if a.containsFVar ac.ih.fvarId! || a.containsFVar ac.f then
    failT "UNSUPPORTED_FEATURE" "accessibility lowering: nested recursive call in the decreasing argument"
  -- (a metavariable in the decreasing argument must be a prerequisite hypothesis of the declaration — a
  -- pending function in it, `div.gcdn`'s `modn` — which becomes a binder; any other is unresolved)
  if a.hasExprMVar then
    let hs ← match (← read).hyps with | some r => pure ((← r.get).map (·.1)) | none => pure #[]
    let ms ← liftMeta (getMVars a)
    unless ms.all hs.contains do
      failT "UNSUPPORTED_FEATURE" "accessibility lowering: the decreasing argument has unresolved metavariables"
  let pr ← liftMeta (accPairOf ac.hasIdx ac.nparams ac.idxTy ac.fam ac.idxLvl a)
  -- the call's own context: every local introduced after Acc.rec's minor premise (let-bound
  -- locals are unfolded in the argument instead)
  let lctx ← getLCtx
  let hid ← match ac.hidden with | some r => r.get | none => pure #[]
  let ctx := lctx.getFVars.filter fun v => !ac.base.contains v.fvarId! && !(lctx.get! v.fvarId!).isLet && !hid.contains v.fvarId!
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
      -- (let-bound locals are unfolded in the whole disjunct, including the types of the context's
      -- binders, which may mention them — `div.gcdn`'s `h : n' = n₀.+1` with `n' := n %% m` — before the
      -- context is abstracted, since a let's value may mention the context itself)
      let d ← liftMeta <| withLocalDecl `y .default cTy fun y => do
        let mut b := mkApp3 (mkConst ``Eq [cLvl]) cTy y prZ
        for x in ctx.reverse do
          let xd := lctx.get! x.fvarId!
          let ty := unfoldLets (← instantiateMVars xd.type)
          b := mkApp2 (mkConst ``Exists [← getLevel ty]) ty (.lam xd.userName ty (b.abstract #[x]) .default)
        mkLambdaFVars #[y, ac.s] b
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
  -- (a large-eliminating inductive's recursor takes the motive level first: here Prop)
  let large := rv.levelParams.length == indLvls.length + 1
  let recC := mkConst (iname.str "rec") (if large then .zero :: indLvls else indLvls)
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

/-- M6 mutual fixpoints: component `j` of a right-nested `PProd C₀ (PProd C₁ … C_{n-1})`. -/
def pprodProj (e : Expr) (j n : Nat) : Expr := Id.run do
  let mut e := e
  for _ in [0:j] do e := .proj ``PProd 1 e
  if j + 1 < n then e := .proj ``PProd 0 e
  return e

/-- The right-nested product `PProd C₀ (PProd C₁ … C_{n-1})`. -/
def mkPProdTy (cs : Array Expr) : MetaM Expr := do
  let mut acc := cs.back!
  for j in (List.range (cs.size - 1)).reverse do
    acc ← mkAppM ``PProd #[cs[j]!, acc]
  return acc

/-- The right-nested tuple of `vs` (`vs[j] : cs[j]`) in `mkPProdTy cs`. -/
def mkPProdVal (cs vs : Array Expr) : MetaM Expr := do
  let mut accT := cs.back!
  let mut accV := vs.back!
  for j in (List.range (cs.size - 1)).reverse do
    accV ← mkAppOptM ``PProd.mk #[cs[j]!, accT, vs[j]!, accV]
    accT ← mkAppM ``PProd #[cs[j]!, accT]
  return accV

/-- The recursive result for a recursive call whose decreasing argument is `y`: `ih_y` for a direct
recursive field `y`, or `ih_g zs` for an application `g zs` of a functional recursive field `g`
(M6). Also returns the indices of `y`'s type. -/
def recResultOf (fieldIH : Array (Expr × Expr × Array Expr)) (nparams : Nat) (y : Expr) (zs' : Array Expr) :
    TransM (Expr × Array Expr) := do
  if let some (_, ih, yIdx) := fieldIH.find? (·.1 == y) then return (ih, yIdx)
  let g := y.getAppFn
  let some (_, ih, _) := fieldIH.find? (·.1 == g)
    | failT "UNSUPPORTED_FEATURE" "recursive call on a term that is not a direct recursive constructor field"
  let zs := y.getAppArgs
  let gt ← liftMeta do whnf (← inferType g)
  unless gt.isForall && zs.size > 0 do
    failT "UNSUPPORTED_FEATURE" "recursive call on a term that is not a direct recursive constructor field"
  let yt ← liftMeta do whnf (← inferType y)
  unless yt.getAppFn == (← liftMeta do forallTelescopeReducing gt fun _ b => do pure (← whnf b).getAppFn) do
    failT "UNSUPPORTED_FEATURE" "functional recursive field applied to too few arguments"
  return (mkAppN ih zs', yt.getAppArgs.extract nparams yt.getAppArgs.size)

/-- Open the function binders of a mutual fixpoint block. -/
partial def withFixNames {α} (ns : Array Name) (tys : Array Expr) (i : Nat) (acc : Array Expr)
    (k : Array Expr → TransM α) : TransM α := do
  if h : i < ns.size then withLocalDecl ns[i] .default tys[i]! fun v => withFixNames ns tys (i + 1) (acc.push v) k
  else k acc

/-- M6 mutual fixpoints: replace each recursive call `f_i P… y rest` (any function of the block) by
`(ih_y).i G' rest`, `ih_y` being the joint recursive result of the direct recursive field `y`. The
other parameters before the decreasing argument must be unchanged (index variables: the field's
indices). Any other occurrence of a block function is rejected. -/
partial def replaceRecCallsMutual (fs : Array FVarId) (P : Array Expr) (idxPos : Array (Option Nat))
    (fieldIH : Array (Expr × Expr × Array Expr)) (gpos : Array Nat) (nparams : Nat) (e : Expr) : TransM Expr := do
  let go := replaceRecCallsMutual fs P idxPos fieldIH gpos nparams
  match e with
  | .app .. =>
    let fn := e.getAppFn
    let args := e.getAppArgs
    if let some fi := fs.findIdx? (fn.isFVarOf ·) then
      let r := P.size
      unless args.size ≥ r + 1 do failT "UNSUPPORTED_FEATURE" "recursive call without its decreasing argument"
      let y := args[r]!
      let (ih, yIdx) ← recResultOf fieldIH nparams y (← y.getAppArgs.mapM go)
      for i in [0:r] do
        if gpos.contains i then continue          -- generalized: passed to the recursive result
        match idxPos[i]! with
        | none =>
          unless args[i]! == P[i]! do
            failT "UNSUPPORTED_FEATURE" s!"mutual recursive call changes parameter {i}, which precedes the decreasing argument"
        | some j =>
          unless args[i]! == yIdx[j]! do
            failT "UNSUPPORTED_FEATURE" s!"recursive call passes index argument {i} different from the field's index"
      return mkAppN (pprodProj ih fi fs.size) ((← gpos.mapM fun i => go args[i]!) ++ (← (args.extract (r + 1) args.size).mapM go))
    return mkAppN (← go fn) (← args.mapM go)
  | .lam n t b bi => return .lam n (← go t) (← go b) bi
  | .forallE n t b bi => return .forallE n (← go t) (← go b) bi
  | .letE n t v b nd =>
    if fs.any v.containsFVar then go (b.instantiate1 v) else return .letE n (← go t) (← go v) (← go b) nd
  | .mdata d b => return .mdata d (← go b)
  | .proj sn i b => return .proj sn i (← go b)
  | .fvar id => if fs.contains id then failT "UNSUPPORTED_FEATURE" "recursive function used other than in a call" else pure e
  | _ => pure e

/-- M6 course-of-values recursion: `Below := λ x, I.rec (λ _, Sort w) minors x` with
`minor_k := λ fields belows, PProd (PProd (M f₁) b₁) (… (PProd (PProd (M f_n) b_n) PUnit))` over the
recursive fields `f_i` (Lean's `below`; `w = max 1 u`, `M : I params → Sort u`). -/
def mkCovBelow (iname : Name) (indLvls : List Level) (params : Array Expr) (rv : RecursorVal)
    (xty motiveM : Expr) (w : Level) : TransM Expr := do
  let motB ← withLocalDecl `x .default xty fun z => bindFVars true #[z] (mkSort w)
  let recB := mkConst (iname.str "rec") (mkLevelSucc w :: indLvls)
  let mut ty ← liftMeta do instantiateForall (← inferType recB) (params.push motB)
  let mut minors : Array Expr := #[]
  for k in [0:rv.numMinors] do
    let .forallE _ minorTy rest _ ← liftMeta (whnf ty) | failT "TRANSLATION_FAILED" s!"{iname}.rec: missing minor {k}"
    let m ← minorTelescope minorTy rv.rules[k]!.nfields iname params fun fields recFields ihs _ => do
      let mut acc := mkConst ``PUnit [w]
      for (f, b) in (recFields.zip ihs).reverse do
        let e ← liftMeta (mkAppM ``PProd #[motiveM.beta #[f], b])
        acc ← liftMeta (mkAppM ``PProd #[e, acc])
      bindFVars true (fields ++ ihs) acc
    minors := minors.push m
    ty := rest.instantiate1 m
  withLocalDecl `x .default xty fun z => bindFVars true #[z] (mkAppN recB (params ++ #[motB] ++ minors ++ #[z]))

/-- M6 cast repair (proofs only). A Rocq cast `c : T` whose conversion needs a fixpoint to unfold
at open arguments (Ring_polynom `norm_aux_PEadd`: `norm_aux (PEadd pe1 pe2)` against its unfolded
body) is not definitional for the recursor-based lowerings. When `T` is a proposition, `c` is
transported along case analysis on free variables of `T`, until both sides are definitionally
equal: `I.rec (λ v, A v → T v) (λ fs ihs h, h | nested) v c` — a generated proof that implements the
lowering's unfolding equation; every leaf is the transported source proof `h` itself. Bounded depth. -/
partial def castRepair (c act exp : Expr) (fuel : Nat) : MetaM (Option Expr) := do
  if ← isDefEq act exp then return some c
  if fuel == 0 then return none
  let cands := (Lean.collectFVars {} exp).fvarIds.map mkFVar
  for v in cands do
    let vty ← whnf (← inferType v)
    let .const iname lvls := vty.getAppFn | continue
    let some (.inductInfo iv) := (← getEnv).find? iname | continue
    unless iv.numIndices == 0 && !iv.isNested && iv.all.length == 1 do continue
    let some (.recInfo rv) := (← getEnv).find? (iname.str "rec") | continue
    let large := rv.levelParams.length == lvls.length + 1
    let params := vty.getAppArgs
    let motive := Expr.lam `z vty (.forallE `h (act.abstract #[v]) ((exp.abstract #[v]).liftLooseBVars 0 1) .default) .default
    let recC := mkConst rv.name (if large then .zero :: lvls else lvls)
    let mut ty ← instantiateForall (← inferType recC) (params.push motive)
    let mut minors : Array Expr := #[]
    let mut ok := true
    for k in [0:rv.numMinors] do
      let .forallE _ minorTy rest _ ← whnf ty | ok := false; break
      -- exactly the fields, their recursive results and the transported proof `h` (the goal may
      -- itself be a ∀-proposition, whose binders are not opened)
      let nf := rv.rules[k]!.nfields
      let m? ← forallBoundedTelescope minorTy (some nf) fun fs rest => do
        unless fs.size == nf do return none
        let mut nih := 0
        for f in fs do
          if (← whnf (← inferType f)).getAppFn.isConstOf iname then nih := nih + 1
        forallBoundedTelescope rest (some (nih + 1)) fun xs body => do
          unless xs.size == nih + 1 do return none
          let h := xs.back!
          let some r ← castRepair h (← inferType h) body (fuel - 1) | return none
          return some (← mkLambdaFVars (fs ++ xs) r)
      let some m := m? | ok := false; break
      minors := minors.push m
      ty := rest.instantiate1 m
    if ok then return some (mkApp (mkAppN recC (params ++ #[motive] ++ minors ++ #[v])) c)
  return none

/-- A backtracking point of a translation: the Meta state together with the sizes of the registries
that live outside it (prerequisite hypotheses, per-occurrence shared levels). Restoring it also drops
the entries an abandoned attempt registered, which would otherwise name metavariables that no longer
exist (`div.gcdn`: a hypothesis for `modn`'s prerequisite created by the failed structural lowering). -/
structure TransSaved where
  st : Meta.SavedState
  hyps : Nat
  shared : Nat

def saveTrans : TransM TransSaved := do
  let st ← liftMeta saveState
  let hyps ← match (← read).hyps with | some r => pure (← r.get).size | none => pure 0
  let shared ← match (← read).sharedFresh with | some r => pure (← r.get).size | none => pure 0
  return { st, hyps, shared }

def restoreTrans (s : TransSaved) : TransM Unit := do
  liftMeta s.st.restore
  if let some r := (← read).hyps then r.modify (·.take s.hyps)
  if let some r := (← read).sharedFresh then r.modify (·.take s.shared)

/-- Rule P, term level: `e : act` used at `exp`, where the two differ only by a lift of a proposition.
`exp ≡ PULift.{r,0} P` with `act ≡ P` gives `PULift.up e`; `act ≡ PULift.{r,0} P` with `exp ≡ P` (a
proposition) gives `PULift.down e`. Only `PULift.{_, 0}`: the lifted type is a proposition. -/
def liftCoerce (e act exp : Expr) : MetaM (Option Expr) := do
  let exp' ← whnf exp
  if exp'.isAppOfArity ``PULift 1 then
    if let [r, u] := exp'.getAppFn.constLevels! then
      if u.isZero && (← isDefEq act exp'.appArg!) then
        return some (mkApp2 (mkConst ``PULift.up [r, .zero]) exp'.appArg! e)
  let act' ← whnf act
  if act'.isAppOfArity ``PULift 1 then
    if let [r, u] := act'.getAppFn.constLevels! then
      if u.isZero && (← isProp exp) && (← isDefEq act'.appArg! exp) then
        return some (mkApp2 (mkConst ``PULift.down [r, .zero]) act'.appArg! e)
  return none

/-- Rule P, term level: the arguments of `f a₁ … aₙ`, each coerced by `liftCoerce` where its type is not
the function's domain at it (counted in `cnt`). -/
def coerceArgs (f : Expr) (args : Array Expr) (cnt : IO.Ref Nat) (lifted : Std.HashSet Name) : MetaM (Array Expr) := do
  -- (speed, exact: a lift can only appear by unfolding a constant of `lifted`, or a let-bound local)
  let mayLift (e : Expr) : MetaM Bool := do
    let e ← instantiateMVars e
    if (e.find? fun x => x.isConst && lifted.contains x.constName!).isSome then return true
    let lctx ← getLCtx
    return (e.find? fun x => x.isFVar && ((lctx.find? x.fvarId!).map (·.isLet)).getD false).isSome
  let mut fty ← inferType f
  let mut out := #[]
  for a in args do
    fty ← whnf fty
    let .forallE _ d b _ := fty | return out ++ args.extract out.size args.size
    let a' ← do
      let aty ← inferType a
      if !(← mayLift d) && !(← mayLift aty) then pure a else
      if ← isDefEq aty d then pure a else
        match ← liftCoerce a aty d with
        | some c => cnt.modify (· + 1); pure c
        | none => pure a
    out := out.push a'
    fty := b.instantiate1 a'
  return out

/-- Rule P, term level: `b` used at `cod`. Directly (`liftCoerce`), or, for a function at a function type
whose domains or codomain differ by lifts, η-expanded with its arguments and result coerced
(`fun xs => PULift.up (o (PULift.down x) …)`); unchanged when nothing needs a coercion. -/
partial def liftCoerceValue (b cod : Expr) (cnt : IO.Ref Nat) (lifted : Std.HashSet Name) : MetaM Expr := do
  let bt ← inferType b
  if ← isDefEq bt cod then return b
  if let some c ← liftCoerce b bt cod then
    cnt.modify (· + 1); return c
  let cod' ← whnf cod
  unless cod'.isForall do return b
  let n0 ← cnt.get
  let r ← forallTelescope cod' fun ys cod2 => do
    let args ← coerceArgs b ys cnt lifted
    unless args.size == ys.size do return none
    let b2 ← liftCoerceValue (mkAppN b args) cod2 cnt lifted
    if (← cnt.get) == n0 then return none
    return some (← mkLambdaFVars ys b2)
  return r.getD b

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
    if ok then return c'
    -- M6: a proof whose cast needs a fixpoint's unfolding at open arguments (castRepair)
    if ← liftMeta (isProp ty') then
      if let some r ← liftMeta (castRepair c' (← inferType c') ty' 3) then return r
    if let some cnt := (← read).propCoerce then
      if let some r ← liftMeta (liftCoerce c' (← inferType c') ty') then
        cnt.modify (· + 1); return r
    failT "TRANSLATION_FAILED" s!"{kind} cast annotation is not convertible in Lean"
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
    -- rule Q-a: a phantom check's sort arguments, per occurrence, at the types of their values
    let args' ← if !(← read).phantomLower then pure args' else
      match f with
      | .const d _ => match (← read).genv.phantomDefs[d]? with
        | some pairs => liftMeta do
          let mut a := args'
          for (si, vi) in pairs do
            if h : si < args.size then
              if let .sort _ := args[si] then
                if vi < a.size then a := a.set! si (← instantiateMVars (← inferType a[vi]!))
          pure a
        | none => pure args'
      | _ => pure args'
    let f' ← withPath "f" (transHead f args')
    let args' ← match (← read).propCoerce with
      | some cnt => do liftMeta (coerceArgs f' args' cnt (← read).genv.liftTargets)
      | none => pure args'
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
    unless tgt.pendingHyps.isEmpty do failT "UNSUPPORTED_FEATURE" "non-uniform match on a pending inductive (pending validation)"
    return ← transCaseNU tgt ind npar puinst pparams pctx pret scrut brs
  let iname := tgt.types[ind.idx]!
  let rv ← recursorOf iname (nested := true)
  let nmain ← mainMinors iname
  -- statement mode: a pending inductive's recursor takes its hypotheses first
  let nh := tgt.pendingHyps.size
  unless rv.numParams == npar + nh && pparams.size == npar do
    failT "EXPORT_VALIDATION_FAILED" s!"case has {pparams.size} parameters, {iname}.rec expects {rv.numParams}"
  unless pctx.size == rv.numIndices + 1 do
    failT "EXPORT_VALIDATION_FAILED" s!"case return context has {pctx.size} binders, expected {rv.numIndices + 1}"
  unless brs.size == nmain do
    failT "EXPORT_VALIDATION_FAILED" s!"case has {brs.size} branches, {iname} has {nmain} constructors"
  let params ← pparams.mapIdxM fun k a => withPath s!"param{k}" (trans a)
  let params ← if nh == 0 then pure params else do
    let some ref := (← read).hyps | failT "TRANSLATION_FAILED" "match on a pending inductive outside pending validation"
    let hs ← tgt.pendingHyps.mapM fun l => do
      match (← ref.get).find? (·.2 == l) with
      | some (m, _) => pure (mkMVar m)
      | none => failT "TRANSLATION_FAILED" s!"match on a pending inductive before its hypothesis {l} is in scope"
    pure (hs ++ params)
  let npar := npar + nh
  let scrut' ← withPath "scrutinee" (trans scrut)
  -- rule P, term level: a scrutinee of a lifted type (`h : Rnat a b` matched as the equation it lifts)
  -- is its proof, `PULift.down h`
  let scrut' ← match (← read).propCoerce with
    | some cnt => liftMeta do
      let t ← whnf (← inferType scrut')
      match t.getAppFn with
      | .const ``PULift [r, u] =>
        if t.getAppNumArgs == 1 && u.isZero then
          cnt.modify (· + 1); pure (mkApp2 (mkConst ``PULift.down [r, .zero]) t.appArg! scrut')
        else pure scrut'
      | _ => pure scrut'
    | none => pure scrut'
  -- M6 ι-generalized fix lowering: a match on the decreasing argument, which is the constructor
  -- application C_k fields in this minor premise, is its branch k (Rocq's and Lean's ι-rule)
  if let some (_, k, fields) := (← read).iota.find? (·.1 == scrut') then
    let some (bctx, bbody) := brs[k]? | failT "EXPORT_VALIDATION_FAILED" "ι-reduction: no such branch"
    unless bctx.size == fields.size do
      failT "UNSUPPORTED_FEATURE" s!"ι-reduction: branch {k} binds {bctx.size} names for {fields.size} fields"
    return ← withPath s!"iota{k}" (withReader (fun c => { c with locals := c.locals ++ fields }) (trans bbody))
  -- M6 course-of-values: a match on a subterm with a known result carries it into the branches
  if let some cs := (← read).cov then
    if let some (_, rz) := cs.results.find? (·.1 == scrut') then
      unless rv.numMotives == 1 do failT "UNSUPPORTED_FEATURE" "course-of-values match on a nested inductive"
      if cs.iname == iname && (← (params.zip cs.params).allM fun (a, b) => liftMeta (isDefEq a b)) && params.size == cs.params.size then
        return ← transCaseCov cs rz iname rv params pctx pret scrut' brs
  -- B (termination lowering): a match enclosing a recursive call of the fixpoint being lowered
  -- carries the equation `scrut = z` into its branches (convoy), `I.rec (λ z, scrut = z → RET) minors
  -- scrut (Eq.refl scrut)`: the call's context, hence the call relation, records why its argument
  -- decreases. The branches compute exactly the source branches (the equation is only bound).
  let convoy ← match (← read).accSite with
    | some ac =>
      if ac.convoy then
        let ls := (← read).locals
        match ls.findIdx? (·.isFVarOf ac.f) with
        | some p => pure (brs.any fun (ctx, b) => b.mentionsRels (ls.size - 1 - p + ctx.size) 1)
        | none => pure false
      else pure false
    | none => pure false
  if convoy && rv.numIndices > 0 then
    failT "UNSUPPORTED_FEATURE" "termination lowering: a match on an indexed inductive encloses a recursive call"
  let sty ← liftMeta do whnf (← instLevelMVars (← inferType scrut'))
  let eqLvl ← if convoy then liftMeta (getLevel sty) else pure Level.zero
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
    let ret := if convoy then mkForall `h .default (mkApp3 (mkConst ``Eq [eqLvl]) sty scrut' xs.back!) ret else ret
    return (← bindFVars true xs ret, u.normalize)
  if !large && u != Level.zero then
    failT "UNSUPPORTED_FEATURE" s!"elimination of {iname} into a non-Prop sort is not available in Lean"
  let recConst := mkConst (iname.str "rec") (recLvls u)
  let ty1 ← liftMeta do instantiateForall (← inferType recConst) (params.push motive)
  let (auxM, ty2) ← liftMeta (auxMotives rv u ty1)
  let mut ty := ty2
  let mut minors : Array Expr := #[]
  for k in [0:nmain] do
    let .forallE _ minorTy rest _ ← liftMeta (whnf ty) | failT "TRANSLATION_FAILED" s!"{iname}.rec: missing minor {k}"
    let (bctx, bbody) := brs[k]!
    let nfields := rv.rules[k]!.nfields
    unless bctx.size == nfields do
      failT "UNSUPPORTED_FEATURE" s!"branch {k}: {bctx.size} binders for {nfields} fields (let-bound constructor arguments)"
    let minor ← minorTelescope minorTy nfields iname params fun fields _ ihs res => do
      if convoy then
        if let some ac := (← read).accSite then
          if let some r := ac.hidden then r.modify (· ++ ihs.map (·.fvarId!))
        let .forallE hn hty _ _ ← liftMeta (whnf res) | failT "TRANSLATION_FAILED" "convoy: minor premise without its equation"
        withLocalDecl hn .default hty fun h => do
          let body ← withPath s!"branch{k}" (withReader (fun c => { c with locals := c.locals ++ fields }) (trans bbody))
          bindFVars true (fields ++ ihs ++ #[h]) body
      else
      let body ← withPath s!"branch{k}" (withReader (fun c => { c with locals := c.locals ++ fields }) (trans bbody))
      bindFVars true (fields ++ ihs) body
    minors := minors.push minor
    ty := rest.instantiate1 minor
  let auxN ← liftMeta (auxMinors (rv.numMinors - nmain) u ty)
  let conv := if convoy then #[mkApp2 (mkConst ``Eq.refl [eqLvl]) sty scrut'] else #[]
  return mkAppN recConst (params ++ #[motive] ++ auxM ++ minors ++ auxN ++ idx ++ #[scrut'] ++ conv)

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
  -- rule P, term level: a scrutinee of a lifted type (`h : Rnat a b` matched as the equation it lifts)
  -- is its proof, `PULift.down h`
  let scrut' ← match (← read).propCoerce with
    | some cnt => liftMeta do
      let t ← whnf (← inferType scrut')
      match t.getAppFn with
      | .const ``PULift [r, u] =>
        if t.getAppNumArgs == 1 && u.isZero then
          cnt.modify (· + 1); pure (mkApp2 (mkConst ``PULift.down [r, .zero]) t.appArg! scrut')
        else pure scrut'
      | _ => pure scrut'
    | none => pure scrut'
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
    (fieldIH : Array (Expr × Expr × Array Expr)) (gpos : Array Nat) (nparams : Nat) (e : Expr)
    (lenient : Bool := false) : TransM Expr := do
  let go (x : Expr) := replaceRecCalls f P idxPos fieldIH gpos nparams x lenient
  match e with
  | .app .. =>
    let fn := e.getAppFn
    let args := e.getAppArgs
    if fn.isFVarOf f then
      let r := P.size
      unless args.size ≥ r + 1 do failT "UNSUPPORTED_FEATURE" "recursive call without its decreasing argument"
      let y := args[r]!
      -- lenient (a course-of-values branch): calls on other subterms are left for an enclosing pass
      if lenient && !(fieldIH.any fun (z, _, _) => z == y || z == y.getAppFn) then
        return mkAppN fn (← args.mapM go)
      let (ih, yIdx) ← recResultOf fieldIH nparams y (← y.getAppArgs.mapM go)
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
  | .letE n t v b nd =>
    -- M6 ζ: a let-bound partial application of the recursive function (Pos.peano_rect's `f2`) is
    -- inlined (definitional), so its calls become recursive calls
    if v.containsFVar f then go (b.instantiate1 v) else return .letE n (← go t) (← go v) (← go b) nd
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
  let bodies := (← read).genv.irBodies
  let need := defs.reverse.map (·.2.2.2 + 1)
  let defs := defs.map fun (n, ty, b, r) => (n, ty, inlineRecArgs bodies need b, r)
  -- statement mode: ζ on the source body first, as the audit reads it (proof mode unchanged)
  let defs := if (← read).genv.stmtMode then defs.map fun (n, ty, b, r) => (n, ty, b.zetaFixLets 0 defs.size, r) else defs
  if defs.size > 1 then return ← transFixMutual defs fidx
  -- M6 course-of-values recursion, only when the structural lowering finds a recursive call on a
  -- subterm that is not a direct recursive field (Ring_polynom `norm_aux`)
  let saved ← saveTrans
  tryCatchThe TransError (transFix1 defs false) fun e => do
    unless e.msg.startsWith "recursive call on a term that is not a direct recursive constructor field" do
      throwThe TransError e
    restoreTrans saved
    unless (← read).genv.stmtMode do return ← transFix1 defs true
    -- B (statement mode, docs/TERMINATION.md): recursion that neither the structural nor the
    -- course-of-values lowering covers (a call on a subterm Rocq's guard sees only by reducing a
    -- function, MathComp's edivn_rec) is lowered to Acc.rec over its call relation, with an explicit
    -- termination obligation
    let saved2 ← saveTrans
    tryCatchThe TransError (transFix1 defs true) fun e2 => do
      unless e2.msg.startsWith "recursive call on a term that is not a direct recursive constructor field" do
        throwThe TransError e2
      restoreTrans saved2
      transFixWf defs

/-- The single-fixpoint lowering (see `transFix`); `cov`: course-of-values recursion, with motive
`λ x, PProd (M x) (Below x)` (`mkCovBelow`), minor `k` the pair of the branch and the chain of the
fields' results, recursive calls on any subterm `z` with a known result `r_z` (direct fields, and the
fields of a `match` on such a subterm: `transCaseCov`) as `(r_z).1 G' Q'`, and the function the first
component. Scope: inductives without indices or non-uniform parameters, with large elimination. -/
partial def transFix1 (defs : Array (AName × IR.Term × IR.Term × Nat)) (cov : Bool) : TransM Expr := do
  let (fname, fty, fbody, rarg) := defs[0]!
  let fty' ← withPath "type" (trans fty)
  let (lams, b) := peelLams fbody
  unless rarg < lams.size do
    failT "UNSUPPORTED_FEATURE" s!"decreasing argument {rarg} is not bound by the leading lambdas ({lams.size})"
  -- the body is a match on the decreasing argument (M3c), or any term (M6: ι-generalized lowering)
  let outerCase : Option (IndRef × Nat × Array (Array AName × IR.Term)) := match b with
    | .case cind cnpar _ _ _ _ _ (.rel sj) brs => if sj == lams.size - 1 - rarg then some (cind, cnpar, brs) else none
    | _ => none
  let outer := (← read).locals
  withLocalDecl (binderName fname) .default fty' fun fv => do
  withSourceLams lams (outer.push fv) 0 #[] fun as => do
    let P := as.extract 0 rarg
    let x := as[rarg]!
    let Q := as.extract (rarg + 1) as.size
    let T ← liftMeta (instantiateForall fty' as)
    let xty ← liftMeta do whnf (← inferType x)
    let (tgt, tidx) ← match outerCase with
      | some (cind, _, _) => pure (← lookupInd cind, cind.idx)
      | none =>
        match (← read).genv.inds.toList.findSome? fun (_, t) => (t.types.findIdx? (xty.getAppFn.isConstOf ·)).map (t, ·) with
        | some r => pure r
        | none => return ← transFixAcc defs
    let iname := tgt.types[tidx]!
    unless xty.getAppFn.isConstOf iname do
      failT "TRANSLATION_FAILED" "type of the decreasing argument is not the matched inductive"
    let rv ← recursorOf iname (nested := !cov)
    let nmain ← mainMinors iname
    -- non-uniform parameters (Lean indices) are the leading fields of Lean's constructors; Rocq's
    -- match counts them as parameters and its branches bind only the other fields (M6)
    let nu := tgt.nonUniform
    if let some (_, cnpar, brs) := outerCase then
      unless rv.numParams + nu == cnpar && brs.size == nmain do
        failT "EXPORT_VALIDATION_FAILED" "match metadata disagrees with the recursor"
    if outerCase.isNone && tgt.nonUniform > 0 then
      return ← transFixAcc defs      -- (accessibility lowering, or its rejection)
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
    let motiveM ← bindFVars true (idx.push x) QT
    let large := rv.levelParams.length == indLvls.length + 1
    if cov && (idx.size > 0 || nu > 0 || !large) then
      failT "UNSUPPORTED_FEATURE" "recursive call on a non-direct subterm (course-of-values) of an indexed, non-uniform or Prop-only inductive"
    let w := (mkLevelMax' (mkLevelSucc .zero) u).normalize
    let below ← if cov then mkCovBelow iname indLvls params rv xty motiveM w else pure motiveM
    let motive ← if cov then
        withLocalDecl `x .default xty fun z => do
          bindFVars true #[z] (← liftMeta (mkAppM ``PProd #[motiveM.beta #[z], below.beta #[z]]))
      else pure motiveM
    if !large && u != Level.zero then
      -- M6: structural recursion on a proof into data: accessibility lowering
      return ← transFixAcc defs
    let recConst := mkConst (iname.str "rec") (if cov then w :: indLvls else if large then u :: indLvls else indLvls)
    let recLvl := if cov then w else u
    let ty1 ← liftMeta do instantiateForall (← inferType recConst) (params.push motive)
    let (auxM, ty2) ← liftMeta (auxMotives rv recLvl ty1)
    let mut ty := ty2
    let mut minors : Array Expr := #[]
    for k in [0:nmain] do
      let .forallE _ minorTy rest _ ← liftMeta (whnf ty) | failT "TRANSLATION_FAILED" s!"{iname}.rec: missing minor {k}"
      let nfields := rv.rules[k]!.nfields
      if let some (_, _, brs) := outerCase then
        unless brs[k]!.1.size + nu == nfields do
          failT "UNSUPPORTED_FEATURE" s!"branch {k}: let-bound constructor arguments"
      let minor ← minorTelescope minorTy nfields iname params fun fields recFields ihs res => do
        let fieldIH ← (recFields.zip ihs).mapM fun (y, ih) => do
          let yt ← liftMeta do whnf (← inferType y)
          return (y, if cov then .proj ``PProd 0 ih else ih, yt.getAppArgs.extract rv.numParams yt.getAppArgs.size)
        let xk0 := mkAppN (mkConst tgt.ctors[tidx]![k]! indLvls) (params ++ fields)
        let res ← if cov then pure (motiveM.beta #[xk0]) else liftMeta (whnf res)
        let comp ← forallBoundedTelescope res (some (G.size + Q.size)) fun gqs _ => do
          unless gqs.size == G.size + Q.size do failT "TRANSLATION_FAILED" "minor result has fewer binders than the motive"
          let gs := gqs.extract 0 G.size
          let qs := gqs.extract G.size gqs.size
          -- The recursor runs this branch at every recursion depth: here the decreasing argument
          -- *is* the constructor applied to the fields, and the index variables of its type are
          -- that application's indices (not the outermost call's arguments).
          let xk := mkAppN (mkConst tgt.ctors[tidx]![k]! indLvls) (params ++ fields)
          let xkIdx ← liftMeta do
            let t ← whnf (← inferType xk)
            pure (t.getAppArgs.extract rv.numParams t.getAppArgs.size)
          -- Rocq's discipline: the constructor concludes at its own non-uniform variables
          for t in [0:nu] do
            unless xkIdx[t]? == fields[t]? do
              failT "UNSUPPORTED_FEATURE" s!"constructor {k} does not conclude at its non-uniform parameter"
          let P' := Id.run do
            let mut P' := P
            for i in gpos, g in gs do P' := P'.set! i g
            for i in [0:P.size] do
              if let some j := idxPos[i]! then P' := P'.set! i xkIdx[j]!
            return P'
          let cs : Option CovSite := if cov then
              some { f := fv.fvarId!, iname, params, motive, results := recFields.zip ihs, P := P', idxPos, gpos,
                     nparams := rv.numParams }
            else none
          let body ← match outerCase with
            | some (_, _, brs) =>
              let locals := outer ++ #[fv] ++ P' ++ #[xk] ++ qs ++ fields.extract nu fields.size
              withPath s!"branch{k}" (withReader (fun c => { c with locals := locals, cov := cs }) (trans brs[k]!.2))
            | none =>
              -- ι-generalized: the whole body, every match on the decreasing argument ι-reduced
              let locals := outer ++ #[fv] ++ P' ++ #[xk] ++ qs
              withPath s!"minor{k}" (withReader (fun c => { c with locals := locals, iota := c.iota.push (xk, k, fields), cov := cs }) (trans b))
          let body ← replaceRecCalls fv.fvarId! P' idxPos fieldIH gpos rv.numParams body
          bindFVars true (if cov then gs ++ qs else fields ++ ihs ++ gs ++ qs) body
        if !cov then return comp
        -- course-of-values: ⟨branch, ⟨r_{f₁}, … , PUnit.unit⟩⟩ (the chain is `Below (C_k fields)`)
        let mut chain := mkConst ``PUnit.unit [w]
        for ih in ihs.reverse do chain ← liftMeta (mkAppM ``PProd.mk #[ih, chain])
        let pair ← liftMeta (mkAppOptM ``PProd.mk #[some (motiveM.beta #[xk0]), some (below.beta #[xk0]), some comp, some chain])
        bindFVars true (fields ++ ihs) pair
      minors := minors.push minor
      ty := rest.instantiate1 minor
    let auxN ← liftMeta (auxMinors (rv.numMinors - nmain) recLvl ty)
    let recApp := mkAppN recConst (params ++ #[motive] ++ auxM ++ minors ++ auxN ++ idx ++ #[x])
    let res ← bindFVars true as (mkAppN (if cov then .proj ``PProd 0 recApp else recApp) (G ++ Q))
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

/-- B (docs/TERMINATION.md): a fixpoint on data whose recursive calls are on terms that are not
direct fields of the decreasing argument (`fix loop m q := match subn m d with 0 => … | S m' => loop m'
(S q)`, where Rocq's guard condition reduces `subn` to see that `m'` is a subterm of `m`). Lowered to
`Acc.rec` over the call relation `R y s := D₁ y s ∨ … ∨ Dₙ y s` (one disjunct per recursive call,
`∃ ctx, y = a`, as in the M6 accessibility lowering), with every match that encloses a call carrying
its scrutinee equation (convoy, `transCase`), so `R` records why each call decreases:

    λ P x Q, Acc.rec (C := I params) R (λ s _, ∀ G Q, T[s]) (λ s h ih, λ G Q, body′) x (wf Γ x) G Q

The well-foundedness `wf : ∀ Γ, ∀ s, Acc R s` (Γ the locals `R` mentions) is **not constructed**: it
is the termination obligation, a hypothesis of the pending artifact (leaf
`<decl>__rocq2lean_termination_<k>`, its statement a proof task); in assembly its final theorem. The
computed value is the source body's: each call is `ih a cert` with `cert : R a s` built from the call's
own context. Scope: decreasing argument of an inductive without indices, not a proof. -/
partial def transFixWf (defs : Array (AName × IR.Term × IR.Term × Nat)) : TransM Expr := do
  let unsup {α} (m : String) : TransM α := failT "UNSUPPORTED_FEATURE" s!"termination lowering: {m}"
  let (fname, fty, fbody, rarg) := defs[0]!
  let fty' ← withPath "type" (trans fty)
  let (lams, b) := peelLams fbody
  unless rarg < lams.size do return ← unsup s!"decreasing argument {rarg} is not bound by the leading lambdas"
  let outer := (← read).locals
  withLocalDecl (binderName fname) .default fty' fun fv => do
  withSourceLams lams (outer.push fv) 0 #[] fun as => do
    let P := as.extract 0 rarg
    let x := as[rarg]!
    let Q := as.extract (rarg + 1) as.size
    let xty ← liftMeta do whnf (← inferType x)
    let .const iname _ := xty.getAppFn | unsup "the decreasing argument is not of an inductive type"
    let some (.inductInfo iv) := (← getEnv).find? iname | unsup "the decreasing argument is not of an inductive type"
    if ← liftMeta (isProp xty) then return ← unsup "the decreasing argument is a proof"
    unless iv.numIndices == 0 do return ← unsup "the decreasing argument's inductive has indices"
    let idxPos : Array (Option Nat) := P.map fun _ => none
    let gpos := (changedParams fbody lams.size rarg 0).toArray.qsort (· < ·)
    let G := gpos.map (P[·]!)
    for i in [0:rarg] do
      unless gpos.contains i do
        let t ← liftMeta do instantiateMVars (← inferType P[i]!)
        if G.any (t.containsFVar ·.fvarId!) then
          failT "UNSUPPORTED_FEATURE" s!"argument {i} depends on an argument that recursive calls change"
    if G.any (xty.containsFVar ·.fvarId!) then
      failT "UNSUPPORTED_FEATURE" "the decreasing argument's type depends on an argument that recursive calls change"
    let C := xty
    let cLvl ← liftMeta (getLevel C)
    let RTy := mkForall `y .default C (mkForall `s .default C (mkSort .zero))
    withLocalDecl `R .default RTy fun Rv => do
    let accTy (R s : Expr) := mkApp3 (mkConst ``Acc [cLvl]) C R s
    let dsRef ← IO.mkRef (#[] : Array Expr)
    let motiveOf (R : Expr) : TransM Expr :=
      withLocalDecl `s .default C fun s => withLocalDecl `acc .default (accTy R s) fun acc =>
        accWalk fty' as.size rarg P idxPos gpos s s 0 #[] #[] fun _ fresh body => do
          bindFVars true #[s, acc] (← bindFVars false fresh body)
    let minorWith (R : Expr) (collect : Bool) (ds : Array Expr) : TransM Expr := do
      let motive ← motiveOf R
      withLocalDecl `s .default C fun s => do
        let hTy ← liftMeta <| withLocalDecl `y .default C fun y => do mkForallFVars #[y] (← mkArrow (mkApp2 R y s) (accTy R y))
        withLocalDecl `h .default hTy fun h => do
        let ihTy ← liftMeta <| withLocalDecl `y .default C fun y => withLocalDecl `hy .default (mkApp2 R y s) fun hy =>
          mkForallFVars #[y, hy] (mkApp2 motive y (mkApp2 h y hy))
        withLocalDecl `ih .default ihTy fun ih => do
        let baseF := (← getLCtx).getFVarIds
        let counter ← IO.mkRef 0
        accWalk fty' as.size rarg P idxPos gpos s s 0 #[] #[] fun vals fresh _ => do
          let site : AccSite := { f := fv.fvarId!, s, ih, R, nP := rarg, idxPos, gpos, expected := vals,
                                  hasIdx := false, nparams := iv.numParams, idxTy := mkSort .zero, idxLvl := .zero,
                                  fam := C, base := baseF, collect, dsRef, ds, counter, convoy := true,
                                  hidden := some (← IO.mkRef #[]) }
          let body ← withPath "body" (withReader (fun c => { c with locals := outer ++ #[fv] ++ vals, accSite := some site }) (trans b))
          bindFVars true #[s, h, ih] (← bindFVars true fresh body)
    let _ ← minorWith Rv true #[]
    let ds ← dsRef.get
    if ds.isEmpty then return ← unsup "no recursive call"
    let Rdef ← liftMeta <| withLocalDecl `y .default C fun y => withLocalDecl `s .default C fun sv => do
      mkLambdaFVars #[y, sv] (mkDisj (ds.toList.map fun d => d.beta #[y, sv]))
    let intro ← minorWith Rdef false ds
    let motive ← motiveOf Rdef
    let uM ← liftMeta do
      withLocalDecl `s .default C fun s => withLocalDecl `acc .default (accTy Rdef s) fun acc => do
        pure (← getLevel (← whnf (mkApp2 motive s acc))).normalize
    -- the termination obligation  ∀ Γ, ∀ s, Acc R s  over the locals Γ that R mentions (closed under
    -- the locals their types mention), in context order
    let wfBody ← liftMeta do
      let e ← withLocalDecl `s .default C fun s => mkForallFVars #[s] (accTy Rdef s)
      instantiateMVars e
    -- (the call relation may mention prerequisite hypotheses — a pending function in a recursive call's
    -- argument; the termination obligation is then a pending proof task over them, docs/TERMINATION.md §B-P)
    if wfBody.hasExprMVar then
      let hs ← match (← read).hyps with | some r => pure ((← r.get).map (·.1)) | none => pure #[]
      unless (← liftMeta (getMVars wfBody)).all hs.contains do
        return ← unsup "the call relation has unresolved metavariables"
    let lctx ← getLCtx
    let mut need : Std.HashSet FVarId := {}
    let mut todo := (collectFVars {} wfBody).fvarIds
    while !todo.isEmpty do
      let v := todo.back!
      todo := todo.pop
      if need.contains v then continue
      need := need.insert v
      if let some d := lctx.find? v then
        todo := todo ++ (collectFVars {} (← liftMeta (instantiateMVars d.type))).fvarIds
    if need.contains fv.fvarId! || need.contains Rv.fvarId! then return ← unsup "the call relation mentions the recursion"
    let gam := lctx.getFVars.filter fun v => need.contains v.fvarId!
    if gam.any fun v => (lctx.get! v.fvarId!).isLet then return ← unsup "the call relation mentions a let-bound local"
    let stmt ← liftMeta (mkForallFVars gam wfBody)
    let pre := (← read).declKey ++ "__rocq2lean_termination_"
    let wfE ← match (← read).hyps with
      | some ref =>
        let k := ((← ref.get).filter (·.2.startsWith pre)).size + 1
        hypFor ref (pre ++ toString k) stmt
      | none =>
        -- assembly: a termination obligation with a final theorem is that theorem
        match (← read).genv.consts[pre ++ "1"]? with
        | some thm => pure (mkConst thm (← levelsOf thm))
        | none => failT "UNSUPPORTED_FEATURE" "termination obligation required: recursive call on a term that is not a direct recursive constructor field (no hypothesis available)"
    let accRec := mkAppN (mkConst ``Acc.rec [uM, cLvl]) #[C, Rdef, motive, intro, x, mkApp (mkAppN wfE gam) x]
    let res := eraseBinderScopes (← bindFVars true as (mkAppN accRec (G ++ Q)))
    if res.containsFVar fv.fvarId! || res.containsFVar Rv.fvarId! then
      return ← unsup "recursive function escapes the supported call pattern"
    return res

/-- M6 course-of-values: `match z` on a subterm `z` with a known result `r_z : Motive' z` becomes
`I.rec params (λ z', Motive' z' → RET[z']) minors z r_z`, minor `k` binding `h : Motive' (C_k fs)`;
`h.2` is the chain `⟨r_{f₁}, …, PUnit.unit⟩` of the recursive fields' results (Below's ι-reduct), so a
recursive call on such a field `f_m` becomes `(proj₀ (proj₁^m h.2)).1 G' Q'` (`replaceRecCalls`,
lenient: other calls are left to the enclosing passes). -/
partial def transCaseCov (cs : CovSite) (rz : Expr) (iname : Name) (rv : RecursorVal) (params : Array Expr)
    (pctx : Array AName) (pret : IR.Term) (scrut' : Expr) (brs : Array (Array AName × IR.Term)) : TransM Expr := do
  unless rv.numIndices == 0 && pctx.size == 1 do
    failT "UNSUPPORTED_FEATURE" "course-of-values match on an indexed inductive"
  let sty ← liftMeta do whnf (← inferType scrut')
  let indLvls := sty.getAppFn.constLevels!
  let (motive, lvl) ← withLocalDecl `z .default sty fun z => do
    let ret ← withPath "return" (withReader (fun c => { c with locals := c.locals ++ #[z] }) (trans pret))
    let body ← liftMeta (mkArrow (cs.motive.beta #[z]) ret)
    let l ← liftMeta do instantiateLevelMVars (← getLevel body)
    return (← bindFVars true #[z] body, l.normalize)
  let recConst := mkConst (iname.str "rec") (lvl :: indLvls)
  let mut ty ← liftMeta do instantiateForall (← inferType recConst) (params.push motive)
  let mut minors : Array Expr := #[]
  for k in [0:rv.numMinors] do
    let .forallE _ minorTy rest _ ← liftMeta (whnf ty) | failT "TRANSLATION_FAILED" s!"{iname}.rec: missing minor {k}"
    let (bctx, bbody) := brs[k]!
    let nfields := rv.rules[k]!.nfields
    unless bctx.size == nfields do
      failT "UNSUPPORTED_FEATURE" s!"branch {k}: {bctx.size} binders for {nfields} fields (let-bound constructor arguments)"
    let minor ← minorTelescope minorTy nfields iname params fun fields recFields ihs res => do
      forallBoundedTelescope (← liftMeta (whnf res)) (some 1) fun hs _ => do
        let h := hs[0]!
        let mut rs : Array (Expr × Expr) := #[]
        let mut cur := Expr.proj ``PProd 1 h
        for y in recFields do
          rs := rs.push (y, .proj ``PProd 0 cur)
          cur := .proj ``PProd 1 cur
        let cs' := { cs with results := cs.results ++ rs }
        let body ← withPath s!"cov{k}"
          (withReader (fun c => { c with locals := c.locals ++ fields, cov := some cs' }) (trans bbody))
        let fieldIH ← rs.mapM fun (y, r) => do
          let yt ← liftMeta do whnf (← inferType y)
          return (y, Expr.proj ``PProd 0 r, yt.getAppArgs.extract cs.nparams yt.getAppArgs.size)
        let body ← replaceRecCalls cs.f cs.P cs.idxPos fieldIH cs.gpos cs.nparams body (lenient := true)
        bindFVars true (fields ++ ihs ++ hs) body
    minors := minors.push minor
    ty := rest.instantiate1 minor
  return mkApp (mkAppN recConst (params ++ #[motive] ++ minors ++ #[scrut'])) rz

/-- M6 mutual structural fixpoints over one (non-mutual, uniform) inductive `I`:

    fix f₀ P x Q₀ {struct x} := b₀ with … f_{n-1} P x Q_{n-1} {struct x} := b_{n-1} for f_j
    ↦ λ P x Q_j, (I.rec params (λ idx x, PProd (∀ Q₀, T₀) (… (∀ Q_{n-1}, T_{n-1}))) minors idx x).j Q_j
    minor_k = λ fields ihs, ⟨λ Q₀, b₀ₖ, …, λ Q_{n-1}, b_{n-1,k}⟩

All functions decrease on the same argument position with the same leading argument types (checked
on the translations). `b_jk` is branch k of `b_j` (a match on x), or all of `b_j` with matches on x
ι-reduced. A call `f_i P y rest` on a recursive field `y` becomes `(ih_y).i G' rest`. Leading
arguments that some call of the block changes (`G`, not indices) are generalized in every component
(`∀ G Q_j, T_j`), as for a single fixpoint; the others are unchanged. `.j` is the `PProd`
projection chain (`pprodProj`). -/
partial def transFixMutual (defs : Array (AName × IR.Term × IR.Term × Nat)) (fidx : Nat) : TransM Expr := do
  let n := defs.size
  let r := defs[0]!.2.2.2
  unless defs.all (·.2.2.2 == r) do
    failT "UNSUPPORTED_FEATURE" s!"mutual fixpoint ({n} functions): decreasing arguments at different positions"
  let peeled := defs.map fun (_, _, b, _) => peelLams b
  unless peeled.all (r < ·.1.size) do
    failT "UNSUPPORTED_FEATURE" s!"mutual fixpoint ({n} functions): decreasing argument not bound by the leading lambdas"
  let ftys ← defs.mapIdxM fun j (_, fty, _, _) => withPath s!"type{j}" (trans fty)
  let outer := (← read).locals
  withFixNames (defs.map (binderName ·.1)) ftys 0 #[] fun fvs => do
  let base := outer ++ fvs
  withSourceLams (peeled[0]!.1.extract 0 (r + 1)) base 0 #[] fun px => do
    let P := px.extract 0 r
    let x := px[r]!
    for j in [1:n] do
      for i in [0:r + 1] do
        let t ← withPath s!"def{j}.lam{i}"
          (withReader (fun c => { c with locals := base ++ px.extract 0 i }) (trans peeled[j]!.1[i]!.2))
        let t0 ← liftMeta do instantiateMVars (← inferType px[i]!)
        unless (← liftMeta (instantiateMVars t)) == t0 do
          failT "UNSUPPORTED_FEATURE" s!"mutual fixpoint: function {j} has a different type for argument {i}"
    let xty ← liftMeta do whnf (← inferType x)
    let idx0 := xty.getAppArgs.filter (P.contains ·)
    let gpos := ((List.range n).foldl (fun a j => changedParams defs[j]!.2.2.1 peeled[j]!.1.size r 0 a n) {}).toArray.qsort (· < ·)
      |>.filter fun i => !idx0.contains P[i]!
    let G := gpos.map (P[·]!)
    for i in [0:r] do
      unless gpos.contains i do
        let t ← liftMeta do instantiateMVars (← inferType P[i]!)
        if G.any (t.containsFVar ·.fvarId!) then
          failT "UNSUPPORTED_FEATURE" s!"argument {i} depends on an argument that recursive calls change"
    if G.any (xty.containsFVar ·.fvarId!) then
      failT "UNSUPPORTED_FEATURE" "the decreasing argument's type depends on an argument that recursive calls change"
    -- component types C_j = ∀ G Q_j, T_j over the other leading arguments and x
    let comps ← (List.range n).toArray.mapM fun j =>
      withSourceLams peeled[j]!.1 base (r + 1) px fun as => do
        let T ← liftMeta (instantiateForall ftys[j]! as)
        bindFVars false (G ++ as.extract (r + 1) as.size) T
    let some (tgt, tidx) := (← read).genv.inds.toList.findSome? fun (_, t) =>
        (t.types.findIdx? (xty.getAppFn.isConstOf ·)).map (t, ·)
      | failT "UNSUPPORTED_FEATURE" s!"mutual fixpoint ({n} functions): the decreasing argument is not of a translated inductive"
    if tgt.nonUniform > 0 || tgt.types.size > 1 then
      failT "UNSUPPORTED_FEATURE" s!"mutual fixpoint ({n} functions) over a mutual or non-uniform inductive"
    let iname := tgt.types[tidx]!
    let rv ← recursorOf iname
    let mut outerCases : Array (Option (Array (Array AName × IR.Term))) := #[]
    for (lams, b) in peeled do
      match b with
      | .case cind cnpar _ _ _ _ _ (.rel sj) brs =>
        if sj == lams.size - 1 - r then
          unless (← lookupInd cind).types[cind.idx]! == iname && rv.numParams == cnpar && brs.size == rv.numMinors do
            failT "EXPORT_VALIDATION_FAILED" "match metadata disagrees with the recursor"
          outerCases := outerCases.push (some brs)
        else outerCases := outerCases.push none
      | _ => outerCases := outerCases.push none
    let xargs := xty.getAppArgs
    let params := xargs.extract 0 rv.numParams
    let idx := xargs.extract rv.numParams xargs.size
    unless idx.all (P.contains ·) && idx.toList.eraseDups.length == idx.size do
      failT "UNSUPPORTED_FEATURE" "indices of the decreasing argument are not distinct earlier parameters"
    let idxPos : Array (Option Nat) := P.map fun p => idx.findIdx? (· == p)
    let indLvls := xty.getAppFn.constLevels!
    let prodTy ← liftMeta (mkPProdTy comps)
    let u := (← liftMeta do instantiateLevelMVars (← getLevel prodTy)).normalize
    let motive ← bindFVars true (idx.push x) prodTy
    unless rv.levelParams.length == indLvls.length + 1 do
      failT "UNSUPPORTED_FEATURE" s!"mutual fixpoint ({n} functions) on {iname}, which has no large elimination"
    let compLams ← comps.mapM fun c => bindFVars true (idx.push x) c
    let recConst := mkConst (iname.str "rec") (u :: indLvls)
    let mut ty ← liftMeta do instantiateForall (← inferType recConst) (params.push motive)
    let mut minors : Array Expr := #[]
    for k in [0:rv.numMinors] do
      let .forallE _ minorTy rest _ ← liftMeta (whnf ty) | failT "TRANSLATION_FAILED" s!"{iname}.rec: missing minor {k}"
      let nfields := rv.rules[k]!.nfields
      for oc in outerCases do
        if let some brs := oc then
          unless brs[k]!.1.size == nfields do
            failT "UNSUPPORTED_FEATURE" s!"branch {k}: let-bound constructor arguments"
      let minor ← minorTelescope minorTy nfields iname params fun fields recFields ihs _ => do
        let fieldIH ← (recFields.zip ihs).mapM fun (y, ih) => do
          let yt ← liftMeta do whnf (← inferType y)
          return (y, ih, yt.getAppArgs.extract rv.numParams yt.getAppArgs.size)
        let xk := mkAppN (mkConst tgt.ctors[tidx]![k]! indLvls) (params ++ fields)
        let xkIdx ← liftMeta do
          let t ← whnf (← inferType xk)
          pure (t.getAppArgs.extract rv.numParams t.getAppArgs.size)
        let cks := compLams.map (·.beta (xkIdx.push xk))
        let vals ← (List.range n).toArray.mapM fun j => do
          let nq := peeled[j]!.1.size - r - 1
          forallBoundedTelescope cks[j]! (some (G.size + nq)) fun gqs _ => do
            unless gqs.size == G.size + nq do failT "TRANSLATION_FAILED" "minor component has fewer binders than the function"
            let gs := gqs.extract 0 G.size
            let qs := gqs.extract G.size gqs.size
            let P' := Id.run do
              let mut P' := P
              for i in gpos, g in gs do P' := P'.set! i g
              for i in [0:P.size] do
                if let some jj := idxPos[i]! then P' := P'.set! i xkIdx[jj]!
              return P'
            let body ← match outerCases[j]! with
              | some brs =>
                withPath s!"def{j}.branch{k}"
                  (withReader (fun c => { c with locals := base ++ P' ++ #[xk] ++ qs ++ fields }) (trans brs[k]!.2))
              | none =>
                withPath s!"def{j}.minor{k}" (withReader (fun c =>
                  { c with locals := base ++ P' ++ #[xk] ++ qs, iota := c.iota.push (xk, k, fields) }) (trans peeled[j]!.2))
            let body ← replaceRecCallsMutual (fvs.map (·.fvarId!)) P' idxPos fieldIH gpos rv.numParams body
            bindFVars true (gs ++ qs) body
        let packed ← liftMeta (mkPProdVal cks vals)
        bindFVars true (fields ++ ihs) packed
      minors := minors.push minor
      ty := rest.instantiate1 minor
    let recApp := mkAppN recConst (params ++ #[motive] ++ minors ++ idx ++ #[x])
    withSourceLams peeled[fidx]!.1 base (r + 1) px fun as => do
      let res ← bindFVars true as (mkAppN (pprodProj recApp fidx n) (G ++ as.extract (r + 1) as.size))
      if fvs.any (res.containsFVar ·.fvarId!) then
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
    | none =>
      -- statement mode, pending validation: an unproved prerequisite is a hypothesis of its statement,
      -- a pending definition its artifact applied to fresh hypotheses
      match (← read).hyps, genv.leafStmt[c]?, genv.pendingDefs[c]? with
      | some ref, some (sname, sh), _ =>
        unless kp == 0 do failT "UNSUPPORTED_FEATURE" s!"universe-polymorphic proof task {c} referenced in a pending declaration"
        let stmtE ← applyHyps ref (mkConst sname (← levelsOf sname)) sh
        hypFor ref c stmtE
      | some ref, none, some (pname, ph) =>
        unless kp == 0 do failT "UNSUPPORTED_FEATURE" s!"universe-polymorphic pending definition {c}"
        applyHyps ref (mkConst pname (← levelsOf pname)) ph
      | _, _, _ => failT "TRANSLATION_FAILED" s!"reference to constant {c}, which has no accepted translation"
  | .ind i u =>
    let t ← lookupInd i
    checkTemplateArgs i.mind t args
    let e := mkConst t.types[i.idx]! (← univArgs i.mind t u args t.types[i.idx]!)
    pendingIndArgs t e
  | .construct i c u =>
    let t ← lookupInd i
    let cs := t.ctors[i.idx]!
    unless c < cs.size do
      failT "EXPORT_VALIDATION_FAILED" s!"constructor index {c} out of range for {i.mind}"
    checkTemplateArgs i.mind t args
    pendingIndArgs t (mkConst cs[c]! (← univArgs i.mind t u args cs[c]!))
  | _ => trans f

end

/-- Translate a closed term and check that no free or meta variable escapes (in pending validation,
only the registered hypothesis metavariables may remain). -/
def transClosed (t : IR.Term) : TransM Expr := do
  -- binder names without macro scopes (hygienic names inherited from Lean's own declarations, e.g.
  -- the recursor types' `a✝`, do not survive the report's string round trip; names carry no meaning)
  let e := eraseBinderScopes (← instLevelMVars (← trans t))
  if e.hasFVar then failT "TRANSLATION_FAILED" "translated term has escaping free variables"
  if e.hasExprMVar then
    let allowed ← match (← read).hyps with
      | some ref => pure ((← ref.get).map (·.1))
      | none => pure #[]
    let ms ← liftMeta (getMVars e)
    unless ms.all allowed.contains do
      failT "TRANSLATION_FAILED" "translated term has unresolved metavariables"
  return e

/-- B: the unfolding equation of a termination-lowered fixpoint at the top of a constant's body,
`c := λ outer, fix f args := B`:  `∀ outer args, self outer args = B[f := self outer]`, with `self` the
translated constant (the pending artifact applied to its hypotheses) and `B` the source body (the
same preparation `transFix` applies), translated as an ordinary term. `none` when the body is not of
that shape. -/
def transUnfoldEq (body : IR.Term) (self : Expr) : TransM (Option Expr) := do
  let (olams, fx) := peelLams body
  let .fix defs 0 := fx | return none
  unless defs.size == 1 do return none
  let bodies := (← read).genv.irBodies
  let need := defs.reverse.map (·.2.2.2 + 1)
  let defs := defs.map fun (n, ty, b, r) => (n, ty, inlineRecArgs bodies need b, r)
  let defs := if (← read).genv.stmtMode then defs.map fun (n, ty, b, r) => (n, ty, b.zetaFixLets 0 defs.size, r) else defs
  let (_, fty, fbody, _) := defs[0]!
  let e ← withSourceLams olams #[] 0 #[] fun outs => do
    let selfO := mkAppN self outs
    let fty' ← withReader (fun c => { c with locals := outs }) (withPath "unfold type" (trans fty))
    let (flams, fb) := peelLams fbody
    withSourceLams flams (outs.push selfO) 0 #[] fun as => do
      let rhs ← withReader (fun c => { c with locals := outs.push selfO ++ as }) (withPath "unfold" (trans fb))
      let T ← liftMeta (instantiateForall fty' as)
      let lvl ← liftMeta (getLevel T)
      liftMeta (mkForallFVars (outs ++ as) (mkApp3 (mkConst ``Eq [lvl]) T (mkAppN selfO as) rhs))
  let e := eraseBinderScopes (← instLevelMVars e)
  if e.hasFVar then failT "TRANSLATION_FAILED" "unfolding equation has escaping free variables"
  return some e

def runTrans {α} (genv : GEnv) (x : TransM α) (globalLevels : Std.HashMap String Level := {})
    (polyLevels : Array Level := #[]) (factReduce : Bool := false) (admitLevels : Array String := #[])
    (lowerShared : Bool := false) (hyps : Option (IO.Ref (Array (MVarId × String))) := none)
    (declKey : String := "") (hypExact : Bool := false)
    (sharedFresh : Option (IO.Ref (Array (LMVarId × String))) := none)
    (propCoerce : Option (IO.Ref Nat) := none) (phantomLower : Bool := false) :
    MetaM (Except TransError α) :=
  (x { genv, globalLevels, polyLevels, factReduce, admitLevels, lowerShared, hyps, declKey, hypExact, sharedFresh, propCoerce, phantomLower }).run

/-- Pending validation: the hypothesis metavariables (in creation order) become binders of the
declaration, `∀ hs, e` (`lam := false`) or `fun hs => e` (Lean's binding abstraction handles their
mutual dependencies; nothing is assigned). -/
def abstractHyps (hs : Array (MVarId × String)) (e : Expr) (lam : Bool) : MetaM Expr := do
  let xs := hs.map fun (m, _) => mkMVar m
  if lam then mkLambdaFVars xs e else mkForallFVars xs e

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

/-- R2B-S applicability: `l` occurs in the source type `∀ xs, Sort s` only in the result sort `s`
(no binder type mentions it): the declaration is a type (former) whose own sort is at `l`. -/
partial def onlyInResultSort (ty : IR.Term) (l : String) : Bool :=
  match ty with
  | .prod _ a b => !(globalsOf a).contains l && onlyInResultSort b l
  | .sort _ => true
  | _ => !(globalsOf ty).contains l

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

/-- Coherence by unification: every per-occurrence metavariable of a shared level `l` still free after
translation is the declaration's own variable for `l` (coherence where typing imposes nothing else). -/
def rebindShared (ref : IO.Ref (Array (LMVarId × String))) (gl : Std.HashMap String Level)
    (f : IR.UniverseFacts := { levels := #[], relations := #[] }) : MetaM Unit := do
  -- one pass: the class (root metavariable) of every occurrence and the source levels it carries
  let occs ← ref.get
  let mut roots : Array (LMVarId × String) := #[]
  let mut cls : Std.HashMap LMVarId (Array String) := {}
  for (m, l) in occs do
    if let .mvar r ← instantiateLevelMVars (.mvar m) then
      roots := roots.push (r, l)
      let cur := cls.getD r #[]
      unless cur.contains l do cls := cls.insert r (cur.push l)
  let mut done : Std.HashSet LMVarId := {}
  for (r, l0) in roots do
    if done.contains r then continue
    done := done.insert r
    -- (still free: an earlier assignment in this pass may have bound it)
    unless (← instantiateLevelMVars (.mvar r)) == .mvar r do continue
    let c := cls.getD r #[l0]
    -- (one class of occurrences for several shared levels, identified by typing: it is the level lying
    -- below every other level of the class, as R3G chooses; the others' arguments are then R3-checked)
    let low? := c.find? fun x => c.all fun y => x == y || entails f x y 0
    -- (a class whose lowest level is not an own level is left free: R3G names it after that level)
    if let some lo := low? then
      unless gl.contains lo do continue
    let l := low?.getD l0
    if let some v := gl[l]? then
      let vi ← instantiateLevelMVars v
      -- (the own level already solved through this occurrence, `?l := max (…, ?occ)`: the occurrence is
      -- the parameter `u_l` itself, so `l` denotes `max (…, u_l)`, its R2F reading; never a cycle)
      if (vi.collectMVars {}).contains r then
        unless vi == .mvar r do assignLevelMVar r (.param (levelParamName l))
      else assignLevelMVar r v

/-- Rule R (docs/COHERENCE_READINGS.md): the levels `σ` and `τ` over the own levels `own` (`u_m` read as the
source level `m`, a constant `c` as `Set + c`) are equal at every model of the source facts: each summand
of either side lies below some summand of the other (entailed by the native graph). -/
def equalAtModels (f : IR.UniverseFacts) (own : Array String) (σ τ : Level) : Bool := Id.run do
  let summ (x : Level) : Option (List (String × Nat)) := do
    let (c, ps) ← levelNF x.normalize
    let ps ← ps.mapM fun (p, k) => (own.find? (levelParamName · == p)).map (·, k)
    some (("Set", c) :: ps)
  let leq (lhs rhs : List (String × Nat)) : Bool :=
    lhs.all fun (a, i) => (a == "Set" && i == 0) || rhs.any fun (b, j) =>
      if i ≤ j then a == b || entails f a b 0 || a == "Set" else entails f a b (i - j)
  match summ σ, summ τ with
  | some a, some b => leq a b && leq b a
  | _, _ => false

/-- Universe obligation (docs/UNIVERSE_TRANSLATION.md, rule R3) for one reference: the target
universe argument `σ` for the referenced constant's parameter standing for source level `l`. -/
def checkInstantiation (f : IR.UniverseFacts) (own : Array String) (l : String) (σ : Level)
    (body : Std.HashMap String Level := {}) (cAdmit : Bool := false) (ownAdmit : Array String := #[])
    (allowLift : Bool := false) (allowLower : Bool := false) (copyArg : Bool := false) : Except String Unit := do
  -- R8: a motive-level parameter stands for (image of the source level) + 1; `shift` converts the
  -- referring declaration's level for `l` into the referenced parameter's convention
  let dAdmit := ownAdmit.contains l
  if dAdmit && !cAdmit then
    throw s!"coherence: source level {l} is a motive level of the referring declaration but not of the referenced one"
  let shift (x : Level) : Level := if cAdmit && !dAdmit then x.succ else x
  if let some s := body[l]? then
    if σ.normalize == (shift s).normalize then return
    -- Rule R: an argument equal to the solution (or R2F image) at every model of the source facts (its
    -- summands are R3-checked below, as every argument's)
    if !cAdmit && !dAdmit && equalAtModels f own σ s then pure () else
    -- R3↓: as for a shared level, a lower argument (checked below not to raise)
    unless allowLower do
      throw s!"coherence: source level {l} is a proof-local level of the referring declaration, solved as {s}; the argument must be the same, not {σ}"
  -- (R-CARRIER P2: an argument for a copy of `l` stands for an argument `a ≤ l`, not for a shared `l`)
  else if own.contains l && !copyArg then
    if σ.normalize == (shift (.param (levelParamName l))).normalize then return
    -- Rule R (docs/COHERENCE_READINGS.md): an argument `max (u_l, s₁, …)` whose other summands pass R3
    -- below (`m + k ≤ l`, `Set + c ≤ l` entailed) equals `l` at every model of the source facts: it is a
    -- referenced declaration's R2F reading of `l`, not a specialization. Not for motive-level (R8)
    -- parameters, where the argument is `u_l + 1`.
    -- (general form, `equalAtModels`: the argument equals `l` at every model of the source facts, e.g. a
    -- summand `u_m` of a source-equal level `m`)
    let reading := !cAdmit && !dAdmit && equalAtModels f own σ (.param (levelParamName l))
    if reading then pure () else
    -- R3↓ (cumulativity tier only, reported per declaration): a lower argument, checked below not to
    -- raise (Set + c ≤ l and m + k ≤ l entailed): Rocq used the reference at l with arguments of
    -- lower levels by cumulativity, Lean instantiates it at their level
    unless allowLower do
      throw s!"coherence: source level {l} is shared with the referring declaration, so its argument must be u_{l}, not {σ}"
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
partial def ownLevelInterp (f : IR.UniverseFacts) (own : Array String) (minimal : Std.HashSet String := {})
    (decoupled : Std.HashSet (String × String) := {}) :
    Std.HashMap String Level := Id.run do
  let leq (a b : String) := f.rel a b == "le" || f.rel a b == "lt"
  let rec go (fuel : Nat) (l : String) : Level :=
    match fuel with
    | 0 => .param (levelParamName l)
    | fuel + 1 => Id.run do
      let mut acc : Level := .param (levelParamName l)
      -- R3G-F (docs/RESULT_SORT_LEVELS.md §2): a result-sort implicit level stands for an argument
      -- `a ≤ l` (R3 at every use); it keeps the levels above it raised but is not itself read through
      -- the levels below it (its lower bounds, as R-SPLIT's copies)
      if minimal.contains l then return acc
      for m in own do
        if m == l || !leq m l then continue
        -- R-CARRIER P1: a parameter carrier is not raised by its own block's other levels
        if decoupled.contains (l, m) then continue
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
    (body : Std.HashMap String Level := {}) (ownAdmit : Array String := #[]) (allowLift : Bool := false)
    (allowLower : Bool := false) :
    Except String Nat := do
  let mut n := 0
  for (c, ls) in constOccurrences e do
    if let some globals := genv.constGlobals[c]? then
      -- R6: the first universe arguments of a polymorphic constant are its instance, not R3 obligations
      let ls := ls.drop (genv.polyByTarget[c]?.getD 0)
      unless globals.size == ls.length do throw s!"{c}: {ls.length} universe arguments for {globals.size} parameters"
      let copyPos := (genv.copyPositions[c]?).getD #[]
      for l in globals, σ in ls, k in List.range globals.size do
        if genv.templateLevels.contains l then continue      -- R5, not R3
        let cAdmit := (genv.admitting[c]?.getD #[]).contains l
        -- R-CARRIER P2: at a copy position the shared-level coherence does not apply (R3 entailment does)
        -- Rule H (docs/COHERENCE_READINGS.md §5): a reference to a proof task's statement (the type of a
        -- generated prerequisite hypothesis) is instantiated where the prerequisite is used; its argument
        -- for a shared level may lie below it (R3↓: no raising, checked below), on every tier
        let hypArg := genv.leafStmtTargets.contains c
        match checkInstantiation genv.facts own l σ body cAdmit ownAdmit allowLift (allowLower || hypArg) (copyPos.getD k false) with
        | .ok () => n := n + 1
        | .error msg => throw s!"reference to {c}: {msg}"
  return n

/-- Summands of a level (`max` flattened). -/
partial def levelSummands : Level → Array Level
  | .max a b => levelSummands a ++ levelSummands b
  | l => #[l]

/-- M6 bounded universe solver for one postponed constraint `max(As) = max(Bs)`: after removing the
offset common to every summand, a bare level metavariable `?v` among `As` that does not occur in `Bs`
gets the candidates `max(Bs ∖ As)` (instantiation at the other side's level, as R3↓), `0`, then each
summand of `Bs`; a candidate (never mentioning `?v`) is kept when Lean's level unification accepts the
constraint with nothing left postponed. Returns the recorded assignment, or none. -/
def solveMaxEq (a b : Level) : MetaM (Option String) := do
  let as := levelSummands a.normalize
  let bs := levelSummands b.normalize
  let k := (as ++ bs).foldl (fun m x => min m x.getOffset) (as ++ bs)[0]!.getOffset
  let shift (x : Level) : Level := x.getLevelOffset.addOffset (x.getOffset - k)
  let as := as.map shift
  let bs := bs.map shift
  let some v := as.find? (fun x => x.isMVar && !bs.any fun y => y.any (· == x)) | return none
  let rest := as.filter (· != v)
  let missing := bs.filter fun x => !rest.contains x
  let c1 := if missing.isEmpty then Level.zero else missing.foldl (init := missing[0]!) fun acc x => mkLevelMax' acc x
  for c in #[c1.normalize, .zero] ++ bs do
    if c.any (· == v) then continue
    let saved ← saveState
    assignLevelMVar v.mvarId! c
    let ok ← isLevelDefEq a b
    if ok && (← getPostponed).isEmpty then return some s!"{v} := {c} (from {a} = {b})"
    saved.restore
  return none

/-- A postponed constraint `max(As, ?v) = B` is unsatisfiable (not merely beyond the solver) when a
parameter summand `p + k` of `As` is below no summand `p + k'` (`k ≤ k'`) of `B`: `p` is unbounded. -/
def unsatMaxEq (a b : Level) : Bool :=
  let bs := levelSummands b.normalize
  (levelSummands a.normalize).any fun x => match x.getLevelOffset with
    | .param p => !bs.any fun y => y.getLevelOffset == .param p && x.getOffset ≤ y.getOffset
    | _ => false

/-- M6: run the bounded solver on Lean's postponed level constraints (`solveMaxEq`, both
orientations); returns the recorded assignments and the constraints left, each classified as
unsatisfiable or as a solver limitation. -/
def solvePostponedLevels : MetaM (Array String × Array String) := do
  let ps ← getPostponed
  setPostponed {}
  let mut log : Array String := #[]
  let mut left : Array String := #[]
  for e in ps.toArray do
    let lhs ← instantiateLevelMVars e.lhs
    let rhs ← instantiateLevelMVars e.rhs
    let saved ← saveState
    if (← isLevelDefEq lhs rhs) && (← getPostponed).isEmpty then continue
    saved.restore
    match ← solveMaxEq lhs rhs with
    | some s => log := log.push s
    | none => match ← solveMaxEq rhs lhs with
      | some s => log := log.push s
      | none =>
        let unsat := unsatMaxEq lhs rhs || unsatMaxEq rhs lhs
        left := left.push s!"{if unsat then "unsatisfiable" else "solver limitation"}: {lhs} = {rhs}"
  return (log, left)

/-- Solve the universe metavariables introduced at references to generalized constants:
type-check with Lean's checker (which unifies universe levels; terms are not changed) and
unify the value's type with the declared type; any level left unconstrained is set to `0`.
The kernel re-checks the result. -/
def solveLevels (ty val : Expr) (dflt : LMVarId → MetaM Level := fun _ => pure .zero) (beforeDefault : MetaM Unit := pure ())
    (solve : Bool := false) :
    MetaM (Expr × Expr × Array String × List Name × Expr × Expr × List Level) := do
  let mut diags : Array String := #[]
  setPostponed {}      -- constraints left by earlier (failed) attempts are not this declaration's
  try Meta.check ty catch e => diags := diags.push s!"Meta.check type: {← e.toMessageData.toString}"
  try Meta.check val catch e => diags := diags.push s!"Meta.check value: {← e.toMessageData.toString}"
  try
    unless ← withTransparency .all <| isDefEq (← inferType val) ty do
      diags := diags.push "value type not unified with the declared type by Meta.isDefEq"
  catch e => diags := diags.push s!"isDefEq: {← e.toMessageData.toString}"
  -- M6 (last tiers only): the bounded solver on postponed `max` constraints, recorded
  if solve then
    let (asg, left) ← solvePostponedLevels
    diags := diags ++ asg.map ("solver: " ++ ·) ++ left.map ("solver: " ++ ·)
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

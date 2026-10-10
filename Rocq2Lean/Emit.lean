import Lean
import Rocq2Lean.IR
import Rocq2Lean.Kernel
import Rocq2Lean.Translate
import Rocq2Lean.Bootstrap

/-!
# Declaration emission

Processes the exported declarations in dependency order. Each one ends in exactly one status:

* `BOOTSTRAP_RESOLVED` — realised by a verified bootstrap rule;
* `TRANSLATED_AND_CHECKED` — translated and accepted by the Lean kernel (`addChecked`);
* `BLOCKED_SOURCE_BODY` — opaque body unavailable, or a genuine source assumption;
* `BLOCKED_DEPENDENCY` — a dependency did not succeed (the dependency path is recorded);
* `UNSUPPORTED_FEATURE`, `TRANSLATION_FAILED`, `EXPORT_VALIDATION_FAILED`, `KERNEL_REJECTED`,
  `AUDIT_REJECTED` — see `docs/SUPPORT_PROFILE.md`.

Nothing is ever added as an axiom, and a failed declaration is never replaced.
-/

namespace Rocq2Lean

open Lean Meta

structure DeclResult where
  source : String
  kind : String
  status : String
  rule : String := ""
  target : Option Name := none
  targetKind : String := ""
  message : String := ""
  path : List String := []
  blockedBy : Array String := #[]
  /-- Accepted target type and value, for the independent structural audit. -/
  targetType : Option Expr := none
  targetValue : Option Expr := none
  /-- Accepted constructor names and types (generated inductives). -/
  targetCtors : Array (Name × Expr) := #[]
  /-- Universe parameters (generalized source global levels). -/
  levelParams : List Name := []
  /-- Number of parameters (generated inductives). -/
  numParams : Nat := 0
  /-- Universe solving: diagnostics, number of defaulted levels, references checked (rule R3). -/
  levelDiagnostics : Array String := #[]
  levelDefaults : Nat := 0
  universeChecks : Nat := 0
  /-- Defaulted (residual) universe levels: the fresh parameters standing for them and the
  declaration's type/value with those parameters, which the kernel accepted (justification). -/
  residualParams : List Name := []
  residualDefaults : List Level := []
  /-- Generated inductives with level parameters: whether the source is template polymorphic, and
  for each template level the parameter (regular order) whose sort binds it (R5). -/
  isTemplate : Bool := false
  /-- Own source levels solved rather than generalized, with their solutions (R2S/R2B). -/
  bodyLevels : Array (String × Level) := #[]
  /-- Source levels of the universe parameters, in parameter order (R3 at references). -/
  paramLevels : Array String := #[]
  primitiveRecord : Bool := false
  /-- Inductive declarations: reference levels left unconstrained by typing, set to their least
  R3-admissible value 0 (R3″; every universe argument is R3-checked). -/
  minimalLevels : Nat := 0
  templateParams : Array (String × Nat) := #[]
  residualType : Option Expr := none
  residualValue : Option Expr := none
  /-- R6: number of universe variables of a universe-polymorphic source constant; they are the
  first universe parameters, `v_0 … v_{k-1}`. -/
  polyParams : Nat := 0
  /-- R2⁺: accepted on the retry with fact-reduced source universes. -/
  factReduced : Bool := false
  /-- R3G: source levels of referenced declarations that occur in the type only implicitly (through
  the reference) and that typing leaves free: universe parameters `u_l`, like explicit type levels. -/
  implicitLevels : Array String := #[]
  /-- R2F-c: own (explicit type and implicit) levels read through the fact interpretation
  `ι l = max (u_l, ι m + k …)` over the native facts among them (as R2F for inductives). -/
  levelInterp : Array (String × Level) := #[]
  /-- R8: motive levels translated as sort levels (`Type@{l} ↦ Sort u_l`, admitting Prop). -/
  admittingLevels : Array String := #[]
  /-- Accepted in the cumulativity tier (R3↑ lifting, R2B-P Prop offset), after the strict rules
  rejected the declaration. -/
  cumulativity : Bool := false
  /-- R2B-P: proof-local levels whose native `Set < m` was checked as `Set ≤ m`, with their solutions;
  each must be a valid Rocq instance of the source declaration (verify: Rocq kernel re-check). -/
  r2bpLevels : Array (String × Level) := #[]
  /-- R2B-P levels that occur in the declaration's type (a specialization of the source statement). -/
  r2bpInType : Array String := #[]
  /-- R2B-S: levels of the declaration's own result sort solved with `Set < l` read as `Set ≤ l`
  (a type definition at the level of its value), with their solutions. -/
  sortLevels : Array (String × Level) := #[]
  /-- M6: constants δ-inlined in the body (`Set`-motive constants used at a `Prop` family). -/
  deltaInlined : Array String := #[]
  /-- R3↓: accepted with references instantiated below shared levels (cumulativity tier). -/
  universeLowered : Bool := false
  /-- M6: a non-template inductive with plain universe parameters (`u_l` for each level, no R2F
  fact interpretation; tried first, the more general translation). -/
  plainLevels : Bool := false
  deriving Inhabited

def DeclResult.ok (r : DeclResult) : Bool :=
  r.status == "TRANSLATED_AND_CHECKED" || r.status == "BOOTSTRAP_RESOLVED"

/-- Source checking flags that the pilot accepts: everything checked, no impredicative Set, no UIP. -/
def relaxedFlags (native : Json) : Array String := Id.run do
  let flags := (native.getObjVal? "typing_flags").toOption.getD .null
  let get (k : String) : Option Bool := (flags.getObjValAs? Bool k).toOption
  let mut bad := #[]
  for k in ["check_guarded", "check_positive", "check_universes", "check_eliminations"] do
    if get k != some true then bad := bad.push k
  for k in ["impredicative_set", "allow_uip"] do
    if get k != some false then bad := bad.push k
  return bad

private def fromTransError (base : DeclResult) (e : TransError) : DeclResult :=
  { base with status := e.status, message := e.msg, path := e.path.reverse }

/-- Dependencies that are missing or failed. -/
private def blockedDeps (results : Std.HashMap String DeclResult) (deps : Array String) :
    Array String × Array String :=
  deps.foldl (init := (#[], #[])) fun (missing, failed) d =>
    match results[d]? with
    | none => (missing.push d, failed)
    | some r => if r.ok then (missing, failed) else (missing, failed.push d)

/-- Global levels of an inductive block (single body): arity and constructor types, sorted. -/
def globalsOfInd (i : IR.InductiveDecl) : Array String :=
  (i.bodies.foldl (fun acc (b : IR.OneInd) => b.ctors.foldl (fun acc c => globalsOf c.type acc) (globalsOf b.type acc)) {}).toArray.qsort (· < ·)

/-- Global levels of a constant that are generalized: those of its type (sorted); proof-local
levels of the body are solved instead (R2B). -/
def globalsOf' (c : IR.ConstantDecl) : Array String :=
  (globalsOf c.type).toArray

/-- The target declaration of a constant, by target kind. -/
def mkConstDecl (name : Name) (kind : String) (lps : List Name) (ty val : Expr) : MetaM Declaration := do
  match kind with
  | "def" =>
    let h := ReducibilityHints.regular (getMaxHeight (← getEnv) val + 1)
    return .defnDecl { name, levelParams := lps, type := ty, value := val, hints := h, safety := .safe, all := [name] }
  | "theorem" => return .thmDecl { name, levelParams := lps, type := ty, value := val, all := [name] }
  | _ => return .opaqueDecl { name, levelParams := lps, type := ty, value := val, isUnsafe := false, all := [name] }

/-- Justification of defaulted universe levels (docs/UNIVERSE_TRANSLATION.md, R3'): the declaration
with each residual level as a fresh universe parameter must be accepted by the kernel, i.e. it is
well typed for *every* value of those levels, so the default `0` chooses nothing. -/
def justifyResiduals (name : Name) (kind : String) (lps resid : List Name) (gty gval : Expr) :
    MetaM (Option String) := do
  if resid.isEmpty then return none
  match ← checkOnly (← mkConstDecl name kind (lps ++ resid) gty gval) with
  | .accepted => return none
  | .rejected msg => return some s!"defaulted universe level(s) {resid} not justified: the declaration is not valid for every value ({msg})"

def processConstant (genv : GEnv) (results : Std.HashMap String DeclResult) (c : IR.ConstantDecl)
    (factReduce : Bool := false) (interp : Bool := false) (admit : Bool := false) (cumul : Bool := false)
    (extraOwn : Array String := #[]) (discover : Bool := false) (lower : Bool := false) (delta : Bool := false) :
    MetaM DeclResult := do
  let base : DeclResult := { source := c.name, kind := "constant", status := "" }
  let (missing, failed) := blockedDeps results (c.typeDeps ++ c.bodyDeps)
  unless missing.isEmpty do
    return { base with status := "EXPORT_VALIDATION_FAILED",
                       message := s!"dependencies absent from the export: {missing}", blockedBy := missing }
  unless failed.isEmpty do
    return { base with status := "BLOCKED_DEPENDENCY", message := s!"failed dependencies: {failed}",
                       blockedBy := failed }
  let bad := relaxedFlags c.native
  unless bad.isEmpty do
    return { base with status := "AUDIT_REJECTED", message := s!"source declared with relaxed checking: {bad}" }
  -- R6 (docs/UNIVERSE_TRANSLATION.md): the universe variables of a polymorphic constant become its
  -- first Lean universe parameters `v_i`; Rocq's constraints among them are not transported: the
  -- kernel checks the body for *every* value of the parameters (which may reject a body that needs
  -- a constraint, never accepts one that is ill-typed for some instance).
  let polyNames : List Name := match c.universes with
    | .polymorphic names _ => (List.range names.size).map polyParamName
    | _ => []
  let polyLvls : Array Level := (polyNames.map Level.param).toArray
  match c.bodyState, c.body with
  | "assumption", _ =>
    return { base with status := "BLOCKED_SOURCE_BODY",
                       message := "genuine source assumption; the pilot admits no source axioms" }
  | "unavailable", _ =>
    return { base with status := "BLOCKED_SOURCE_BODY", message := "body not available in the export" }
  | "unsupported_primitive", _ =>
    return { base with status := "UNSUPPORTED_FEATURE", message := "primitive or symbol constant" }
  | st, some body =>
    -- M6 (last tier): δ-inline `Set`-motive constants (`Prop ≤ Set` at a family argument)
    let (body, inlined) := if delta then inlineConsts genv.irBodies genv.setMotive body else (body, {})
    if delta && inlined.isEmpty then
      return { base with status := "UNSUPPORTED_FEATURE", message := "no Set-motive constant to inline" }
    let inlinedA := inlined.toArray.qsort (· < ·)
    unless st == "transparent" || st == "opaque_present" || st == "sealed_implementation" do
      return { base with status := "EXPORT_VALIDATION_FAILED", message := s!"unknown body state '{st}'" }
    let name := targetName c.name
    if (← getEnv).contains name then
      return { base with status := "TRANSLATION_FAILED", message := s!"target name {name} already in use" }
    -- R2S: every own global level (type and body) starts as a level metavariable; references to a
    -- declaration sharing a source level use that variable (coherence by construction). After
    -- Lean's unifier has identified the levels typing forces together, the type levels still free
    -- become universe parameters `u_l`; the others are *solved* (σ l over the parameters), and the
    -- native facts among the declaration's levels must hold for the solution (R2S/R2B obligation).
    -- Body-only levels left free default to their minimal model (R2B, justified by R3′).
    -- R3G: implicit levels found by a discovery pass (`extraOwn`) are own type levels from the start
    let explicitTy := (globalsOf c.type).toArray
    let typeLevels := (explicitTy ++ extraOwn).toList.eraseDups.toArray.qsort (· < ·)
    -- R8: motive levels of the type (only when requested; see the translation ladder)
    let admitLv := if admit then (motiveLevels c.type).filter explicitTy.contains else #[]
    let own := ((globalsOf body (globalsOf c.type)).toArray ++ extraOwn).toList.eraseDups.toArray.qsort (· < ·)
    let mut gl : Std.HashMap String Level := {}
    let mut ownMVars : Array (String × Level) := #[]
    for m in own do
      let v ← mkFreshLevelMVar
      gl := gl.insert m v
      ownMVars := ownMVars.push (m, v)
    let ty ← match ← runTrans genv (withPath "type" (transClosed c.type)) gl polyLvls factReduce admitLv lower with
      | .ok e => pure e
      | .error e => return fromTransError base e
    let val ← match ← runTrans genv (withPath "body" (transClosed body)) gl polyLvls factReduce admitLv lower with
      | .ok e => pure e
      | .error e => return fromTransError base e
    -- after unification: every own level still free that occurs in the (solved) type becomes a
    -- parameter — a type level, or a body level that a type level's solution now mentions
    let implicitRef ← IO.mkRef (#[] : Array String)
    let interpRef ← IO.mkRef (#[] : Array (String × Level))
    let keepParams : MetaM Unit := do
      -- R3G discovery pass: report the source levels of free metavariable classes of the *type* at
      -- references (a level below every other level of its class, not own, not template, whose
      -- every argument still contains a free metavariable); nothing is assigned
      if discover then
        let tyI ← instLevelMVars ty
        let valI ← instLevelMVars val
        let argsFor (e : Expr) : MetaM (Array (String × Level)) := do
          let mut out := #[]
          for (n, ls) in constOccurrences e do
            if let some gs := genv.constGlobals[n]? then
              let ls := ls.drop (genv.polyByTarget[n]?.getD 0)
              if gs.size == ls.length then
                for l in gs, σ in ls do out := out.push (l, ← instantiateLevelMVars σ)
          return out
        let inTy ← argsFor tyI
        let all := inTy ++ (← argsFor valI)
        let mut picks : Array String := #[]
        let mut done : Array Level := #[]
        for (_, σ) in inTy do
          unless σ.isMVar && !done.contains σ do continue
          done := done.push σ
          let cls := (all.filter (·.2 == σ)).map (·.1)
          let tyCls := (inTy.filter (·.2 == σ)).map (·.1)
          let pick := tyCls.toList.eraseDups.find? fun l =>
            !own.contains l && !picks.contains l && !genv.templateLevels.contains l &&
            cls.all (fun l' => entails genv.facts l l' 0) && (all.filter (·.1 == l)).all (·.2.hasMVar)
          if let some l := pick then picks := picks.push l
        implicitRef.set picks
        return
      -- type levels first, so that a class of levels identified by unification is represented by
      -- a type level (its source level is what R3 checks at references)
      unless interp do
        for (m, v) in ownMVars do
          if typeLevels.contains m then
            if let .mvar r ← instantiateLevelMVars v then assignLevelMVar r (.param (levelParamName m))
        let ((), tyMVars) := (levelMVarsOf (← instLevelMVars ty)).run #[]
        for (m, v) in ownMVars do
          if let .mvar r ← instantiateLevelMVars v then
            if tyMVars.contains r then assignLevelMVar r (.param (levelParamName m))
      -- R3G: a universe argument still free in the *type*, at a reference to a declaration whose
      -- parameter stands for source level `l`, is the source level `l` itself (Rocq references
      -- monomorphic declarations at their own levels): it becomes the parameter `u_l`, so the
      -- declaration stays as general as typing allows instead of being fixed at a default. The
      -- kernel checks the declaration for every value of it.
      -- A free metavariable may stand for several source levels (Lean's unifier identified the
      -- arguments of several references). It is taken as `u_l` for a level `l` that occurs in the
      -- *type* and lies below every other level of its class (`l ≤ l'` entailed by the native
      -- facts), so every other argument of the class satisfies R3's no-raising condition (which
      -- `checkUniverseObligations` re-checks). Own levels and template levels are never chosen.
      let tyI ← instLevelMVars ty
      let valI ← instLevelMVars val
      let argsFor (e : Expr) : MetaM (Array (String × Level)) := do
        let mut out := #[]
        for (n, ls) in constOccurrences e do
          if let some gs := genv.constGlobals[n]? then
            let ls := ls.drop (genv.polyByTarget[n]?.getD 0)
            if gs.size == ls.length then
              for l in gs, σ in ls do out := out.push (l, ← instantiateLevelMVars σ)
        return out
      let inTy ← argsFor tyI
      let all := inTy ++ (← argsFor valI)
      let mut done : Array Level := #[]
      let mut chosen : Array (String × Array LMVarId) := #[]
      -- (R2F-c: classes of the body are candidates too; their levels become own levels)
      for (_, σ) in (if interp then all else inTy) do
        unless σ.isMVar && !done.contains σ do continue
        done := done.push σ
        let cls := (all.filter (·.2 == σ)).map (·.1)
        let tyCls := ((if interp then all else inTy).filter (·.2 == σ)).map (·.1)
        -- every argument for `l` anywhere must still be free: they all become `u_l` (coherence)
        let mut cur : Array (String × Level) := #[]
        for (l', σ') in all do cur := cur.push (l', ← instantiateLevelMVars σ')
        let pick := tyCls.toList.eraseDups.find? fun l =>
          !own.contains l && !genv.templateLevels.contains l && cls.all (fun l' => entails genv.facts l l' 0) &&
          (cur.filter (·.1 == l)).all (·.2.isMVar)
        if let some l := pick then
          let mut ms : Array LMVarId := #[]
          for (l', σ') in cur do
            if l' == l then
              if let .mvar r ← instantiateLevelMVars σ' then
                if interp then ms := ms.push r else assignLevelMVar r (.param (levelParamName l))
          if interp then chosen := chosen.push (l, ms)
          implicitRef.modify fun a => if a.contains l then a else a.push l
      -- R2F-c: the explicit type levels and the chosen implicit levels are the declaration's own
      -- levels, each read as ι l = max (u_l, ι m + k) over the native facts m (+1) ≤ l among them
      -- (`ownLevelInterp`, as for inductives): every own fact holds for every parameter value,
      -- and at u := ρ (any model ρ of the facts) ι is ρ itself.
      if interp then
        -- only type levels still free are interpreted; a level that typing already fixed is a solved
        -- level (R2S) and keeps its R2B fact check
        let mut freeT : Array String := #[]
        for (m, v) in ownMVars do
          if typeLevels.contains m then
            if (← instantiateLevelMVars v).isMVar then freeT := freeT.push m
        let ownI := (freeT ++ chosen.map (·.1)).toList.eraseDups.toArray.qsort (· < ·)
        let ι := ownLevelInterp genv.facts ownI
        interpRef.set (ownI.map fun l => (l, ι[l]!))
        for (m, v) in ownMVars do
          if ownI.contains m then
            if let .mvar r ← instantiateLevelMVars v then assignLevelMVar r ι[m]!
        for (l, ms) in chosen do
          for r in ms do
            if let .mvar r' ← instantiateLevelMVars (.mvar r) then assignLevelMVar r' ι[l]!
    -- default of a still-free proof-local level: its minimal model over the *current* values of the
    -- type levels (parameters or solutions)
    let dflt (id : LMVarId) : MetaM Level := do
      match ownMVars.find? (fun (_, v) => v == .mvar id) with
      | some (m, _) =>
        let mut cur : Std.HashMap String Level := {}
        for (t, v) in ownMVars do
          if typeLevels.contains t then cur := cur.insert t (← instantiateLevelMVars v)
        pure (minimalModelLevel genv.facts cur m)
      | none => pure .zero
    let (ty, val, diags, resid, gty, gval, rdefaults) ← solveLevels ty val dflt keepParams (solve := lower)
    if discover then
      return { base with status := "DISCOVERED", implicitLevels := (← implicitRef.get).qsort (· < ·) }
    let base := { base with levelDiagnostics := diags, levelDefaults := resid.length }
    let mut sol : Std.HashMap String Level := {}
    let mut paramLevels : Array String := #[]
    let levelInterp ← interpRef.get
    for (m, v) in ownMVars do
      let s ← instantiateLevelMVars v
      if levelInterp.any (·.1 == m) then continue        -- R2F-c own level: a parameter, read through ι
      if s == .param (levelParamName m) then paramLevels := paramLevels.push m
      else sol := sol.insert m s.normalize
    let implicitLevels := ((← implicitRef.get) ++ extraOwn.filter (!explicitTy.contains ·)).toList.eraseDups.toArray.qsort (· < ·)
    let globals := (paramLevels ++ implicitLevels ++ levelInterp.map (·.1)).toList.eraseDups.toArray.qsort (· < ·)
    let lparams := polyNames ++ globals.toList.map levelParamName
    -- R3 coherence for R2F-c own levels: an argument for `l` must be ι l
    let solι := levelInterp.foldl (fun (m : Std.HashMap String Level) (l, x) => m.insert l x) sol
    let base := { base with bodyLevels := own.filterMap fun m => sol[m]?.map (m, ·) }
    for m in own do
      if sol.contains m then
        if let .error msg := checkBodyLevel genv.facts globals sol m admitLv cumul then
          return { base with status := "UNIVERSE_REJECTED", message := msg }
    -- levels for which the relaxation was actually needed (the strict check fails): proof-local ones
    -- (R2B-P, source instance checked at verify) and levels of the type's own result sort (R2B-S)
    let mut r2bp : Array (String × Level) := #[]
    let mut sortLv : Array (String × Level) := #[]
    if cumul then
      let tyGlobals := globalsOf c.type
      for m in own do
        if let some σ := sol[m]? then
          if !(checkBodyLevel genv.facts globals sol m admitLv false).toBool then
            -- a level of the type that is not only the result sort: the row is the source statement
            -- specialized at the checked instance (R2B-P with `in_type`; never on a requested root)
            if tyGlobals.contains m && onlyInResultSort c.type m then sortLv := sortLv.push (m, σ)
            else r2bp := r2bp.push (m, σ)
    let nchecks ← match checkUniverseObligations genv globals ty solι admitLv cumul lower,
                         checkUniverseObligations genv globals val solι admitLv cumul lower with
      | .ok a, .ok b => pure (a + b)
      | .error msg, _ | _, .error msg =>
        return { base with status := "UNIVERSE_REJECTED", message := msg }
    let base := { base with universeChecks := nchecks }
    unless (← whnf (← inferType ty)).isSort do
      return { base with status := "TRANSLATION_FAILED", message := "translated type is not a type" }
    -- a sealed-module implementation (e.g. HB.lock) is translated as a transparent definition: its
    -- implementation's unlock lemma is `erefl` and needs the δ-rule (the target gains a definitional
    -- unfolding that the sealed source hides; every source proof still checks)
    let kind ← if c.bodyState == "transparent" || c.bodyState == "sealed_implementation" then pure "def"
      else if ← isProp ty then pure "theorem" else pure "opaque"
    let base := { base with target := some name, targetKind := kind, rule := s!"constant/{c.bodyState}" }
    if let some msg ← justifyResiduals name kind lparams resid gty gval then
      return { base with status := "UNIVERSE_REJECTED", message := msg }
    let base := if resid.isEmpty then base
      else { base with residualParams := resid, residualDefaults := rdefaults, residualType := gty, residualValue := gval }
    match ← addChecked (← mkConstDecl name kind lparams ty val) with
    | .accepted => return { base with status := "TRANSLATED_AND_CHECKED", targetType := ty, targetValue := val,
                                      levelParams := lparams, paramLevels := globals, polyParams := polyNames.length,
                                      factReduced := factReduce, implicitLevels, levelInterp,
                                      admittingLevels := admitLv, cumulativity := cumul, r2bpLevels := r2bp, sortLevels := sortLv,
                                      r2bpInType := (r2bp.map (·.1)).filter (globalsOf c.type).contains,
                                      universeLowered := lower, deltaInlined := inlinedA }
    | .rejected msg => return { base with status := "KERNEL_REJECTED", message := msg }
  | st, _ =>
    return { base with status := "EXPORT_VALIDATION_FAILED", message := s!"body state '{st}' inconsistent with body" }

/-- Template binding of a template inductive (R5), from the Rocq kernel's own record
(`native.template_info`, round-trip checked): each template level is bound by exactly one
parameter whose sort is exactly `Type@{l}`, every global level of the declaration is a template
level, and the quoted parameter types agree. Returns `(level, parameter position)` pairs. -/
def templateBinding (i : IR.InductiveDecl) (globals : Array String) :
    Except (String × String) (Array (String × Nat)) := do
  let ti := i.native.getObjValD "template_info"
  let some defaults := (ti.getObjValAs? (Array String) "defaults").toOption | throw ("EXPORT_VALIDATION_FAILED", "template inductive without template_info")
  let some pargs := (ti.getObjValAs? (Array Json) "param_arguments").toOption | throw ("EXPORT_VALIDATION_FAILED", "template_info without param_arguments")
  -- other (non-template) global levels are allowed: they are solved by unification (R5S)
  let _ := globals
  if i.params.any (·.body.isSome) then throw ("UNSUPPORTED_FEATURE", "template inductive with let-bound parameters")
  unless pargs.size == i.params.size do throw ("EXPORT_VALIDATION_FAILED", "template_info parameter count differs from the quoted parameters")
  let mut out : Array (String × Nat) := #[]
  for pa in pargs, k in [0:pargs.size] do
    if pa.isNull then continue
    let us := (pa.getObjValAs? (Array Json) "u").toOption.getD #[]
    -- `quality_sort`: the parameter also binds a sort quality (Rocq: "can be instantiated to
    -- Prop"); the kernel's template defaults fix the quality to Type, which is the instance
    -- translated here. References instantiating it at Prop are rejected explicitly (R5).
    let kind := (pa.getObjValAs? String "k").toOption
    let ok := (kind == some "type" || kind == some "quality_sort") && us.size == 1 &&
      (us[0]!.getObjValAs? Nat "n").toOption == some 0 && !(us[0]!.getObjValD "bound").isNull
    unless ok do throw ("UNSUPPORTED_FEATURE", s!"template parameter {k} binds a level with an offset or an algebraic universe")
    let l := (us[0]!.getObjValAs? String "l").toOption.getD ""
    -- the quoted parameter (MetaRocq, innermost-first) must be an arity ending in exactly that
    -- sort: `Type@{l}` or `∀ zs, Type@{l}` (e.g. sigT's `P : A → Type@{l}`)
    let rec codomain : IR.Term → IR.Term
      | .prod _ _ b => codomain b
      | t => t
    match codomain i.params[i.params.size - 1 - k]!.type with
    | .sort (.type #[{ level := .global l', offset := 0 }]) =>
      unless l' == l do throw ("EXPORT_VALIDATION_FAILED", s!"template parameter {k}: quoted sort level {l'} differs from the kernel's {l}")
    | _ => throw ("UNSUPPORTED_FEATURE", s!"template parameter {k}: its type is not an arity ending in Type@\{{l}}")
    out := out.push (l, k)
  for d in defaults do
    unless (out.filter (·.1 == d)).size == 1 do throw ("UNSUPPORTED_FEATURE", s!"template level {d} is not bound by exactly one parameter")
  return out

def processInductive (genv : GEnv) (results : Std.HashMap String DeclResult) (i : IR.InductiveDecl)
    (raw : Json) (extraOwn : Array String := #[]) (discover : Bool := false) (lower : Bool := false)
    (plain : Bool := false) :
    MetaM (DeclResult × Option IndTarget) := do
  let base : DeclResult := { source := i.name, kind := "inductive", status := "" }
  let (missing, failed) := blockedDeps results (i.typeDeps.filter (· != i.name))
  unless missing.isEmpty && failed.isEmpty do
    return ({ base with status := if missing.isEmpty then "BLOCKED_DEPENDENCY" else "EXPORT_VALIDATION_FAILED",
                        message := s!"dependencies missing {missing} / failed {failed}",
                        blockedBy := missing ++ failed }, none)
  let bad := relaxedFlags i.native
  unless bad.isEmpty do
    return ({ base with status := "AUDIT_REJECTED", message := s!"source declared with relaxed checking: {bad}" }, none)
  match findBootstrap? i.name with
  | some rule =>
    match ← verifyBootstrap rule i raw with
    | .ok () =>
      return ({ base with status := "BOOTSTRAP_RESOLVED", rule := rule.id, target := rule.target.types[0]?,
                          targetKind := "inductive (bootstrap)" }, some rule.target)
    | .error msg => return ({ base with status := "AUDIT_REJECTED", rule := rule.id, message := msg }, none)
  | none => generateInductive base i

where
  /-- M3a: emit a fresh Lean inductive for a single-body, monomorphic, non-coinductive block. -/
  generateInductive (base : DeclResult) (i : IR.InductiveDecl) : MetaM (DeclResult × Option IndTarget) := do
    let unsupported (msg : String) := ({ base with status := "UNSUPPORTED_FEATURE", message := msg }, none)
    if let .polymorphic .. := i.universes then return unsupported "universe-polymorphic inductive"
    if i.finite == "CoFinite" then return unsupported "coinductive type"
    unless i.bodies.size == 1 do return unsupported s!"mutual block of {i.bodies.size} inductives"
    let body := i.bodies[0]!
    -- Primitive records (M5): structure-like (one constructor, no indices, non-recursive), so Lean's
    -- kernel projections and structure eta apply; projections are translated to `Expr.proj`.
    let isRecord := !body.projs.isEmpty
    if isRecord then
      unless body.ctors.size == 1 && body.indices.isEmpty && body.projs.size == body.ctors[0]!.args.size do
        return unsupported "primitive record that is not structure-like (one constructor, no indices, one projection per field)"
    if (← getEnv).contains (inductiveNames i.name body.name #[]).1 then
      return ({ base with status := "TRANSLATION_FAILED", message := "target name already in use" }, none)
    let (tname, cnames) := inductiveNames i.name body.name (body.ctors.map (·.name))
    -- Source global levels of the declaration become universe parameters (R2T); for a template
    -- inductive they must be exactly its template levels, each bound by one parameter sort (R5).
    let isTemplate := (i.native.getObjValAs? Bool "template").toOption == some true
    -- R3G for blocks: implicit levels (discovered in a first pass) are own levels of the block from
    -- the start, interpreted by R2F together with the explicit ones
    let allGlobals := if isTemplate then globalsOfInd i
      else (globalsOfInd i ++ extraOwn).toList.eraseDups.toArray.qsort (· < ·)
    let templateParams ← if isTemplate then
        match templateBinding i allGlobals with
        | .ok b => pure b
        | .error (st, msg) => return ({ base with status := st, message := msg }, none)
      else pure #[]
    -- Template inductives: the template levels are the parameters (R5); any other global level of
    -- the block (e.g. Corelib mem_pred's conclusion Type@{max(Set, pred.u0)}, where pred is used on
    -- the parameter by cumulativity) is solved by unifying the constructor types (R5S).
    -- Non-template inductives: every global level is a parameter, read through its fact-respecting
    -- interpretation (R2F).
    let globals := if isTemplate then (templateParams.map (·.1)).qsort (· < ·) else allGlobals
    let extra := allGlobals.filter (!globals.contains ·)
    let lparams := globals.toList.map levelParamName
    let plain := plain && !isTemplate
    let mut gl : Std.HashMap String Level :=
      if isTemplate || plain then globals.foldl (fun m n => m.insert n (.param (levelParamName n))) {}
      else ownLevelInterp genv.facts globals
    let mut extraMVars : Array (String × Level) := #[]
    for m in extra do
      let v ← mkFreshLevelMVar
      gl := gl.insert m v
      extraMVars := extraMVars.push (m, v)
    let ty ← match ← runTrans genv (withPath "arity" (transClosed body.type)) gl (lowerShared := lower) with
      | .ok e => pure e
      | .error e => return (fromTransError base e, none)
    -- constructor types are translated and type-checked against a local `self` of the arity type
    -- (the block is not declared yet), which is then replaced by the constant at the parameters
    let r : Except TransError (Array Constructor × FVarId) ← withLocalDeclD `self ty fun sv => do
      let mut out : Array Constructor := #[]
      for c in body.ctors, cn in cnames do
        let r ← (withReader (fun ctx => { ctx with locals := #[sv] })
                   (withPath s!"ctor {c.name}" (do return eraseBinderScopes (← instLevelMVars (← trans c.type))))).run { genv, globalLevels := gl, lowerShared := lower } |>.run
        match r with
        | .ok cty =>
          -- R3″/R5S: unify level metavariables of the block by type-checking the constructor type
          try Meta.check cty catch _ => pure ()
          out := out.push { name := cn, type := cty }
        | .error e => return .error e
      return .ok (out, sv.fvarId!)
    let (rawCtors, selfId) ← match r with
      | .ok cs => pure cs
      | .error e => return (fromTransError base e, none)
    try Meta.check ty catch _ => pure ()
    -- a non-template level that unification leaves free is a genuine independent level of the
    -- block: it becomes a (non-template) universe parameter, R3 applies at references (R2T)
    let mut sol : Std.HashMap String Level := {}
    let mut freeExtra : Array String := #[]
    for (m, v) in extraMVars do
      if let .mvar r ← instantiateLevelMVars v then
        assignLevelMVar r (.param (levelParamName m))
        freeExtra := freeExtra.push m
    for (m, v) in extraMVars do
      let s ← instantiateLevelMVars v
      if s.hasMVar then
        return ({ base with status := "UNSUPPORTED_FEATURE",
                            message := s!"level {m} of the template inductive is only partly determined by its constructors" }, none)
      unless freeExtra.contains m do sol := sol.insert m s.normalize
    let globals := (globals ++ freeExtra).qsort (· < ·)
    let lparams := globals.toList.map levelParamName
    let self := mkConst tname (lparams.map Level.param)
    let mut ctors : Array Constructor := #[]
    for c in rawCtors do
      let cty ← instLevelMVars (c.type.replaceFVar (mkFVar selfId) self)
      if cty.hasFVar || cty.hasExprMVar then
        return ({ base with status := "TRANSLATION_FAILED", message := s!"constructor {c.name} has escaping free or meta variables" }, none)
      ctors := ctors.push { c with type := cty }
    let ty ← instLevelMVars ty
    for m in extra.filter (!freeExtra.contains ·) do
      if let .error msg := checkBodyLevel genv.facts globals sol m then
        return ({ base with status := "UNIVERSE_REJECTED", message := msg }, none)
    let base := { base with bodyLevels := extra.filterMap fun m => sol[m]?.map (m, ·) }
    -- R3G (inductives), discovery pass: a level metavariable left free at a reference to a
    -- declaration whose parameter stands for source level `l` is `l` itself. The pass reports the
    -- levels so found (same choice and coherence conditions as for constants); the block is then
    -- translated again with them as own levels (`extraOwn`).
    if discover && isTemplate then
      return ({ base with status := "DISCOVERED" }, none)     -- never adds the declaration
    if discover then
      let mut occ : Array (String × Level) := #[]
      for e in #[ty] ++ ctors.map (·.type) do
        for (n, ls) in constOccurrences (← instLevelMVars e) do
          if let some gs := genv.constGlobals[n]? then
            let ls := ls.drop (genv.polyByTarget[n]?.getD 0)
            if gs.size == ls.length then
              for l in gs, σ in ls do occ := occ.push (l, ← instantiateLevelMVars σ)
      -- candidates: classes occurring in the arity (parameter and index types), where a level can
      -- never make a constructor field too big for the block's sort
      let mut inArity : Array Level := #[]
      for (n, ls) in constOccurrences (← instLevelMVars ty) do
        if genv.constGlobals.contains n then
          for σ in ls do inArity := inArity.push (← instantiateLevelMVars σ)
      let mut picks : Array String := #[]
      let mut done : Array Level := #[]
      for (_, σ) in occ.filter (fun (_, σ) => inArity.contains σ) do
        unless σ.isMVar && !done.contains σ do continue
        done := done.push σ
        let cls := (occ.filter (·.2 == σ)).map (·.1)
        let pick := cls.toList.eraseDups.find? fun l =>
          !globals.contains l && !picks.contains l && !genv.templateLevels.contains l &&
          cls.all (fun l' => entails genv.facts l l' 0) && (occ.filter (·.1 == l)).all (·.2.hasMVar)
        if let some l := pick then picks := picks.push l
      return ({ base with status := "DISCOVERED", implicitLevels := picks.qsort (· < ·) }, none)
    -- R3″: references inside the block (to generalized constants / level-parameter inductives) carry
    -- level metavariables; those not fixed by type-checking (nor taken by R3G) take their least
    -- R3-admissible value 0, and R3 is checked on every universe argument of the block.
    let mut ms : Array LMVarId := #[]
    for e in #[ty] ++ ctors.map (·.type) do
      let e ← instLevelMVars e
      let ((), m) := (levelMVarsOf e).run ms
      ms := m
    for m in ms do assignLevelMVar m .zero
    let ty ← instLevelMVars ty
    ctors ← ctors.mapM fun c => do return { c with type := ← instLevelMVars c.type }
    let mut nchecks := 0
    -- R3 coherence: an argument for an own level of a non-template block must be the level standing
    -- for it, its R2F interpretation ι l (u_l itself when no fact constrains l)
    let interpMap : Std.HashMap String Level :=
      if isTemplate || plain then {} else (ownLevelInterp genv.facts globals)
    for e in #[ty] ++ ctors.map (·.type) do
      match checkUniverseObligations genv globals e interpMap (allowLower := lower) with
      | .ok n => nchecks := nchecks + n
      | .error msg => return ({ base with status := "UNIVERSE_REJECTED", message := msg }, none)
    let base := { base with minimalLevels := ms.size, universeChecks := nchecks }
    -- M6: non-uniform parameters (the native `nparams_rec`, round-trip checked) become the first
    -- indices of the Lean inductive; the arity and constructor types are unchanged
    let nparamsRec := (i.native.getObjValAs? Nat "nparams_rec").toOption.getD i.npars
    unless nparamsRec ≤ i.npars do
      return ({ base with status := "EXPORT_VALIDATION_FAILED", message := s!"nparams_rec {nparamsRec} exceeds npars {i.npars}" }, none)
    if nparamsRec < i.npars && (isRecord || isTemplate) then
      return ({ base with status := "UNSUPPORTED_FEATURE",
                          message := "non-uniform parameters of a primitive record or template inductive" }, none)
    let decl := Declaration.inductDecl lparams nparamsRec [{ name := tname, type := ty, ctors := ctors.toList }] false
    let base := { base with target := some tname, targetKind := "inductive",
                            rule := if isTemplate then "inductive/generated-template"
                                    else if lparams.isEmpty then "inductive/generated" else "inductive/generated-levels" }
    match ← addChecked decl with
    | .accepted =>
      let univ := if lparams.isEmpty then UnivRule.mono else .params lparams.length isTemplate
      let tgt : IndTarget := { types := #[tname], ctors := #[cnames], univ, rule := "generated",
                               templateParamPos := templateParams.map (·.2), isStructure := isRecord,
                               templateLevelIdx := (List.range globals.size).toArray.filter
                                 (fun k => templateParams.any (·.1 == globals[k]!)),
                               nonUniform := i.npars - nparamsRec }
      return ({ base with status := "TRANSLATED_AND_CHECKED", targetType := ty, numParams := nparamsRec, primitiveRecord := isRecord,
                          universeLowered := lower, plainLevels := plain,
                          levelParams := lparams, paramLevels := globals, isTemplate, templateParams,
                          implicitLevels := extraOwn.filter (!(globalsOfInd i).contains ·),
                          targetCtors := ctors.map fun c => (c.name, c.type) }, some tgt)
    | .rejected msg => return ({ base with status := "KERNEL_REJECTED", message := msg }, none)

/-- Translate all declarations of an export, in order. -/
def translateSource (src : IR.Source) : MetaM (Array DeclResult) := do
  let irBodies := src.decls.foldl (init := ({} : Std.HashMap String IR.Term)) fun m d => match d with
    | .constant c => match c.body, c.universes with
      | some b, .monomorphic => if c.bodyState == "transparent" then m.insert c.name b else m
      | _, _ => m
    | _ => m
  let setMotive := src.decls.foldl (init := ({} : Std.HashSet String)) fun m d => match d with
    | .constant c => if irBodies.contains c.name && c.type.hasSetMotive then m.insert c.name else m
    | _ => m
  let mut genv : GEnv := { facts := src.facts, irBodies, setMotive }
  let mut results : Std.HashMap String DeclResult := {}
  let mut out := #[]
  for d in src.decls do
    -- the heartbeat budget is per declaration; a declaration exceeding it is a RESOURCE_LIMIT row
    let saved ← saveState
    -- (an internal error of one declaration is its TRANSLATION_FAILED row, not the end of the run)
    -- resource limits per declaration (docs/TRUST.md): reflection proofs (ring/lia certificates)
    -- evaluate the translated normalizers on concrete data during the checks
    let limits := fun (c : Core.Context) => { c with maxRecDepth := 8192, maxHeartbeats := c.maxHeartbeats * 5 }
    let r? ← tryCatchRuntimeEx (Sum.inl <$> withTheReader Core.Context limits
        (withCurrHeartbeats (translateDecl genv results d))) fun e => do
      saved.restore
      pure (Sum.inr (e.isRuntime, ← e.toMessageData.toString))
    let r ← match r? with
      | .inl (r, genv') => genv := genv'; pure r
      | .inr (rt, msg) =>
        pure { source := d.name, kind := match d with | .constant _ => "constant" | _ => "inductive",
               status := if rt then "RESOURCE_LIMIT" else "TRANSLATION_FAILED",
               message := if rt then s!"resource limit per declaration: {msg.take 300}" else s!"internal error: {msg.take 600}" }
    results := results.insert r.source r
    out := out.push r
  return out
where
  /-- One declaration (the attempts and retry tiers), with the environment it extends. -/
  translateDecl (genv0 : GEnv) (results : Std.HashMap String DeclResult) (d : IR.Decl) : MetaM (DeclResult × GEnv) := do
    let mut genv := genv0
    let r ← match d with
      | .constant c =>
        -- R8 first when the type has motive levels: the sort-level form is strictly more general
        -- (u := v+1 gives the R2 form), so it is kept whenever the kernel accepts it
        -- R3G discovery pass (adds nothing): implicit levels of the type, then every attempt below with
        -- them as own levels; if all fail, the same attempts without them (the earlier behaviour)
        -- (The discovery pass for constants, `discover := true`, is not used yet: implicit levels
        -- relate to other references only through `max` arguments that Lean's level unifier cannot
        -- invert, which made more general constants break their own dependants. In-place R3G below.)
        let exts : List (Array String) := [#[]]
        let mut r : DeclResult := default
        let mut first : Option DeclResult := none
        let mut lastTier : Option DeclResult := none
        for eo in exts do
          let r0 ← if (motiveLevels c.type).isEmpty then processConstant genv results c (extraOwn := eo) else do
              let a ← processConstant genv results c (admit := true) (extraOwn := eo)
              if a.ok then pure a else processConstant genv results c (extraOwn := eo)
          first := some r0          -- the diagnosis kept is that of the last (earlier-behaviour) attempt
          r := r0
          if r.ok then break
          -- Universe retry ladder (docs/UNIVERSE_TRANSLATION.md): a kernel or universe rejection under
          -- R2 is retried with fact-reduced universes (R2⁺), then with the fact interpretation of the
          -- own levels (R2F-c), then both; the first accepted translation is kept.
          let retry (st : String) := st == "KERNEL_REJECTED" || st == "UNIVERSE_REJECTED"
          if retry r.status then
            -- strict tiers first; the cumulativity tier (R3↑, R2B-P) only when they all fail
            -- R3↓ last (cumulativity tier, reported): references instantiated below shared levels
            for (fr, it, cu, lo) in [(true, false, false, false), (false, true, false, false), (true, true, false, false),
                                     (false, false, true, false), (true, false, true, false), (false, true, true, false),
                                     (true, true, true, false), (false, false, true, true), (true, false, true, true),
                                     (false, true, true, true), (true, true, true, true)] do
              let r' ← processConstant genv results c (factReduce := fr) (interp := it) (cumul := cu) (extraOwn := eo) (lower := lo)
              lastTier := some r'
              if r'.ok then
                r := r'
                break
            -- M6 last: δ-inline Set-motive constants (Prop ≤ Set at a family argument), then retry
            if !r.ok then
              for (fr, it, cu, lo) in [(false, false, false, false), (true, true, true, true)] do
                let r' ← processConstant genv results c (factReduce := fr) (interp := it) (cumul := cu) (extraOwn := eo)
                  (lower := lo) (delta := true)
                if r'.status != "UNSUPPORTED_FEATURE" then lastTier := some r'
                if r'.ok then
                  r := r'
                  break
          if r.ok then break
        -- a declaration that no attempt accepts keeps the diagnosis of the plain attempt without
        -- implicit levels (the earlier behaviour)
        if !r.ok then
          r := first.getD r
          -- the last tier's diagnosis (R2⁺ + R2F-c + cumulativity + R3↓ with the bounded solver) is
          -- appended, with its solver log
          if let some lt := lastTier then
            let slog := lt.levelDiagnostics.filter (·.startsWith "solver:")
            r := { r with message := s!"{r.message} [last tier: {lt.status}: {lt.message.take 600}{if slog.isEmpty then "" else s!" {slog}"}]" }
        if r.ok then if let some n := r.target then
          genv := { genv with consts := genv.consts.insert c.name n,
                              constLevels := genv.constLevels.insert c.name r.levelParams.length,
                              constGlobals := if r.levelParams.isEmpty then genv.constGlobals
                                else genv.constGlobals.insert n r.paramLevels }
          if r.polyParams > 0 then
            genv := { genv with constPoly := genv.constPoly.insert c.name r.polyParams,
                                polyByTarget := genv.polyByTarget.insert n r.polyParams }
          unless r.admittingLevels.isEmpty do
            genv := { genv with admitting := genv.admitting.insert n r.admittingLevels }
        pure r
      | .inductive i =>
        -- R3G for blocks: first with free reference levels as implicit parameters (more general); if
        -- the kernel rejects that (an implicit level in a field may exceed the block's sort), the
        -- R3″ translation (free reference levels at 0) as before
        -- M6: each attempt first with plain universe parameters (more general: the R2F interpretation
        -- also bakes in facts that only uses elsewhere impose, e.g. Ring_theory.ring_morph's
        -- C ≥ R from IDmorph), then with the R2F interpretation
        let run1 (eo : Array String) (lower : Bool) : MetaM (DeclResult × Option IndTarget) := do
          let (a, ta) ← processInductive genv results i src.rawDecls[i.name]! (extraOwn := eo) (lower := lower) (plain := true)
          if a.ok then return (a, ta)
          processInductive genv results i src.rawDecls[i.name]! (extraOwn := eo) (lower := lower)
        let (r, t?) ← do
          let (d, _) ← processInductive genv results i src.rawDecls[i.name]! (discover := true)
          if d.status == "DISCOVERED" && !d.implicitLevels.isEmpty then
            let (r1, t1) ← run1 d.implicitLevels false
            if r1.ok then pure (r1, t1) else run1 #[] false
          else run1 #[] false
        -- R3↓ last (reported): references in the block instantiated below its shared levels
        let (r, t?) ← if r.ok || !(r.status == "KERNEL_REJECTED" || r.status == "UNIVERSE_REJECTED") then pure (r, t?) else do
          let (r2, t2) ← run1 #[] true
          if r2.ok then pure (r2, t2) else pure ({ r with message := s!"{r.message} [R3↓ attempt: {r2.status}: {r2.message}]" }, t?)
        if let some t := t? then genv := { genv with inds := genv.inds.insert i.name t }
        -- Non-template inductives with generalized global levels: references obey R3 like
        -- generalized constants (the type and its constructors carry the same parameters).
        if r.ok && !r.levelParams.isEmpty then
          if let some tn := r.target then
            for n in #[tn] ++ r.targetCtors.map (·.1) do
              genv := { genv with constGlobals := genv.constGlobals.insert n r.paramLevels }
            for (l, _) in r.templateParams do
              genv := { genv with templateLevels := genv.templateLevels.insert l }
        pure r
    return (r, genv)

/-! ## Report -/

partial def levelJson : Level → Json
  | .zero => Json.mkObj [("k", "zero")]
  | .succ l => Json.mkObj [("k", "succ"), ("l", levelJson l)]
  | .max a b => Json.mkObj [("k", "max"), ("a", levelJson a), ("b", levelJson b)]
  | .imax a b => Json.mkObj [("k", "imax"), ("a", levelJson a), ("b", levelJson b)]
  | .param n => Json.mkObj [("k", "param"), ("n", n.toString)]
  | .mvar _ => Json.mkObj [("k", "mvar")]

/-- Lean `Expr` as JSON, for the independent audit. Binder names are kept but are not compared. -/
partial def exprJson : Expr → Json
  | .bvar i => Json.mkObj [("k", "bvar"), ("i", i)]
  | .fvar _ => Json.mkObj [("k", "fvar")]
  | .mvar _ => Json.mkObj [("k", "mvar")]
  | .sort l => Json.mkObj [("k", "sort"), ("l", levelJson l)]
  | .const n ls => Json.mkObj [("k", "const"), ("n", n.toString), ("u", Json.arr (ls.map levelJson).toArray)]
  | .app f a => Json.mkObj [("k", "app"), ("f", exprJson f), ("a", exprJson a)]
  | .lam n t b _ => Json.mkObj [("k", "lam"), ("n", n.toString), ("t", exprJson t), ("b", exprJson b)]
  | .forallE n t b _ => Json.mkObj [("k", "forall"), ("n", n.toString), ("t", exprJson t), ("b", exprJson b)]
  | .letE n t v b _ =>
    Json.mkObj [("k", "let"), ("n", n.toString), ("t", exprJson t), ("v", exprJson v), ("b", exprJson b)]
  | .lit (.natVal n) => Json.mkObj [("k", "natlit"), ("v", n)]
  | .lit (.strVal s) => Json.mkObj [("k", "strlit"), ("v", s)]
  | .mdata _ e => Json.mkObj [("k", "mdata"), ("e", exprJson e)]
  | .proj s i e => Json.mkObj [("k", "proj"), ("s", s.toString), ("i", i), ("e", exprJson e)]

def DeclResult.toJson (r : DeclResult) : Json :=
  -- (two typed halves: one long list literal is beyond the elaborator's coercion heuristics)
  let universes : List (String × Json) := [
    ("universe_cumulativity", Json.bool r.cumulativity),
    ("universe_lowered", Json.bool r.universeLowered),
    ("plain_levels", Json.bool r.plainLevels),
    ("delta_inlined", Json.arr (r.deltaInlined.map Json.str)),
    ("r2bp_levels", Json.arr (r.r2bpLevels.map fun (m, l) =>
      Json.mkObj [("level", m), ("sigma", levelJson l), ("in_type", Json.bool (r.r2bpInType.contains m))])),
    ("sort_lowered_levels", Json.arr (r.sortLevels.map fun (m, l) => Json.mkObj [("level", m), ("sigma", levelJson l)]))]
  let rest : List (String × Json) := [
    ("source", r.source), ("kind", r.kind), ("status", r.status), ("rule", r.rule),
    ("target", match r.target with | some n => Json.str n.toString | none => .null),
    ("target_kind", r.targetKind), ("message", r.message),
    ("path", Json.arr (r.path.map Json.str).toArray),
    ("blocked_by", Json.arr (r.blockedBy.map Json.str)),
    ("target_type", match r.targetType with | some e => exprJson e | none => .null),
    ("target_value", match r.targetValue with | some e => exprJson e | none => .null),
    ("level_params", Json.arr (r.levelParams.map (Json.str ·.toString)).toArray),
    ("num_params", r.numParams),
    ("template", r.isTemplate),
    ("primitive_record", r.primitiveRecord),
    ("universe_minimal_levels", r.minimalLevels),
    ("solved_levels", Json.arr (r.bodyLevels.map fun (m, l) => Json.mkObj [("level", m), ("sigma", levelJson l)])),
    ("template_params", Json.arr (r.templateParams.map fun (l, k) => Json.mkObj [("level", l), ("param", k)])),
    ("universe_level_defaults", r.levelDefaults),
    ("universe_poly_params", r.polyParams),
    ("sort_fact_reduced", r.factReduced),
    ("implicit_levels", Json.arr (r.implicitLevels.map Json.str)),
    ("admitting_levels", Json.arr (r.admittingLevels.map Json.str)),
    ("level_interp", Json.arr (r.levelInterp.map fun (l, x) => Json.mkObj [("level", l), ("sigma", levelJson x)])),
    ("universe_checks", r.universeChecks),
    ("universe_diagnostics", Json.arr (r.levelDiagnostics.map Json.str)),
    ("universe_residuals", if r.residualParams.isEmpty then .null else Json.mkObj [
      ("params", Json.arr (r.residualParams.map (Json.str ·.toString)).toArray),
      ("defaults", Json.arr (r.residualDefaults.map levelJson).toArray),
      ("justification", "kernel accepted the declaration with these levels as fresh universe parameters"),
      ("generic_type", match r.residualType with | some e => exprJson e | none => .null),
      ("generic_value", match r.residualValue with | some e => exprJson e | none => .null)]),
    ("target_ctors", Json.arr (r.targetCtors.map fun (n, e) =>
      Json.mkObj [("name", n.toString), ("type", exprJson e)]))]
  Json.mkObj (rest ++ universes)

end Rocq2Lean

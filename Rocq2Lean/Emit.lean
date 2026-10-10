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
  /-- Proof-local levels (in the body only) and their solutions (R2B). -/
  bodyLevels : Array (String × Level) := #[]
  templateParams : Array (String × Nat) := #[]
  residualType : Option Expr := none
  residualValue : Option Expr := none
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

def processConstant (genv : GEnv) (results : Std.HashMap String DeclResult) (c : IR.ConstantDecl) :
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
  if let .polymorphic .. := c.universes then
    return { base with status := "UNSUPPORTED_FEATURE", message := "universe-polymorphic constant" }
  match c.bodyState, c.body with
  | "assumption", _ =>
    return { base with status := "BLOCKED_SOURCE_BODY",
                       message := "genuine source assumption; the pilot admits no source axioms" }
  | "unavailable", _ =>
    return { base with status := "BLOCKED_SOURCE_BODY", message := "body not available in the export" }
  | "unsupported_primitive", _ =>
    return { base with status := "UNSUPPORTED_FEATURE", message := "primitive or symbol constant" }
  | st, some body =>
    unless st == "transparent" || st == "opaque_present" do
      return { base with status := "EXPORT_VALIDATION_FAILED", message := s!"unknown body state '{st}'" }
    let name := targetName c.name
    if (← getEnv).contains name then
      return { base with status := "TRANSLATION_FAILED", message := s!"target name {name} already in use" }
    -- Global monomorphic levels of the *type* become universe parameters (R2); levels occurring
    -- only in the body are proof-local: level metavariables solved by Lean's unifier (R2B).
    let globals := (globalsOf c.type).toArray.qsort (· < ·)
    let bodyOnly := (globalsOf body).toArray.filter (!globals.contains ·) |>.qsort (· < ·)
    let lparams := globals.toList.map levelParamName
    let mut gl : Std.HashMap String Level :=
      globals.foldl (fun m n => m.insert n (.param (levelParamName n))) {}
    let mut bodyMVars : Array (String × Level) := #[]
    for m in bodyOnly do
      let v ← mkFreshLevelMVar
      gl := gl.insert m v
      bodyMVars := bodyMVars.push (m, v)
    let ty ← match ← runTrans genv (withPath "type" (transClosed c.type)) gl with
      | .ok e => pure e
      | .error e => return fromTransError base e
    let val ← match ← runTrans genv (withPath "body" (transClosed body)) gl with
      | .ok e => pure e
      | .error e => return fromTransError base e
    -- Unassigned proof-local levels default to their minimal model (R2B); others to 0 (R3′).
    let mut dflts : Std.HashMap LMVarId Level := {}
    for (m, v) in bodyMVars do
      if let .mvar id := v then dflts := dflts.insert id (minimalModelLevel genv.facts globals m)
    let (ty, val, diags, resid, gty, gval, rdefaults) ← solveLevels ty val (fun id => dflts.getD id .zero)
    let base := { base with levelDiagnostics := diags, levelDefaults := resid.length }
    let mut sol : Std.HashMap String Level := {}
    for (m, v) in bodyMVars do
      sol := sol.insert m (← instantiateLevelMVars v).normalize
    let base := { base with bodyLevels := bodyMVars.map fun (p : String × Level) => (p.1, sol[p.1]!) }
    for m in bodyOnly do
      if let .error msg := checkBodyLevel genv.facts globals sol m then
        return { base with status := "UNIVERSE_REJECTED", message := msg }
    let nchecks ← match checkUniverseObligations genv globals ty sol, checkUniverseObligations genv globals val sol with
      | .ok a, .ok b => pure (a + b)
      | .error msg, _ | _, .error msg =>
        return { base with status := "UNIVERSE_REJECTED", message := msg }
    let base := { base with universeChecks := nchecks }
    unless (← whnf (← inferType ty)).isSort do
      return { base with status := "TRANSLATION_FAILED", message := "translated type is not a type" }
    let kind ← if c.bodyState == "transparent" then pure "def" else if ← isProp ty then pure "theorem" else pure "opaque"
    let base := { base with target := some name, targetKind := kind, rule := s!"constant/{c.bodyState}" }
    if let some msg ← justifyResiduals name kind lparams resid gty gval then
      return { base with status := "UNIVERSE_REJECTED", message := msg }
    let base := if resid.isEmpty then base
      else { base with residualParams := resid, residualDefaults := rdefaults, residualType := gty, residualValue := gval }
    match ← addChecked (← mkConstDecl name kind lparams ty val) with
    | .accepted => return { base with status := "TRANSLATED_AND_CHECKED", targetType := ty, targetValue := val,
                                      levelParams := lparams }
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
  unless globals.all defaults.contains do
    throw ("UNSUPPORTED_FEATURE", s!"template inductive with non-template global levels {globals.filter (!defaults.contains ·)}")
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
    (raw : Json) :
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
    unless body.projs.isEmpty do return unsupported "primitive record (projections)"
    if (← getEnv).contains (inductiveNames i.name body.name #[]).1 then
      return ({ base with status := "TRANSLATION_FAILED", message := "target name already in use" }, none)
    let (tname, cnames) := inductiveNames i.name body.name (body.ctors.map (·.name))
    -- Source global levels of the declaration become universe parameters (R2T); for a template
    -- inductive they must be exactly its template levels, each bound by one parameter sort (R5).
    let globals := globalsOfInd i
    let lparams := globals.toList.map levelParamName
    let gl : Std.HashMap String Level := globals.foldl (fun m n => m.insert n (.param (levelParamName n))) {}
    let isTemplate := (i.native.getObjValAs? Bool "template").toOption == some true
    let templateParams ← if isTemplate then
        match templateBinding i globals with
        | .ok b => pure b
        | .error (st, msg) => return ({ base with status := st, message := msg }, none)
      else pure #[]
    let ty ← match ← runTrans genv (withPath "arity" (transClosed body.type)) gl with
      | .ok e => pure e
      | .error e => return (fromTransError base e, none)
    let self := mkConst tname (lparams.map Level.param)
    let mut ctors : Array Constructor := #[]
    for c in body.ctors, cn in cnames do
      let r ← (withReader (fun ctx => { ctx with locals := #[self] })
                 (withPath s!"ctor {c.name}" (transClosed c.type))).run { genv, globalLevels := gl } |>.run
      match r with
      | .ok cty => ctors := ctors.push { name := cn, type := cty }
      | .error e => return (fromTransError base e, none)
    let decl := Declaration.inductDecl lparams i.npars [{ name := tname, type := ty, ctors := ctors.toList }] false
    let base := { base with target := some tname, targetKind := "inductive",
                            rule := if isTemplate then "inductive/generated-template"
                                    else if lparams.isEmpty then "inductive/generated" else "inductive/generated-levels" }
    match ← addChecked decl with
    | .accepted =>
      let univ := if lparams.isEmpty then UnivRule.mono else .params lparams.length isTemplate
      let tgt : IndTarget := { types := #[tname], ctors := #[cnames], univ, rule := "generated",
                               templateParamPos := templateParams.map (·.2) }
      return ({ base with status := "TRANSLATED_AND_CHECKED", targetType := ty, numParams := i.npars,
                          levelParams := lparams, isTemplate, templateParams,
                          targetCtors := ctors.map fun c => (c.name, c.type) }, some tgt)
    | .rejected msg => return ({ base with status := "KERNEL_REJECTED", message := msg }, none)

/-- Translate all declarations of an export, in order. -/
def translateSource (src : IR.Source) : MetaM (Array DeclResult) := do
  let mut genv : GEnv := { facts := src.facts }
  let mut results : Std.HashMap String DeclResult := {}
  let mut out := #[]
  for d in src.decls do
    let r ← match d with
      | .constant c =>
        let r ← processConstant genv results c
        if r.ok then if let some n := r.target then
          genv := { genv with consts := genv.consts.insert c.name n,
                              constLevels := genv.constLevels.insert c.name r.levelParams.length,
                              constGlobals := if r.levelParams.isEmpty then genv.constGlobals
                                else genv.constGlobals.insert n ((globalsOf' c).qsort (· < ·)) }
        pure r
      | .inductive i =>
        let (r, t?) ← processInductive genv results i src.rawDecls[i.name]!
        if let some t := t? then genv := { genv with inds := genv.inds.insert i.name t }
        -- Non-template inductives with generalized global levels: references obey R3 like
        -- generalized constants (the type and its constructors carry the same parameters).
        if r.ok && !r.isTemplate && !r.levelParams.isEmpty then
          if let some tn := r.target then
            -- `levelParams` are `globalsOfInd i` mapped by `levelParamName`, in the same order.
            for n in #[tn] ++ r.targetCtors.map (·.1) do
              genv := { genv with constGlobals := genv.constGlobals.insert n (globalsOfInd i) }
        pure r
    results := results.insert r.source r
    out := out.push r
  return out

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
  Json.mkObj [
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
    ("body_levels", Json.arr (r.bodyLevels.map fun (m, l) => Json.mkObj [("level", m), ("sigma", levelJson l)])),
    ("template_params", Json.arr (r.templateParams.map fun (l, k) => Json.mkObj [("level", l), ("param", k)])),
    ("universe_level_defaults", r.levelDefaults),
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

end Rocq2Lean

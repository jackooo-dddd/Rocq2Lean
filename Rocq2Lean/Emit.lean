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
    let ty ← match ← runTrans genv (withPath "type" (transClosed c.type)) with
      | .ok e => pure e
      | .error e => return fromTransError base e
    unless (← whnf (← inferType ty)).isSort do
      return { base with status := "TRANSLATION_FAILED", message := "translated type is not a type" }
    let val ← match ← runTrans genv (withPath "body" (transClosed body)) with
      | .ok e => pure e
      | .error e => return fromTransError base e
    let (decl, kind) ←
      if c.bodyState == "transparent" then
        let h := ReducibilityHints.regular (getMaxHeight (← getEnv) val + 1)
        pure (Declaration.defnDecl { name, levelParams := [], type := ty, value := val, hints := h,
                                     safety := .safe, all := [name] }, "def")
      else if ← isProp ty then
        pure (Declaration.thmDecl { name, levelParams := [], type := ty, value := val, all := [name] }, "theorem")
      else
        pure (Declaration.opaqueDecl { name, levelParams := [], type := ty, value := val, isUnsafe := false,
                                       all := [name] }, "opaque")
    let base := { base with target := some name, targetKind := kind, rule := s!"constant/{c.bodyState}" }
    match ← addChecked decl with
    | .accepted => return { base with status := "TRANSLATED_AND_CHECKED", targetType := ty, targetValue := val }
    | .rejected msg => return { base with status := "KERNEL_REJECTED", message := msg }
  | st, _ =>
    return { base with status := "EXPORT_VALIDATION_FAILED", message := s!"body state '{st}' inconsistent with body" }

def processInductive (results : Std.HashMap String DeclResult) (i : IR.InductiveDecl) (raw : Json) :
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
  | none =>
    return ({ base with status := "UNSUPPORTED_FEATURE",
                        message := "new inductive declarations are not enabled in this build" }, none)

/-- Translate all declarations of an export, in order. -/
def translateSource (src : IR.Source) : MetaM (Array DeclResult) := do
  let mut genv : GEnv := {}
  let mut results : Std.HashMap String DeclResult := {}
  let mut out := #[]
  for d in src.decls do
    let r ← match d with
      | .constant c =>
        let r ← processConstant genv results c
        if r.ok then if let some n := r.target then genv := { genv with consts := genv.consts.insert c.name n }
        pure r
      | .inductive i =>
        let (r, t?) ← processInductive results i src.rawDecls[i.name]!
        if let some t := t? then genv := { genv with inds := genv.inds.insert i.name t }
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
    ("target_value", match r.targetValue with | some e => exprJson e | none => .null)]

end Rocq2Lean

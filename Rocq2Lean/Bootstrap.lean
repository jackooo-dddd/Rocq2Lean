import Lean
import Rocq2Lean.IR
import Rocq2Lean.Signature
import Rocq2Lean.Translate

/-!
# Bootstrap registry

The only source declarations that are *not* translated: a few core inductives realised by
existing Lean inductives. Each entry records the exact canonical source signature
(`Rocq2Lean.canonicalSignature`), the Lean target, the universe rule and a rule id.
`verifyBootstrap` re-checks every entry on every run:

1. the exported source signature equals the registered one;
2. the Lean target has the registered shape (parameters, indices, universe parameters,
   constructor names and order, block size);
3. adapter check: the source arity and every source constructor type, translated through the
   mapping itself, are definitionally equal to the target's.

No definitions, theorems or fixture-specific names belong here.
-/

namespace Rocq2Lean

open Lean Meta

structure BootstrapRule where
  id : String
  source : String
  signature : String
  target : IndTarget
  numParams : Nat
  numIndices : Nat
  numLevels : Nat
  deriving Inhabited

def bootstrapRules : Array BootstrapRule := #[
  { id := "bootstrap/nat-to-Nat", source := "Corelib.Init.Datatypes.nat",
    signature := "{\"bodies\":[{\"ctors\":[{\"args\":[],\"arity\":0,\"indices\":[],\"name\":\"O\",\"type\":{\"i\":0,\"k\":\"rel\"}},{\"args\":[{\"body\":null,\"n\":{\"n\":null,\"r\":\"R\"},\"ty\":{\"i\":0,\"k\":\"rel\"}}],\"arity\":1,\"indices\":[],\"name\":\"S\",\"type\":{\"b\":{\"i\":1,\"k\":\"rel\"},\"k\":\"prod\",\"n\":{\"n\":null,\"r\":\"R\"},\"ty\":{\"i\":0,\"k\":\"rel\"}}}],\"indices\":[],\"kelim\":\"IntoAny\",\"name\":\"nat\",\"projs\":[],\"r\":\"R\",\"sort\":{\"k\":\"type\",\"u\":[{\"l\":{\"k\":\"set\"},\"n\":0}]},\"type\":{\"k\":\"sort\",\"s\":{\"k\":\"type\",\"u\":[{\"l\":{\"k\":\"set\"},\"n\":0}]}}}],\"finite\":\"Finite\",\"kind\":\"inductive\",\"name\":\"Corelib.Init.Datatypes.nat\",\"npars\":0,\"params\":[],\"polymorphic\":false,\"private\":null,\"template\":false,\"universes\":{\"k\":\"monomorphic\"},\"variance\":null}",
    target := { types := #[``Nat], ctors := #[#[``Nat.zero, ``Nat.succ]], univ := .mono,
                rule := "bootstrap/nat-to-Nat" },
    numParams := 0, numIndices := 0, numLevels := 0 },
  { id := "bootstrap/eq-to-Eq", source := "Corelib.Init.Logic.eq",
    signature := "{\"bodies\":[{\"ctors\":[{\"args\":[],\"arity\":0,\"indices\":[{\"i\":0,\"k\":\"rel\"}],\"name\":\"eq_refl\",\"type\":{\"b\":{\"b\":{\"args\":[{\"i\":1,\"k\":\"rel\"},{\"i\":0,\"k\":\"rel\"},{\"i\":0,\"k\":\"rel\"}],\"f\":{\"i\":2,\"k\":\"rel\"},\"k\":\"app\"},\"k\":\"prod\",\"n\":{\"n\":\"x\",\"r\":\"R\"},\"ty\":{\"i\":0,\"k\":\"rel\"}},\"k\":\"prod\",\"n\":{\"n\":\"A\",\"r\":\"R\"},\"ty\":{\"k\":\"sort\",\"s\":{\"k\":\"type\",\"u\":[{\"l\":{\"k\":\"global\",\"n\":\"*\"},\"n\":0}]}}}}],\"indices\":[{\"body\":null,\"n\":{\"n\":null,\"r\":\"R\"},\"ty\":{\"i\":1,\"k\":\"rel\"}}],\"kelim\":\"IntoAny\",\"name\":\"eq\",\"projs\":[],\"r\":\"R\",\"sort\":{\"k\":\"prop\"},\"type\":{\"b\":{\"b\":{\"b\":{\"k\":\"sort\",\"s\":{\"k\":\"prop\"}},\"k\":\"prod\",\"n\":{\"n\":null,\"r\":\"R\"},\"ty\":{\"i\":1,\"k\":\"rel\"}},\"k\":\"prod\",\"n\":{\"n\":\"x\",\"r\":\"R\"},\"ty\":{\"i\":0,\"k\":\"rel\"}},\"k\":\"prod\",\"n\":{\"n\":\"A\",\"r\":\"R\"},\"ty\":{\"k\":\"sort\",\"s\":{\"k\":\"type\",\"u\":[{\"l\":{\"k\":\"global\",\"n\":\"*\"},\"n\":0}]}}}}],\"finite\":\"Finite\",\"kind\":\"inductive\",\"name\":\"Corelib.Init.Logic.eq\",\"npars\":2,\"params\":[{\"body\":null,\"n\":{\"n\":\"x\",\"r\":\"R\"},\"ty\":{\"i\":0,\"k\":\"rel\"}},{\"body\":null,\"n\":{\"n\":\"A\",\"r\":\"R\"},\"ty\":{\"k\":\"sort\",\"s\":{\"k\":\"type\",\"u\":[{\"l\":{\"k\":\"global\",\"n\":\"*\"},\"n\":0}]}}}],\"polymorphic\":false,\"private\":null,\"template\":true,\"universes\":{\"k\":\"monomorphic\"},\"variance\":null}",
    target := { types := #[``Eq], ctors := #[#[``Eq.refl]], univ := .templateFromArg 0,
                rule := "bootstrap/eq-to-Eq" },
    numParams := 2, numIndices := 1, numLevels := 1 }
]

def findBootstrap? (source : String) : Option BootstrapRule :=
  bootstrapRules.find? (·.source == source)

private def check (b : Bool) (msg : String) : ExceptT String MetaM Unit :=
  unless b do throwThe String msg

/-- Re-verify a bootstrap rule against the exported source declaration and the Lean target. -/
def verifyBootstrap (rule : BootstrapRule) (src : IR.InductiveDecl) (raw : Json) :
    MetaM (Except String Unit) := ExceptT.run do
  check (canonicalSignature raw == rule.signature)
    s!"source signature of {rule.source} differs from the registered signature of rule {rule.id}"
  check (src.bodies.size == rule.target.types.size) "block size differs"
  let env ← getEnv
  -- Target shape.
  let mut infos : Array InductiveVal := #[]
  for t in rule.target.types, cs in rule.target.ctors do
    let some (.inductInfo iv) := env.find? t | throwThe String s!"target {t} is not an inductive type"
    check (iv.numParams == rule.numParams) s!"{t}: expected {rule.numParams} parameters"
    check (iv.numIndices == rule.numIndices) s!"{t}: expected {rule.numIndices} indices"
    check (iv.levelParams.length == rule.numLevels) s!"{t}: expected {rule.numLevels} universe parameters"
    check (iv.ctors == cs.toList) s!"{t}: constructors {iv.ctors} differ from {cs.toList}"
    check (iv.all == rule.target.types.toList) s!"{t}: mutual block differs"
    infos := infos.push iv
  -- Adapter check: translate source arities and constructor types through the mapping.
  let lps := infos[0]!.levelParams
  let lvls := lps.map Level.param
  let mut genv : GEnv := { inds := ({} : Std.HashMap _ _).insert rule.source rule.target }
  if let .templateFromArg k := rule.target.univ then
    let params := src.params.reverse
    unless k < params.size do throwThe String "template parameter position out of range"
    let .sort (.type #[{ level := .global n, offset := 0 }]) := params[k]!.type
      | throwThe String "template parameter is not of sort Type@{l} for a single global level l"
    genv := { genv with sortOverride := ({} : Std.HashMap _ _).insert n lvls[0]! }
  let selfRefs := rule.target.types.map (mkConst · lvls)
  for body in src.bodies, iv in infos, cs in rule.target.ctors do
    let ty ← match ← runTrans genv (transClosed body.type) with
      | .ok e => pure e
      | .error e => throwThe String s!"source arity of {body.name}: {e.msg}"
    check (← isDefEq ty iv.type) s!"source arity of {body.name} is not convertible to {iv.name}'s type"
    for c in body.ctors, cn in cs do
      let r ← (withReader (fun ctx => { ctx with locals := selfRefs }) (transClosed c.type) |>.run { genv }).run
      let cty ← match r with
        | .ok e => pure e
        | .error e => throwThe String s!"source constructor {c.name}: {e.msg}"
      let some (.ctorInfo ci) := env.find? cn | throwThe String s!"{cn} is not a constructor"
      check (ci.levelParams == lps) s!"{cn}: universe parameters differ"
      check (← isDefEq cty ci.type) s!"source constructor {c.name} is not convertible to {cn}'s type"

end Rocq2Lean

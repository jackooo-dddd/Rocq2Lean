import Lean

/-!
# `#rocq2lean_eval`: closed-value normalization for computation comparison

`#rocq2lean_eval "names.json" "out.json"` fully normalizes each named closed constant
(`Meta.reduce`, all transparency) and writes it as a constructor tree:
`{"c": ctor, "args": [...]}`, `{"i": inductive}` or `{"nat": n}` (Lean `Nat` literals).
Anything else is written as `{"other": …}`, which never compares equal.
-/

namespace Rocq2Lean

open Lean Elab Command Meta

partial def valueJson (e : Expr) : MetaM Json := do
  match e with
  | .lit (.natVal n) => return Json.mkObj [("nat", n)]
  | _ =>
    let fn := e.getAppFn
    let args := e.getAppArgs
    match fn with
    | .const n _ =>
      match (← getEnv).find? n with
      | some (.ctorInfo _) => return Json.mkObj [("c", n.toString), ("args", Json.arr (← args.mapM valueJson))]
      | some (.inductInfo _) => return Json.mkObj [("i", n.toString), ("args", Json.arr (← args.mapM valueJson))]
      | _ => return Json.mkObj [("other", toString e)]
    | _ => return Json.mkObj [("other", toString e)]

syntax (name := rocqEval) "#rocq2lean_eval " str str : command

@[command_elab rocqEval] def elabRocqEval : CommandElab := fun stx => do
  let some inp := stx[1].isStrLit? | throwError "expected names path"
  let some out := stx[2].isStrLit? | throwError "expected output path"
  let j ← IO.ofExcept (Json.parse (← IO.FS.readFile inp))
  let arr ← IO.ofExcept j.getArr?
  let names : Array String ← IO.ofExcept (arr.mapM fun x => x.getStr?)
  let res ← liftTermElabM do
    names.mapM fun (n : String) => do
      let v ← withTransparency .all <| Meta.reduce (mkConst n.toName) (explicitOnly := false) (skipTypes := false)
      return Json.mkObj [("name", Json.str n), ("value", ← valueJson v)]
  IO.FS.writeFile out ((Json.arr res).pretty ++ "\n")

end Rocq2Lean

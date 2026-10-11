import Lean
import Rocq2Lean.Kernel
import Rocq2Lean.Emit

/-!
# `#rocq2lean_replay "report.json" "result.json"`

Rebuilds every `TRANSLATED_AND_CHECKED` declaration of a report (statement mode: every claimed row,
statements and pending artifacts included) **from its JSON alone**
(`exprOfJson`, the inverse of `exprJson`) and submits it to the Lean kernel through
`addChecked`, in a fresh module that does not import the generated one. Used to

* show that the audited representation is kernel-valid by itself, and
* decide whether a *mutated* report is kernel-accepted (so a fidelity test can show that the
  structural/universe audit — not the kernel — rejected a type-correct mutation).
-/

namespace Rocq2Lean

open Lean Elab Command Meta

partial def levelOfJson (j : Json) : Except String Level := do
  match ← j.getObjValAs? String "k" with
  | "zero" => pure .zero
  | "succ" => return .succ (← levelOfJson (← j.getObjVal? "l"))
  | "max" => return .max (← levelOfJson (← j.getObjVal? "a")) (← levelOfJson (← j.getObjVal? "b"))
  | "imax" => return .imax (← levelOfJson (← j.getObjVal? "a")) (← levelOfJson (← j.getObjVal? "b"))
  | "param" => return .param (← j.getObjValAs? String "n").toName
  | k => throw s!"level kind {k} cannot be replayed"

partial def exprOfJson (j : Json) : Except String Expr := do
  -- (`exprJson` writes `Name.anonymous` as "[anonymous]", e.g. Rocq's anonymous binders)
  let name (k : String) : Except String Name := do
    let s ← j.getObjValAs? String k
    return if s == "[anonymous]" then .anonymous else s.toName
  let sub (k : String) : Except String Expr := do exprOfJson (← j.getObjVal? k)
  match ← j.getObjValAs? String "k" with
  | "bvar" => return .bvar (← j.getObjValAs? Nat "i")
  | "sort" => return .sort (← levelOfJson (← j.getObjVal? "l"))
  | "const" => return .const (← name "n") ((← (← j.getObjValAs? (Array Json) "u").mapM levelOfJson).toList)
  | "app" => return .app (← sub "f") (← sub "a")
  | "lam" => return .lam (← name "n") (← sub "t") (← sub "b") .default
  | "forall" => return .forallE (← name "n") (← sub "t") (← sub "b") .default
  | "let" => return .letE (← name "n") (← sub "t") (← sub "v") (← sub "b") false
  | "natlit" => return .lit (.natVal (← j.getObjValAs? Nat "v"))
  | "strlit" => return .lit (.strVal (← j.getObjValAs? String "v"))
  | "mdata" => sub "e"
  | "proj" => return .proj (← name "s") (← j.getObjValAs? Nat "i") (← sub "e")
  | k => throw s!"expression kind {k} cannot be replayed"

syntax (name := rocqReplay) "#rocq2lean_replay " str str : command

@[command_elab rocqReplay] def elabRocqReplay : CommandElab := fun stx => do
  let some repPath := stx[1].isStrLit? | throwError "expected a report path"
  let some outPath := stx[2].isStrLit? | throwError "expected an output path"
  let report ← IO.ofExcept (Json.parse (← IO.FS.readFile repPath))
  let results ← IO.ofExcept (report.getObjValAs? (Array Json) "results")
  let out ← liftTermElabM do
    let mut out : Array Json := #[]
    for r in results do
      unless ["TRANSLATED_AND_CHECKED", "STATEMENT_KERNEL_CHECKED", "PENDING_KERNEL_CHECKED",
              "STATEMENT_PENDING_KERNEL_CHECKED"].contains ((r.getObjValAs? String "status").toOption.getD "") do continue
      let src := (r.getObjValAs? String "source").toOption.getD "?"
      let decl : Except String Declaration := do
        let n := (← r.getObjValAs? String "target").toName
        let lps := (← r.getObjValAs? (Array String) "level_params").toList.map String.toName
        let ty ← exprOfJson (← r.getObjVal? "target_type")
        match ← r.getObjValAs? String "target_kind" with
        | "inductive" =>
          let ctors ← (← r.getObjValAs? (Array Json) "target_ctors").mapM fun c => do
            return ({ name := (← c.getObjValAs? String "name").toName, type := ← exprOfJson (← c.getObjVal? "type") } : Constructor)
          return .inductDecl lps (← r.getObjValAs? Nat "num_params") [{ name := n, type := ty, ctors := ctors.toList }] false
        | "def" | "statement" =>
          return .defnDecl { name := n, levelParams := lps, type := ty, value := ← exprOfJson (← r.getObjVal? "target_value"),
                             hints := .regular 0, safety := .safe, all := [n] }
        | "theorem" =>
          return .thmDecl { name := n, levelParams := lps, type := ty, value := ← exprOfJson (← r.getObjVal? "target_value"), all := [n] }
        | "opaque" =>
          return .opaqueDecl { name := n, levelParams := lps, type := ty, value := ← exprOfJson (← r.getObjVal? "target_value"),
                               isUnsafe := false, all := [n] }
        | k => throw s!"unknown target kind {k}"
      match decl with
      | .error e => out := out.push (Json.mkObj [("source", src), ("kernel", "NOT_REPLAYABLE"), ("message", e)])
      | .ok d =>
        let env ← getEnv
        let d := match d with
          | .defnDecl v => .defnDecl { v with hints := .regular (getMaxHeight env v.value + 1) }
          | d => d
        match ← addChecked d with
        | .accepted => out := out.push (Json.mkObj [("source", src), ("kernel", "ACCEPTED")])
        | .rejected msg => out := out.push (Json.mkObj [("source", src), ("kernel", "REJECTED"), ("message", msg)])
    return out
  IO.FS.writeFile outPath ((Json.mkObj [("schema", "rocq2lean-replay/1"), ("results", Json.arr out)]).pretty ++ "\n")

end Rocq2Lean

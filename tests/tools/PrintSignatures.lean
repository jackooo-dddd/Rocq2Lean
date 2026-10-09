import Rocq2Lean.IR
import Rocq2Lean.Signature
open Lean Rocq2Lean

/-- Usage: lake env lean --run tests/tools/PrintSignatures.lean FILE.ndjson -/
def main (args : List String) : IO Unit := do
  let src ← IO.ofExcept (IR.parseSource (← IO.FS.readFile args[0]!))
  for (n, j) in src.rawDecls.toList do
    if (j.getObjValAs? String "kind").toOption == some "inductive" then
      IO.println s!"{n}\n{canonicalSignature j}\n"

import Lean
import Rocq2Lean.Emit
import Rocq2Lean.Command
import Rocq2Lean.Sha256

/-!
# `#rocq2lean_assemble` (docs/ASSEMBLY.md)

`#rocq2lean_assemble "source.ndjson" "<ir sha256>" "contract.json" "<sha256>" "validated_report.json"
"<sha256>" "proofs.json" "<sha256>" "assembly_report.json"` runs in a module that imports the validated
statement library (`Rocq2LeanOut`) and the verified proof-template modules listed in `proofs.json`
(`[{"leaf", "template", "task_id", …}]`). Every input is bound by its SHA-256 (checked here, in Lean),
the validated report must be the translation of this IR under this contract, and the translation runs
under the contract's protection binding exactly as `#rocq2lean_import` does. The export is translated
again in assembly mode (`translateSource … (asm? := …)`, `Emit.lean`): validated rows are reproduced
and matched against the imported library, proof tasks get their final theorems where the kernel
accepts the instantiated template at the final statement, and pending rows whose prerequisites are
all assembled become `Rocq.*` declarations. The report lists every row with its assembly state.

The command fails (and the module does not build) if a validated row is not reproduced exactly, or if
a row is missing — never because a prerequisite was simply not supplied (that row stays pending).
-/

namespace Rocq2Lean

open Lean Elab Command

syntax (name := rocqAssemble) "#rocq2lean_assemble " str str str str str str str str str : command

private def readBound (path wantSha : String) (what : String) : IO Json := do
  let bytes ← IO.FS.readBinFile path
  let got := Sha256.hexDigest bytes
  unless got == wantSha do throw <| IO.userError s!"ASSEMBLY_INPUT_REJECTED: {what} {path} has SHA-256 {got}, expected {wantSha}"
  let some txt := String.fromUTF8? bytes | throw <| IO.userError s!"ASSEMBLY_INPUT_REJECTED: {what} is not UTF-8"
  IO.ofExcept (Json.parse txt)

@[command_elab rocqAssemble] def elabRocqAssemble : CommandElab := fun stx => do
  let args := (List.range 9).map fun i => (stx[i + 1].isStrLit?).getD ""
  let [srcPath, irSha, conPath, conSha, valPath, valSha, prfPath, prfSha, outPath] := args
    | throwError "#rocq2lean_assemble: expected nine string arguments"
  let bytes ← IO.FS.readBinFile srcPath
  unless Sha256.hexDigest bytes == irSha do throwError "ASSEMBLY_INPUT_REJECTED: {srcPath} is not the bound IR"
  let some contents := String.fromUTF8? bytes | throwError "ASSEMBLY_INPUT_REJECTED: source is not UTF-8"
  let source ← match IR.parseSource contents with
    | .ok s => pure s
    | .error e => throwError "ASSEMBLY_INPUT_REJECTED: {e}"
  let (protJson, protNames) ← readProtection conPath conSha irSha
  let validated ← readBound valPath valSha "validated report"
  unless (validated.getObjValAs? String "input_sha256").toOption == some irSha do
    throwError "ASSEMBLY_INPUT_REJECTED: the validated report is not the translation of this IR"
  let contract ← IO.ofExcept (Json.parse (← IO.FS.readFile conPath))
  unless (validated.getObjValAs? String "run_id").toOption == (contract.getObjValAs? String "run_id").toOption do
    throwError "ASSEMBLY_INPUT_REJECTED: the validated report and the contract belong to different runs"
  let proofs ← readBound prfPath prfSha "proof manifest"
  let rows ← IO.ofExcept (validated.getObjValAs? (Array Json) "results")
  let vmap : Std.HashMap String Json := rows.foldl (fun m r => m.insert ((r.getObjValAs? String "source").toOption.getD "") r) {}
  let entries ← IO.ofExcept (proofs.getObjValAs? (Array Json) "proofs")
  let mut tmpls : Std.HashMap String Name := {}
  for e in entries do
    let leaf ← IO.ofExcept (e.getObjValAs? String "leaf")
    let t ← IO.ofExcept (e.getObjValAs? String "template")
    if tmpls.contains leaf then throwError "ASSEMBLY_INPUT_REJECTED: two proofs for {leaf}"
    unless (← getEnv).contains t.toName do throwError "ASSEMBLY_INPUT_REJECTED: template {t} is not imported"
    tmpls := tmpls.insert leaf t.toName
  let results ← liftTermElabM (translateSource source protNames (asm? := some { validated := vmap, templates := tmpls }))
  let roots := rootSummary source results
  let count (p : DeclResult → Bool) := (results.filter p).size
  let st (s : String) := count (·.assembly == s)
  let pf (s : String) := count (·.proofState == s)
  let pendingSt (s : String) := s == "OBLIGATIONS_PENDING" || s == "PENDING_KERNEL_CHECKED" || s == "STATEMENT_PENDING_KERNEL_CHECKED"
  let bad := roots.filter fun r => !(r.2.2 == "TRANSLATED_AND_CHECKED" || r.2.2 == "STATEMENT_KERNEL_CHECKED" || pendingSt r.2.2)
  let pendingRoots := roots.filter (pendingSt ·.2.2)
  let fatal := results.filter fun r => r.assembly == "REUSE_MISMATCH" || r.assembly == "ASSEMBLY_REJECTED" && r.verbatim.isNone
  let leaves := results.filter fun r => r.proofState != ""
  -- complete: every row accepted (validated or assembled) and every proof task's final theorem assembled
  let complete := results.all (fun r => r.assembly == "VALIDATED" || r.assembly == "ASSEMBLED") &&
    leaves.all (·.proofState == "PROOF_ASSEMBLED") && results.all (fun r => !r.status.startsWith "STATEMENT_" || r.proofState == "PROOF_ASSEMBLED")
  let summary := Json.mkObj [
    ("rows", results.size), ("validated", st "VALIDATED"), ("assembled", st "ASSEMBLED"), ("pending", st "PENDING"),
    ("opaque_binding_pending", st "OPAQUE_BINDING_PENDING"), ("assembly_blocked", st "ASSEMBLY_BLOCKED"),
    ("assembly_rejected", st "ASSEMBLY_REJECTED"), ("not_translated", st "NOT_TRANSLATED"),
    ("reuse_mismatch", st "REUSE_MISMATCH"),
    ("proof_tasks", leaves.size), ("proofs_assembled", pf "PROOF_ASSEMBLED"), ("proofs_not_supplied", pf "PROOF_NOT_SUPPLIED"),
    ("transport_required", pf "ASSEMBLY_TRANSPORT_REQUIRED"), ("opaque_values_unbound", pf "OPAQUE_BINDING_PENDING"),
    ("complete", complete)]
  let report := Json.mkObj [
    ("report", "rocq2lean-assembly/1"),
    ("status", if !fatal.isEmpty then "ASSEMBLY_REJECTED" else if !bad.isEmpty then "ROOTS_NOT_TRANSLATED"
               else if pendingRoots.isEmpty then "OK" else "OK_OBLIGATIONS_PENDING"),
    ("lean_version", Lean.versionString),
    ("source", srcPath), ("input_sha256", irSha),
    ("run_id", (validated.getObjValAs? String "run_id").toOption.getD ""),
    ("validated_report_sha256", valSha), ("proofs_sha256", prfSha),
    ("source_header", source.header), ("protection", protJson),
    ("roots", Json.arr (roots.map fun (q, n, s) => Json.mkObj [("requested", q), ("name", n), ("status", s)])),
    ("assembly", summary),
    ("results", Json.arr (results.map (·.toJson)))]
  IO.FS.writeFile outPath (report.pretty ++ "\n")
  unless fatal.isEmpty do
    throwError "ASSEMBLY_REJECTED: {fatal.size} row(s) not reproduced: {(fatal.map fun r => s!"{r.source}: {r.assembly} {r.assemblyNote}").toList.take 10}"
  logInfo m!"rocq2lean assemble: {summary.compress}"

end Rocq2Lean

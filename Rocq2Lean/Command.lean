import Lean
import Rocq2Lean.Emit
import Rocq2Lean.Sha256

/-!
# `#rocq2lean_import`

`#rocq2lean_import "source.ndjson" "report.json" "<sha256>" "<run id>"` translates an export,
refusing to start unless the file's SHA-256 is the expected one and the request recorded in the
export is a valid root contract (non-empty, no duplicate spellings or resolutions, every root an
exported constant or inductive). It adds the accepted declarations to the current module (so the
module's `.olean` carries them), and writes the report. The command fails — and so the module
fails to build — unless every requested root is `TRANSLATED_AND_CHECKED`; the report is written
in either case, with a top-level `status` (`OK`, `ROOTS_NOT_TRANSLATED` or
`ROOT_CONTRACT_REJECTED`).
-/

namespace Rocq2Lean

open Lean Elab Command

syntax (name := rocqImport) "#rocq2lean_import " str str str str : command

/-- Root records of the report: the requested spelling, the resolved declaration and the status
of that declaration's (unique) result row. -/
def rootSummary (src : IR.Source) (results : Array DeclResult) : Array (String × String × String) :=
  src.roots.map fun r =>
    (r.requested, r.name, match results.filter (·.source == r.name) with
      | #[d] => d.status
      | #[] => "MISSING_FROM_RESULTS"
      | _ => "DUPLICATE_RESULTS")

/-- Problems with the request recorded in the export: empty, an empty or duplicate spelling, two
spellings resolving to one declaration, or a root that is not an exported declaration. -/
def rootContractProblem (src : IR.Source) : Option String := Id.run do
  if src.roots.isEmpty then return some "the export records no requested root"
  let reqs := src.roots.map (·.requested)
  let names := src.roots.map (·.name)
  for i in [0:reqs.size] do
    if reqs[i]!.all Char.isWhitespace then return some "empty root name"
    if (reqs.extract 0 i).contains reqs[i]! then return some s!"duplicate requested root {reqs[i]!}"
    if (names.extract 0 i).contains names[i]! then
      return some s!"requested roots resolve to the same declaration {names[i]!}"
  for n in names do
    unless src.decls.any (·.name == n) do return some s!"root {n} is not an exported declaration"
  return none

@[command_elab rocqImport] def elabRocqImport : CommandElab := fun stx => do
  let some srcPath := stx[1].isStrLit? | throwError "expected a source path"
  let some repPath := stx[2].isStrLit? | throwError "expected a report path"
  let some wantSha := stx[3].isStrLit? | throwError "expected the source SHA-256"
  let some runId := stx[4].isStrLit? | throwError "expected a run id"
  let bytes ← IO.FS.readBinFile srcPath
  let gotSha := Sha256.hexDigest bytes
  unless gotSha == wantSha do
    throwError "EXPORT_VALIDATION_FAILED: {srcPath} has SHA-256 {gotSha}, expected {wantSha}"
  let some contents := String.fromUTF8? bytes | throwError "EXPORT_VALIDATION_FAILED: source is not UTF-8"
  let source ← match IR.parseSource contents with
    | .ok s => pure s
    | .error e => throwError "EXPORT_VALIDATION_FAILED: {e}"
  if let some msg := rootContractProblem source then
    IO.FS.writeFile repPath ((Json.mkObj [
      ("report", "rocq2lean-translation/0.3"), ("status", "ROOT_CONTRACT_REJECTED"), ("reason", msg),
      ("lean_version", Lean.versionString), ("source", srcPath), ("input_sha256", gotSha), ("run_id", runId),
      ("roots", Json.arr #[]), ("results", Json.arr #[])]).pretty ++ "\n")
    throwError "ROOT_CONTRACT_REJECTED: {msg}"
  let results ← liftTermElabM (translateSource source)
  let roots := rootSummary source results
  let count (p : DeclResult → Bool) := (results.filter p).size
  let rootNames := source.roots.map (·.name)
  let summary := Json.mkObj [
    ("roots", rootNames.size),
    ("translated_dependencies",
      count fun r => r.status == "TRANSLATED_AND_CHECKED" && !rootNames.contains r.source),
    ("bootstrap_resolved", count (·.status == "BOOTSTRAP_RESOLVED")),
    ("generated_helpers", 0),
    ("not_ok", count (!·.ok))]
  let bad := roots.filter (·.2.2 != "TRANSLATED_AND_CHECKED")
  let report := Json.mkObj [
    ("report", "rocq2lean-translation/0.3"),
    ("status", if bad.isEmpty then "OK" else "ROOTS_NOT_TRANSLATED"),
    ("lean_version", Lean.versionString),
    ("source", srcPath),
    ("input_sha256", gotSha),
    ("run_id", runId),
    ("source_header", source.header),
    ("roots", Json.arr (roots.map fun (q, n, s) => Json.mkObj [("requested", q), ("name", n), ("status", s)])),
    ("summary", summary),
    ("results", Json.arr (results.map (·.toJson)))]
  IO.FS.writeFile repPath (report.pretty ++ "\n")
  unless bad.isEmpty do
    let details := results.filter (!·.ok) |>.map fun r =>
      s!"  {r.source}: {r.status} {r.message} {if r.path.isEmpty then "" else s!"at {r.path}"}"
    throwError "rocq2lean: requested roots not translated: {bad}\n{String.intercalate "\n" details.toList}"
  logInfo m!"rocq2lean: {roots.size} root(s) TRANSLATED_AND_CHECKED; summary {summary.compress}"

end Rocq2Lean

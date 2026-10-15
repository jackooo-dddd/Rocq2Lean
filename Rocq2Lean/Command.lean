import Lean
import Rocq2Lean.Emit
import Rocq2Lean.Sha256

/-!
# `#rocq2lean_import`

`#rocq2lean_import "source.ndjson" "report.json" "<sha256>" "<run id>" ["contract.json" "<sha256>"]`
translates an export,
refusing to start unless the file's SHA-256 is the expected one and the request recorded in the
export is a valid root contract (non-empty, no duplicate spellings or resolutions, every root an
exported constant or inductive). It adds the accepted declarations to the current module (so the
module's `.olean` carries them), and writes the report. The command fails — and so the module
fails to build — unless every requested root is `TRANSLATED_AND_CHECKED`; the report is written
in either case, with a top-level `status` (`OK`, `ROOTS_NOT_TRANSLATED` or
`ROOT_CONTRACT_REJECTED`).

P0: with the export's coverage contract (and its SHA-256), the contract's `protection` binding — the
protected public declarations of the pinned inventory present in this export — is enforced by the
translator: a protected declaration keeps its full statement (`INTERFACE_REJECTED` otherwise). The
contract must be bound to this IR and must carry the binding; translating without a contract (a
diagnostic translate-only run) records `protection: null`, and such a run cannot be verified.
-/

namespace Rocq2Lean

open Lean Elab Command

syntax (name := rocqImport) "#rocq2lean_import " str str str str (str str)? : command

/-- The contract's protection binding for an export with IR digest `irSha`: its JSON (for the report)
and the protected declaration names. -/
def readProtection (path wantSha irSha : String) : IO (Json × Std.HashSet String) := do
  let bytes ← IO.FS.readBinFile path
  let got := Sha256.hexDigest bytes
  unless got == wantSha do throw <| IO.userError s!"PROTECTION_REJECTED: {path} has SHA-256 {got}, expected {wantSha}"
  let some txt := String.fromUTF8? bytes | throw <| IO.userError "PROTECTION_REJECTED: contract is not UTF-8"
  let con ← IO.ofExcept (Json.parse txt)
  unless (con.getObjValAs? String "ir_sha256").toOption == some irSha do
    throw <| IO.userError "PROTECTION_REJECTED: the contract is not bound to this export"
  let prot ← match con.getObjVal? "protection" with
    | .ok p@(.obj _) => pure p
    | _ => throw <| IO.userError "PROTECTION_REJECTED: the contract carries no protection binding"
  let names ← IO.ofExcept (prot.getObjValAs? (Array String) "protected")
  let summary := Json.mkObj [("contract_sha256", got),
    ("manifest_sha256", (prot.getObjVal? "manifest_sha256").toOption.getD .null),
    ("protected_in_export", names.size)]
  return (summary, names.foldl (·.insert ·) {})

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
  -- the optional `(str str)?` group: a null node with the two literals, or with none
  let opt := stx[5].getArgs
  let conArg : Option (String × String) :=
    if opt.size == 2 then match opt[0]!.isStrLit?, opt[1]!.isStrLit? with
      | some a, some b => if a.isEmpty then none else some (a, b)
      | _, _ => none
    else none
  let tStart ← IO.monoMsNow
  let bytes ← IO.FS.readBinFile srcPath
  let gotSha := Sha256.hexDigest bytes
  let tSha ← IO.monoMsNow
  unless gotSha == wantSha do
    throwError "EXPORT_VALIDATION_FAILED: {srcPath} has SHA-256 {gotSha}, expected {wantSha}"
  let some contents := String.fromUTF8? bytes | throwError "EXPORT_VALIDATION_FAILED: source is not UTF-8"
  let source ← match IR.parseSource contents with
    | .ok s => pure s
    | .error e => throwError "EXPORT_VALIDATION_FAILED: {e}"
  let tParse ← IO.monoMsNow
  if let some msg := rootContractProblem source then
    IO.FS.writeFile repPath ((Json.mkObj [
      ("report", "rocq2lean-translation/0.3"), ("status", "ROOT_CONTRACT_REJECTED"), ("reason", msg),
      ("lean_version", Lean.versionString), ("source", srcPath), ("input_sha256", gotSha), ("run_id", runId),
      ("roots", Json.arr #[]), ("results", Json.arr #[])]).pretty ++ "\n")
    throwError "ROOT_CONTRACT_REJECTED: {msg}"
  let (protJson, protNames) ← match conArg with
    | some (p, h) => readProtection p h gotSha
    | none => pure (Json.null, {})
  let results ← liftTermElabM (translateSource source protNames)
  let tTrans ← IO.monoMsNow
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
  -- timing (entry 14), outside the (deterministic, bound) report: phases and per-declaration attempts
  let timing := Json.mkObj [
    ("schema", "rocq2lean-translation-timing/1"),
    ("phase_ms", Json.mkObj [("sha256", Json.num (tSha - tStart)), ("parse", Json.num (tParse - tSha)),
                             ("translate", Json.num (tTrans - tParse))]),
    ("declarations", Json.arr (results.map fun r => Json.mkObj [("source", r.source), ("status", r.status),
      ("time_ms", Json.num r.timeMs),
      ("tier_times", Json.arr (r.tierTimes.map fun (l, ms, st) => Json.arr #[Json.str l, Json.num ms, Json.str st]))]))]
  IO.FS.writeFile ((System.FilePath.mk repPath).withFileName "translation_timing.json") (timing.compress ++ "\n")
  -- statement mode: a root translated as its statement, or pending on proofs, is not a failure
  let pendingSt (s : String) := s == "OBLIGATIONS_PENDING" || s == "PENDING_KERNEL_CHECKED" ||
    s == "STATEMENT_PENDING_KERNEL_CHECKED"
  let bad := roots.filter fun r => !(r.2.2 == "TRANSLATED_AND_CHECKED" || r.2.2 == "STATEMENT_KERNEL_CHECKED" || pendingSt r.2.2)
  let pendingRoots := roots.filter (pendingSt ·.2.2)
  let report := Json.mkObj [
    ("report", "rocq2lean-translation/0.3"),
    ("status", if !bad.isEmpty then "ROOTS_NOT_TRANSLATED" else if pendingRoots.isEmpty then "OK" else "OK_OBLIGATIONS_PENDING"),
    ("lean_version", Lean.versionString),
    ("source", srcPath),
    ("input_sha256", gotSha),
    ("run_id", runId),
    ("source_header", source.header),
    ("protection", protJson),
    ("roots", Json.arr (roots.map fun (q, n, s) => Json.mkObj [("requested", q), ("name", n), ("status", s)])),
    ("summary", summary),
    ("results", Json.arr (results.map (·.toJson)))]
  IO.FS.writeFile repPath (report.pretty ++ "\n")
  -- statement mode: the module of the claimed rows is still produced (validated row by row); the
  -- report's status records the untranslated roots and the CLI exits non-zero
  let stmtMode := (source.header.getObjValAs? String "mode").toOption.isNone &&
    ((source.header.getObjVal? "mode").toOption.bind (fun m => (m.getObjValAs? String "name").toOption)) == some "statement"
  unless bad.isEmpty do
    let details := results.filter (!·.ok) |>.map fun r =>
      s!"  {r.source}: {r.status} {r.message} {if r.path.isEmpty then "" else s!"at {r.path}"}"
    if stmtMode then
      logWarning m!"rocq2lean: {bad.size} requested root(s) not translated (statement mode: module kept for the claimed rows)"
    else
      throwError "rocq2lean: requested roots not translated: {bad}\n{String.intercalate "\n" details.toList}"
  logInfo m!"rocq2lean: {roots.size} root(s) TRANSLATED_AND_CHECKED; summary {summary.compress}"

end Rocq2Lean

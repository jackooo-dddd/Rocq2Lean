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

/-- Incremental runs (docs/INCREMENTAL.md): the base run in directory `dir` (its report, replay records,
timing and module), for an export with SHA-256 `irSha`; `rerunPath`: the declarations to translate again,
one per line. -/
def loadReplay (dir : System.FilePath) (irSha : String) (rerunPath : Option String) : IO ReplayInput := do
  let fail (m : String) : IO ReplayInput := throw <| IO.userError s!"REPLAY_REJECTED: {m}"
  -- the report: streamed, one row per line after the `results` line (`,` after each row but the last, `]}`)
  let repLines ← IO.FS.lines (dir / "translation_report.json")
  unless repLines.any (· == s!"\"input_sha256\": {(Json.str irSha).compress},") do
    return ← fail s!"the base run in {dir} did not translate this export"
  let some k := repLines.findIdx? (· == "\"results\": [") | return ← fail "base report without streamed rows"
  let mut lines : Std.HashMap String String := {}
  for i in [k+1:repLines.size] do
    let l := repLines[i]!
    let raw := if i + 1 == repLines.size then l.dropRight 2 else l.dropRight 1
    if raw.isEmpty then continue
    let j ← IO.ofExcept (Json.parse raw)
    lines := lines.insert ((j.getObjValAs? String "source").toOption.getD "") raw
  let mut records : Std.HashMap String Json := {}
  for l in ← IO.FS.lines (dir / "replay_records.jsonl") do
    if l.isEmpty then continue
    let j ← IO.ofExcept (Json.parse l)
    records := records.insert ((j.getObjValAs? String "decl").toOption.getD "") j
  let tj ← IO.ofExcept (Json.parse (← IO.FS.readFile (dir / "translation_timing.json")))
  let mut timing : Std.HashMap String (Nat × Array (String × Nat × String)) := {}
  for e in (tj.getObjValAs? (Array Json) "declarations").toOption.getD #[] do
    let tiers := ((e.getObjValAs? (Array Json) "tier_times").toOption.getD #[]).filterMap fun t => match t with
      | .arr #[.str l, .num ms, .str st] => some (l, ms.mantissa.toNat, st)
      | _ => none
    timing := timing.insert ((e.getObjValAs? String "source").toOption.getD "") ((e.getObjValAs? Nat "time_ms").toOption.getD 0, tiers)
  -- (the region stays mapped: the declarations are installed from it)
  let (md, _) ← readModuleData (dir / "lean" / "Rocq2LeanOut.olean")
  let consts := md.constants.foldl (fun m c => m.insert c.name c) ({} : Std.HashMap Name ConstantInfo)
  let rerun ← match rerunPath with
    | some p => pure ((← IO.FS.lines p).foldl (fun s l => if l.trim.isEmpty then s else s.insert l.trim) ({} : Std.HashSet String))
    | none => pure {}
  return { lines, records, timing, consts, rerun }

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
  -- incremental (docs/INCREMENTAL.md): `R2L_REPLAY_BASE=<run directory>`, `R2L_RERUN=<file>`
  let repDir := (System.FilePath.mk repPath).parent.getD "."
  let rep? ← match ← IO.getEnv "R2L_REPLAY_BASE" with
    | some dir =>
      if (← IO.FS.realPath dir) == (← IO.FS.realPath repDir) then
        throwError "REPLAY_REJECTED: the base run is this run"
      some <$> loadReplay dir gotSha (← IO.getEnv "R2L_RERUN")
    | none => pure none
  let tRep ← IO.monoMsNow
  let results ← liftTermElabM (translateSource source protNames (rep? := rep?))
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
                             ("replay_load", Json.num (tRep - tParse)), ("translate", Json.num (tTrans - tRep))]),
    ("declarations", Json.arr (results.map fun r => Json.mkObj <| [("source", r.source), ("status", r.status),
      ("time_ms", Json.num r.timeMs)] ++ (if r.replayed then [("replayed", Json.bool true)] else []) ++ [
      ("tier_times", Json.arr (r.tierTimes.map fun (l, ms, st) => Json.arr #[Json.str l, Json.num ms, Json.str st]))]))]
  IO.FS.writeFile ((System.FilePath.mk repPath).withFileName "translation_timing.json") (timing.compress ++ "\n")
  -- statement mode: a root translated as its statement, or pending on proofs, is not a failure
  let pendingSt (s : String) := s == "OBLIGATIONS_PENDING" || s == "PENDING_KERNEL_CHECKED" ||
    s == "STATEMENT_PENDING_KERNEL_CHECKED"
  let bad := roots.filter fun r => !(r.2.2 == "TRANSLATED_AND_CHECKED" || r.2.2 == "STATEMENT_KERNEL_CHECKED" || pendingSt r.2.2)
  let pendingRoots := roots.filter (pendingSt ·.2.2)
  let head : List (String × Json) := [
    ("report", "rocq2lean-translation/0.3"),
    ("status", if !bad.isEmpty then "ROOTS_NOT_TRANSLATED" else if pendingRoots.isEmpty then "OK" else "OK_OBLIGATIONS_PENDING"),
    ("lean_version", Lean.versionString),
    ("source", srcPath),
    ("input_sha256", gotSha),
    ("run_id", runId),
    ("source_header", source.header),
    ("protection", protJson),
    ("roots", Json.arr (roots.map fun (q, n, s) => Json.mkObj [("requested", q), ("name", n), ("status", s)])),
    ("summary", summary)]
  -- the report is streamed, one row per line (the same JSON value as one `Json.mkObj` with a `results`
  -- array): a corpus report is several GB, and building it as one tree and one string exhausted the memory
  -- (S21, exit 137 after translation). Each value is rendered by the pretty printer on one line, so object
  -- keys keep the pretty printer's order (`compress` orders them differently; the hardening suites' targeted
  -- mutations walk the report in key order)
  let line (j : Json) : String := j.pretty (lineWidth := 1000000000)
  IO.FS.withFile repPath .write fun h => do
    h.putStr "{"
    for (k, v) in head do
      h.putStr s!"{(Json.str k).compress}: {line v},\n"
    h.putStr "\"results\": ["
    let mut first := true
    for r in results do
      h.putStr (if first then "\n" else ",\n")
      -- (a replayed row is the base report's line, byte for byte)
      h.putStr (match r.verbatimRaw with | some raw => raw | none => line r.toJson)
      first := false
    h.putStr "]}\n"
  -- incremental (docs/INCREMENTAL.md): this run's replay records, so that it can be a base run; with a base,
  -- what was replayed, translated and changed
  IO.FS.withFile (repDir / "replay_records.jsonl") .write fun h => do
    for j in ← replayRecords.get do h.putStrLn j.compress
  if rep?.isSome then
    let changed ← replayChanged.get
    let fallback ← replayFallback.get
    let recs ← replayRecords.get
    let selfBad := recs.filter fun j => (j.getObjVal? "selfcheck").isOk
    IO.FS.writeFile (repDir / "replay_summary.json") ((Json.mkObj [
      ("schema", "rocq2lean-replay-summary/1"),
      ("base", (← IO.getEnv "R2L_REPLAY_BASE").getD ""),
      ("rerun_requested", ((← IO.getEnv "R2L_RERUN").getD "")),
      ("rows", results.size),
      ("rows_replayed", (results.filter (·.replayed)).size),
      ("rows_translated", (results.filter (!·.replayed)).size),
      ("changed", Json.arr (changed.map Json.str)),
      ("fallback", Json.arr (fallback.map fun (n, m) => Json.mkObj [("decl", n), ("reason", m)])),
      ("selfcheck_failures", Json.arr (selfBad.map fun j => (j.getObjVal? "decl").toOption.getD .null)),
      ("load_ms", Json.num (tRep - tParse)), ("translate_ms", Json.num (tTrans - tRep))]).pretty ++ "\n")
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

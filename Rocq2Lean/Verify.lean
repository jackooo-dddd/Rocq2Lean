import Lean
import Rocq2Lean.Emit
import Rocq2Lean.Bootstrap

/-!
# `#rocq2lean_verify "contract.json" "report.json" "result.json"`

Fresh-process consumer check. Run in a *separate* module that imports the generated one. The
expected roots and the required dependency closure come from the **coverage contract**
written at export time from the validated source IR (never from the report under audit).

Detectors (each recorded separately in `result.json`):

* `binding` — report `run_id` / `input_sha256` equal the contract's;
* `coverage` — exactly one result per exported declaration; every declaration of the required
  closure accepted (`TRANSLATED_AND_CHECKED`, or `BOOTSTRAP_RESOLVED` for bootstrap rules);
  every requested root `TRANSLATED_AND_CHECKED`; at least one accepted declaration;
* `roots` — the report's status is `OK` and its root records equal the contract's roots
  (requested spelling and resolved declaration, in order), each with its result row's status;
* `presence`, `kind`, `type`, `value`, `levels`, `ctors` — the imported declaration equals the
  reported one;
* `safety` — not `unsafe`/`partial`;
* `axioms` — empty transitive axiom set (`collectAxioms`), standard Lean axioms included;
* `target_deps` — every constant referenced by an accepted target is an accepted target of
  this run, a bootstrap target, or a kernel-generated constructor/recursor of one.

Any failure fails the module (non-zero exit of the consumer process).
-/

namespace Rocq2Lean

open Lean Elab Command Meta

syntax (name := rocqVerify) "#rocq2lean_verify " str str str : command

/-- Obligation for every recursor application `I.rec params motive minors idx major` occurring in
an accepted value: `idx` are exactly the indices of the (weak-head normalized) type of `major`.
Returns the number of checked applications and any violations. -/
def checkRecIndices (v : Expr) : MetaM (Nat × Array String) := do
  let checked ← IO.mkRef 0
  let bad ← IO.mkRef (#[] : Array String)
  discard <| Meta.transform v (post := fun e => do
    if let .const r _ := e.getAppFn then
      if let some (.recInfo rv) := (← getEnv).find? r then
        let args := e.getAppArgs
        let n := rv.numParams + rv.numMotives + rv.numMinors + rv.numIndices + 1
        if args.size ≥ n then
          let major := args[n - 1]!
          let idx := args.extract (rv.numParams + rv.numMotives + rv.numMinors) (n - 1)
          let mty ← whnf (← inferType major)
          let margs := mty.getAppArgs
          let want := margs.extract rv.numParams margs.size
          checked.modify (· + 1)
          unless want.size == idx.size && (want.zip idx).all (fun (a, b) => a == b) do
            unless want.size == idx.size && (← (want.zip idx).allM fun (a, b) => isDefEq a b) do
              bad.modify (·.push s!"{r}: indices differ from the major premise's type")
    return .continue)
  return (← checked.get, ← bad.get)

/-- Kernel metadata of a recursor, for the independent audit. -/
def recursorJson (rv : RecursorVal) : Json :=
  Json.mkObj [("name", rv.name.toString), ("level_params", Json.arr (rv.levelParams.map (Json.str ·.toString)).toArray),
    ("num_params", rv.numParams), ("num_indices", rv.numIndices), ("num_motives", rv.numMotives),
    ("num_minors", rv.numMinors), ("rule_nfields", Json.arr (rv.rules.map (fun r => Json.num r.nfields)).toArray),
    ("type", exprJson rv.type)]

private def kindOf : ConstantInfo → String
  | .defnInfo _ => "def"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"
  | .axiomInfo _ => "axiom"
  | .quotInfo _ => "quot"

private def getStr (j : Json) (k : String) : String := (j.getObjValAs? String k).toOption.getD ""

@[command_elab rocqVerify] def elabRocqVerify : CommandElab := fun stx => do
  let some conPath := stx[1].isStrLit? | throwError "expected a contract path"
  let some repPath := stx[2].isStrLit? | throwError "expected a report path"
  let some outPath := stx[3].isStrLit? | throwError "expected a result path"
  let contract ← IO.ofExcept (Json.parse (← IO.FS.readFile conPath))
  let report ← IO.ofExcept (Json.parse (← IO.FS.readFile repPath))
  let results ← IO.ofExcept (report.getObjValAs? (Array Json) "results")
  let reqRoots ← IO.ofExcept (contract.getObjValAs? (Array Json) "roots")
  let required ← IO.ofExcept (contract.getObjValAs? (Array String) "required_closure")
  let exported ← IO.ofExcept (contract.getObjValAs? (Array String) "exported")
  let mut problems : Array (String × String) := #[]
  let mut detectors : Std.HashMap String Nat := {}
  let note (det msg : String) (ps : Array (String × String)) := ps.push (det, msg)
  -- binding
  if getStr report "run_id" != getStr contract "run_id" then
    problems := note "binding" "report run_id differs from the contract" problems
  if getStr report "input_sha256" != getStr contract "ir_sha256" then
    problems := note "binding" "report input_sha256 differs from the contract's IR digest" problems
  -- coverage: exactly one row per exported declaration, none extra
  let mut rows : Std.HashMap String (Array Json) := {}
  for r in results do
    let s := getStr r "source"
    rows := rows.insert s ((rows.getD s #[]).push r)
  for (s, rs) in rows.toList do
    if rs.size != 1 then problems := note "coverage" s!"{s}: {rs.size} result rows" problems
    unless exported.contains s do problems := note "coverage" s!"{s}: result for a declaration that was not exported" problems
  for s in exported do
    unless rows.contains s do problems := note "coverage" s!"{s}: exported declaration has no result" problems
  let status (s : String) : String := match rows[s]? with
    | some #[r] => getStr r "status"
    | _ => "MISSING"
  for s in required do
    let st := status s
    let okBootstrap := st == "BOOTSTRAP_RESOLVED" && (findBootstrap? s).isSome
    unless st == "TRANSLATED_AND_CHECKED" || okBootstrap do
      problems := note "coverage" s!"required declaration {s} has status {st}" problems
  for r in reqRoots do
    let c := getStr r "canonical"
    if status c != "TRANSLATED_AND_CHECKED" then
      problems := note "coverage" s!"requested root {getStr r "requested"} ({c}) has status {status c}" problems
  -- roots: the report's own root records are exactly the contract's roots (requested spelling
  -- and resolution, in order), each with the status of its result row; the report status is OK.
  let repRoots := (report.getObjValAs? (Array Json) "roots").toOption.getD #[]
  if getStr report "status" != "OK" then
    problems := note "roots" s!"report status is '{getStr report "status"}', not OK" problems
  if repRoots.size != reqRoots.size then
    problems := note "roots" s!"report has {repRoots.size} root record(s), the contract requests {reqRoots.size}" problems
  for rr in repRoots, cr in reqRoots do
    if getStr rr "requested" != getStr cr "requested" || getStr rr "name" != getStr cr "canonical" then
      problems := note "roots" (s!"report root record {getStr rr "requested"} ↦ {getStr rr "name"} differs from " ++
        s!"contract root {getStr cr "requested"} ↦ {getStr cr "canonical"}") problems
  for rr in repRoots do
    if getStr rr "status" != status (getStr rr "name") then
      problems := note "roots" (s!"report root record {getStr rr "name"} says {getStr rr "status"}, " ++
        s!"its result row says {status (getStr rr "name")}") problems
  -- allowed target constants
  let mut allowed : Std.HashSet Name := {}
  let mut accepted : Array (String × Json) := #[]
  for s in required do
    match rows[s]? with
    | some #[r] =>
      let st := getStr r "status"
      if st == "TRANSLATED_AND_CHECKED" then
        let t := (getStr r "target").toName
        allowed := allowed.insert t
        if getStr r "target_kind" == "inductive" then
          allowed := allowed.insert (t.str "rec")
          for c in (r.getObjValAs? (Array Json) "target_ctors").toOption.getD #[] do
            allowed := allowed.insert (getStr c "name").toName
        accepted := accepted.push (s, r)
      else if st == "BOOTSTRAP_RESOLVED" then
        if let some rule := findBootstrap? s then
          for t in rule.target.types do allowed := allowed.insert t |>.insert (t.str "rec")
          for cs in rule.target.ctors do for c in cs do allowed := allowed.insert c
    | _ => pure ()
  if accepted.isEmpty then problems := note "coverage" "no accepted declaration" problems
  -- per declaration
  let env ← getEnv
  let mut recs : Std.HashMap Name RecursorVal := {}
  let mut recApps : Nat := 0
  for (s, r) in accepted do
    let tgt := getStr r "target"
    let some ci := env.find? tgt.toName
      | problems := note "presence" s!"{tgt} ({s}): not in the imported environment" problems; continue
    let kind := getStr r "target_kind"
    if kindOf ci != kind then problems := note "kind" s!"{tgt}: imported {kindOf ci}, report says {kind}" problems
    if ci.isUnsafe || ci.isPartial then problems := note "safety" s!"{tgt}: unsafe or partial" problems
    let lps := ((r.getObjValAs? (Array String) "level_params").toOption.getD #[]).toList.map String.toName
    if ci.levelParams != lps then problems := note "levels" s!"{tgt}: universe parameters differ" problems
    if (r.getObjValD "target_type") != exprJson ci.type then
      problems := note "type" s!"{tgt}: imported type differs from the reported type" problems
    let mut used : Array Name := ci.type.getUsedConstants
    if let .inductInfo iv := ci then
      let ctors := (r.getObjValAs? (Array Json) "target_ctors").toOption.getD #[]
      if iv.ctors != (ctors.map fun c => (getStr c "name").toName).toList then
        problems := note "ctors" s!"{tgt}: constructors differ from the report" problems
      for c in ctors do
        match env.find? (getStr c "name").toName with
        | some cci =>
          if (c.getObjValD "type") != exprJson cci.type then
            problems := note "ctors" s!"{getStr c "name"}: constructor type differs" problems
          used := used ++ cci.type.getUsedConstants
        | none => problems := note "ctors" s!"{getStr c "name"}: constructor missing" problems
    else
      match ci.value? (allowOpaque := true) with
      | some v =>
        if (r.getObjValD "target_value") != exprJson v then
          problems := note "value" s!"{tgt}: imported value differs from the reported value" problems
        used := used ++ v.getUsedConstants
      | none => problems := note "value" s!"{tgt}: imported declaration has no value" problems
    for c in used do
      unless allowed.contains c do
        problems := note "target_deps" s!"{tgt}: references {c}, which is not part of this run's accepted closure" problems
      if let some (.recInfo rv) := env.find? c then recs := recs.insert c rv
    if let some v := ci.value? (allowOpaque := true) then
      let (n, bad) ← liftTermElabM (checkRecIndices v)
      recApps := recApps + n
      for b in bad do problems := note "rec_indices" s!"{tgt}: {b}" problems
    let axs ← liftCoreM (collectAxioms tgt.toName)
    unless axs.isEmpty do problems := note "axioms" s!"{tgt}: depends on axioms {axs}" problems
  for (d, _) in problems do detectors := detectors.insert d (detectors.getD d 0 + 1)
  let dets := ["binding", "coverage", "roots", "presence", "kind", "safety", "levels", "type", "value", "ctors",
               "target_deps", "axioms", "rec_indices"].map fun d => (d, Json.str (if detectors.getD d 0 == 0 then "OK" else "FAIL"))
  let res := Json.mkObj [
    ("schema", "rocq2lean-consumer/1"), ("status", if problems.isEmpty then "OK" else "AUDIT_REJECTED"),
    ("run_id", getStr contract "run_id"), ("accepted_checked", accepted.size),
    ("recursor_applications_checked", recApps),
    ("recursors", Json.arr (recs.toArray.map (recursorJson ·.2))),
    ("detectors", Json.mkObj dets),
    ("problems", Json.arr (problems.map fun (d, m) => Json.mkObj [("detector", d), ("message", m)]))]
  IO.FS.writeFile outPath (res.pretty ++ "\n")
  unless problems.isEmpty do
    throwError "AUDIT_REJECTED (consumer):\n{String.intercalate "\n" (problems.map fun (d, m) => s!"[{d}] {m}").toList}"
  logInfo m!"rocq2lean verify: {accepted.size} accepted declaration(s) of the required closure match; no axioms"

end Rocq2Lean

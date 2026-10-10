import Lean
import Rocq2Lean.Emit
import Rocq2Lean.Bootstrap
import Rocq2Lean.Replay

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
* `instance_levels` — at every `Eq`/`Eq.refl`/`Eq.rec` occurrence and every large recursor
  application, the typing-determined universe argument equals the level Lean infers here;
* `residual_levels` — every defaulted universe level is justified: the reported generic
  declaration (residuals as fresh universe parameters) is accepted by the kernel here, and
  instantiating its residual parameters with `0` gives exactly the imported declaration;
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

/-- Obligation for the universe arguments that typing determines and no source instance records
(docs/UNIVERSE_TRANSLATION.md, R4): at every occurrence of `Eq.{u} A`, `Eq.refl.{u} A` and
`Eq.rec.{_, u} A`, `u` is the sort level of `A`'s type; at every application of a large recursor
`I.rec.{v, …} params motive …`, `v` is the level of the motive's codomain. Returns the number of
checked arguments and any violations. -/
def checkInstanceLevels (tmpl : Std.HashMap Name (Array (Nat × Nat))) (v : Expr) : MetaM (Nat × Array String) := do
  let checked ← IO.mkRef 0
  let bad ← IO.mkRef (#[] : Array String)
  let same (what : String) (got want : Level) : MetaM Unit := do
    checked.modify (· + 1)
    unless ← isLevelDefEq got want do bad.modify (·.push s!"{what}: argument {got}, typing determines {want}")
  discard <| Meta.transform v (post := fun e => do
    if let .const c us := e.getAppFn then
      let args := e.getAppArgs
      if (c == ``Eq || c == ``Eq.refl) && args.size ≥ 1 && us.length == 1 then
        same s!"{c}" us[0]! (← getLevel args[0]!)
      if c == ``Eq.rec && args.size ≥ 1 && us.length == 2 then
        same s!"{c} (type level)" us[1]! (← getLevel args[0]!)
      let large ← match (← getEnv).find? c with
        | some (.recInfo rv) =>
          if rv.numMotives == 1 && !us.isEmpty then
            -- large eliminator: the motive's codomain is the recursor's first universe parameter
            forallBoundedTelescope rv.type (some (rv.numParams + 1)) fun xs _ => do
              if xs.size != rv.numParams + 1 then return false
              forallTelescopeReducing (← inferType xs.back!) fun _ b => do
                return b.isSort && b.sortLevel! == .param rv.levelParams.head!
          else pure false
        | _ => pure false
      -- R5: a template inductive's level is the level of its template parameter (A : Sort (σ+1))
      if let some bind := tmpl[c]? then
        let off := if large then 1 else 0
        for (j, k) in bind do
          if h : k < args.size then
            if j + off < us.length then
              -- the codomain sort of the argument's type (arity parameters: of the type family)
              let s ← forallTelescopeReducing (← inferType args[k]) fun _ b => do
                match ← whnf b with
                | .sort s => pure (some s)
                | _ => pure none
              match s with
              | some s => same s!"{c} (template level {j} from parameter {k})" (.succ us[j + off]!) s
              | none => bad.modify (·.push s!"{c}: template parameter {k} does not have an arity type")
      if let some (.recInfo rv) := (← getEnv).find? c then
        if rv.numMotives == 1 && args.size > rv.numParams && !us.isEmpty then
          if large then
            let mty ← inferType args[rv.numParams]!
            forallTelescopeReducing mty fun _ b => do
              match (← whnf b) with
              | .sort l => same s!"{c} (motive level)" us[0]! l
              | _ => bad.modify (·.push s!"{c}: motive codomain is not a sort")
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
  -- template inductives of this run (report): head ↦ [(level index, template parameter)]
  let mut tmpl : Std.HashMap Name (Array (Nat × Nat)) := {}
  for (_, r) in accepted do
    if (r.getObjValAs? Bool "template").toOption == some true then
      let lps := (r.getObjValAs? (Array String) "level_params").toOption.getD #[]
      let bind := ((r.getObjValAs? (Array Json) "template_params").toOption.getD #[]).filterMap fun x => do
        let l ← (x.getObjValAs? String "level").toOption
        let k ← (x.getObjValAs? Nat "param").toOption
        let j ← lps.findIdx? (· == (levelParamName l).toString)
        return (j, k)
      let t := (getStr r "target").toName
      for n in #[t, t.str "rec"] ++ ((r.getObjValAs? (Array Json) "target_ctors").toOption.getD #[]).map (fun c => (getStr c "name").toName) do
        tmpl := tmpl.insert n bind
  let mut residualsChecked : Nat := 0
  let mut instChecked : Nat := 0
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
    for e in ci.type :: (ci.value? (allowOpaque := true)).toList do
      let (n, bad) ← liftTermElabM (checkInstanceLevels tmpl e)
      instChecked := instChecked + n
      for b in bad do problems := note "instance_levels" s!"{tgt}: {b}" problems
    -- residual_levels
    let nDefaults := (r.getObjValAs? Nat "universe_level_defaults").toOption.getD 0
    match r.getObjValD "universe_residuals" with
    | .null =>
      if nDefaults != 0 then
        problems := note "residual_levels" s!"{tgt}: {nDefaults} defaulted universe level(s) without a justification" problems
    | res =>
      let parsed : Except String (List Name × List Level × Expr × Expr) := do
        let ps := (← res.getObjValAs? (Array String) "params").toList.map String.toName
        let ds ← (← res.getObjValAs? (Array Json) "defaults").toList.mapM levelOfJson
        return (ps, ds, ← exprOfJson (← res.getObjVal? "generic_type"), ← exprOfJson (← res.getObjVal? "generic_value"))
      match parsed, ci.value? (allowOpaque := true) with
      | .ok (ps, z, gty, gval), some v =>
        if ps.length != nDefaults || ps.any ci.levelParams.contains then
          problems := note "residual_levels" s!"{tgt}: residual parameters {ps} do not match {nDefaults} defaulted level(s)" problems
        -- compared up to universe-level normalization (instantiation may spell levels differently)
        let nl (e : Expr) : Json := exprJson (e.replaceLevel fun l => some l.normalize)
        unless z.length == ps.length && nl (gty.instantiateLevelParams ps z) == nl ci.type &&
            nl (gval.instantiateLevelParams ps z) == nl v do
          problems := note "residual_levels" s!"{tgt}: the generic declaration with its residual levels at their defaults is not the imported one" problems
        let d ← liftTermElabM (mkConstDecl (tgt.toName ++ `_rocq2lean_residual_check) kind (ci.levelParams ++ ps) gty gval)
        match ← liftCoreM (checkOnly d) with
        | .accepted => residualsChecked := residualsChecked + 1
        | .rejected m =>
          problems := note "residual_levels" s!"{tgt}: generic declaration rejected by the kernel, defaults unjustified ({m})" problems
      | .error e, _ => problems := note "residual_levels" s!"{tgt}: unreadable residual record ({e})" problems
      | _, none => problems := note "residual_levels" s!"{tgt}: residual record on a declaration without value" problems
    let axs ← liftCoreM (collectAxioms tgt.toName)
    unless axs.isEmpty do problems := note "axioms" s!"{tgt}: depends on axioms {axs}" problems
  for (d, _) in problems do detectors := detectors.insert d (detectors.getD d 0 + 1)
  let dets := ["binding", "coverage", "roots", "presence", "kind", "safety", "levels", "type", "value", "ctors",
               "target_deps", "axioms", "rec_indices", "residual_levels", "instance_levels"].map fun d => (d, Json.str (if detectors.getD d 0 == 0 then "OK" else "FAIL"))
  let res := Json.mkObj [
    ("schema", "rocq2lean-consumer/1"), ("status", if problems.isEmpty then "OK" else "AUDIT_REJECTED"),
    ("run_id", getStr contract "run_id"), ("accepted_checked", accepted.size),
    ("recursor_applications_checked", recApps),
    ("residual_levels_checked", residualsChecked),
    ("instance_levels_checked", instChecked),
    ("recursors", Json.arr (recs.toArray.map (recursorJson ·.2))),
    ("detectors", Json.mkObj dets),
    ("problems", Json.arr (problems.map fun (d, m) => Json.mkObj [("detector", d), ("message", m)]))]
  IO.FS.writeFile outPath (res.pretty ++ "\n")
  unless problems.isEmpty do
    throwError "AUDIT_REJECTED (consumer):\n{String.intercalate "\n" (problems.map fun (d, m) => s!"[{d}] {m}").toList}"
  logInfo m!"rocq2lean verify: {accepted.size} accepted declaration(s) of the required closure match; no axioms"

end Rocq2Lean

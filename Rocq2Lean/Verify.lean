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
  this run, a bootstrap target, or a kernel-generated constructor/recursor of one;
* `interface` (P0) — the contract carries a protection binding (the pinned inventory's protected
  public declarations present in the export), the report's binding agrees with it, every result row's
  `protected` flag equals membership in it, and no accepted protected declaration was translated with
  a specialized statement (R2B-S result-sort lowering or R2B-P on a statement level), whether it is a
  requested root or a dependency.

Statement mode (the contract's `mode` is `statement`, docs/STATEMENT_ONLY_DESIGN.md): the rows
checked are the rows the translator *claims* — accepted (`TRANSLATED_AND_CHECKED`,
`BOOTSTRAP_RESOLVED`, `STATEMENT_KERNEL_CHECKED`) or pending (`PENDING_KERNEL_CHECKED`,
`STATEMENT_PENDING_KERNEL_CHECKED`) — among all exported declarations; the others are reported, never
accepted, and roots need not all be translated. Additional detectors:

* `namespaces` — accepted targets are `Rocq.*`, pending artifacts `RocqPending.*`;
* `target_deps` — an accepted target references only accepted targets (never a pending artifact);
  a pending artifact also references pending artifacts and proof-task statements;
* `statements` — a proof task is a definition whose type is `Prop` (`….statement`) or a sort
  (`….type`, opaque data), after its hypotheses; an accepted definition is not a proof (its type is
  not a proposition), and nothing accepted is a `theorem`, `opaque` or `axiom`.

Assembly (docs/ASSEMBLY.md; a fourth argument, the assembly's proof manifest): the report is an
assembly report over the same export. Rows are kept apart by category:

* *validated* rows (`assembly = VALIDATED`) are the statement library itself: axiom-free, as above;
* *assembled* rows (`ASSEMBLED`) are accepted `Rocq.*` declarations: they may reference the final
  theorems of proof tasks (never a pending artifact or a template), and their transitive axioms must
  lie within the manifest's allowance — they are *reported* per target, not required to be empty (an
  assembled proof field brings the axioms of its proof);
* *final theorems* (`proof_target`, detector `proofs`) are theorems whose type is exactly the accepted
  statement at its universe parameters and whose value is the manifest's template for that task applied
  to its prerequisites' final theorems; the template's own dependencies (including the pending
  statements it is stated over) are an implementation dependency of the proof term only;
* *carried-over* rows (`PENDING`, `OPAQUE_BINDING_PENDING`, `ASSEMBLY_BLOCKED`, …) are the unchanged
  pending artifacts, checked as pending artifacts;
* `assembly` — every row's assembly state agrees with its status;
* `proof_dependent_computation` (reported, not a failure) — in an assembled definition, each
  elimination of a `Prop` inductive into a non-`Prop` sort whose major premise mentions a final theorem:
  computation that inspects a proof (its reduction may depend on how the proof was written).

Any failure fails the module (non-zero exit of the consumer process).
-/

namespace Rocq2Lean

open Lean Elab Command Meta

syntax (name := rocqVerify) "#rocq2lean_verify " str str str (str)? : command

/-- Assembly: applications of a recursor of a `Prop` inductive at a non-zero motive level whose major
premise mentions one of `proofs` (computation that inspects an assembled proof). -/
partial def proofDependentElims (env : Environment) (proofs : Std.HashSet Name) (e : Expr) : MetaM (Array String) := do
  let mut out := #[]
  let mentions (x : Expr) : Bool := (x.find? fun y => match y with | .const n _ => proofs.contains n | _ => false).isSome
  let rec go (e : Expr) (acc : Array String) : MetaM (Array String) := do
    match e with
    | .app .. =>
      let f := e.getAppFn
      let args := e.getAppArgs
      let mut acc := acc
      if let .const n ls := f then
        if let some (.recInfo rv) := env.find? n then
          if let some (.inductInfo iv) := env.find? rv.getMajorInduct then
            let isPropInd ← forallTelescopeReducing iv.type fun _ b => pure b.isProp
            let large := match ls with | l :: _ => !(l.normalize == .zero) && rv.levelParams.length > iv.levelParams.length | [] => false
            let mi := rv.getMajorIdx
            if isPropInd && large && mi < args.size && mentions args[mi]! then
              acc := acc.push s!"{n} (major premise mentions an assembled proof)"
      acc ← go f acc
      for a in args do acc ← go a acc
      return acc
    | .lam _ t b _ | .forallE _ t b _ => go b (← go t acc)
    | .letE _ t v b _ => go b (← go v (← go t acc))
    | .mdata _ b | .proj _ _ b => go b acc
    | _ => return acc
  out ← go e out
  return out

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

/-- R3G-F (docs/RESULT_SORT_LEVELS.md), on the imported inductive alone: the parameter `p` of a
result-sort implicit level occurs in no binder domain of the arity (parameters and indices keep their
ranges) but in its final sort, and as a sort in no constructor type (fields keep their ranges; it may
occur in universe arguments of references). -/
partial def resultImplicitOk (arity : Expr) (ctors : List Expr) (p : Name) : Bool :=
  let hasP (e : Expr) := (collectLevelParams {} e).params.contains p
  let asSort (e : Expr) := (e.find? fun x => match x with
    | .sort u => (collectLevelParams {} (.sort u)).params.contains p
    | _ => false).isSome
  let rec arityOk : Expr → Bool
    | .forallE _ d b _ => !hasP d && arityOk b
    | e => hasP e
  arityOk arity && ctors.all (!asSort ·)

/-- R-SPLIT (docs/LEVEL_SPLIT.md), on the imported declaration's type alone: as a *sort*, the
universe parameter `p` of a copy occurs only in the final sort of the domain of binder `pos` (after
`nh` hypothesis binders) — nowhere else in that domain, in no other binder's domain — and otherwise
only in the type's final sort. (Universe arguments of references may carry it: those are the
references' instances, R3-checked by the audit.) -/
partial def splitPositionOk (ty : Expr) (nh pos : Nat) (p : Name) : Bool :=
  let has (e : Expr) := (e.find? fun x => match x with
    | .sort u => (collectLevelParams {} (.sort u)).params.contains p
    | _ => false).isSome
  let rec finalOnly : Expr → Bool
    | .forallE _ d b _ => !has d && finalOnly b
    | .sort _ => true
    | e => !has e
  let rec go (j : Nat) (sawOwn : Bool) : Expr → Bool
    | .forallE _ d b _ =>
      if j == nh + pos then finalOnly d && has d && go (j + 1) true b
      else !has d && go (j + 1) sawOwn b
    | .sort _ => sawOwn
    | e => sawOwn && !has e
  go 0 false ty

@[command_elab rocqVerify] def elabRocqVerify : CommandElab := fun stx => do
  let some conPath := stx[1].isStrLit? | throwError "expected a contract path"
  let some repPath := stx[2].isStrLit? | throwError "expected a report path"
  let some outPath := stx[3].isStrLit? | throwError "expected a result path"
  -- assembly: the proof manifest (docs/ASSEMBLY.md)
  let asmPath? : Option String := (stx[4].getArgs[0]?).bind (·.isStrLit?)
  let asmManifest ← match asmPath? with
    | some p => pure (some (← IO.ofExcept (Json.parse (← IO.FS.readFile p))))
    | none => pure none
  let asm := asmManifest.isSome
  let allowedAx : Array Name := ((asmManifest.bind (·.getObjValAs? (Array String) "allowed_axioms" |>.toOption)).getD #[]).map String.toName
  let manifestProofs : Array Json := (asmManifest.bind (·.getObjValAs? (Array Json) "proofs" |>.toOption)).getD #[]
  let contract ← IO.ofExcept (Json.parse (← IO.FS.readFile conPath))
  let report ← IO.ofExcept (Json.parse (← IO.FS.readFile repPath))
  let results ← IO.ofExcept (report.getObjValAs? (Array Json) "results")
  let reqRoots ← IO.ofExcept (contract.getObjValAs? (Array Json) "roots")
  let required ← IO.ofExcept (contract.getObjValAs? (Array String) "required_closure")
  let exported ← IO.ofExcept (contract.getObjValAs? (Array String) "exported")
  let mut problems : Array (String × String) := #[]
  let mut detectors : Std.HashMap String Nat := {}
  let note (det msg : String) (ps : Array (String × String)) := ps.push (det, msg)
  let stmtMode := getStr contract "mode" == "statement"
  let acceptedSt := ["TRANSLATED_AND_CHECKED", "STATEMENT_KERNEL_CHECKED"]
  let pendingSt := ["PENDING_KERNEL_CHECKED", "STATEMENT_PENDING_KERNEL_CHECKED"]
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
  -- B (docs/TERMINATION.md): rows the translator generated for an exported declaration (its
  -- termination obligation's statement, its unfolding equation), named `<decl>__rocq2lean_termination_<k>`
  -- / `<decl>__rocq2lean_unfold_<k>`, of that kind, statement mode only
  let mut generated : Array String := #[]
  for r in results do
    let p := getStr r "synthesized_from"
    if p.isEmpty then continue
    let s := getStr r "source"
    let k := getStr r "synthetic_kind"
    let suf := if k == "termination" then "__rocq2lean_termination_" else if k == "unfolding_equation" then "__rocq2lean_unfold_" else ""
    let ok := stmtMode && !suf.isEmpty && exported.contains p && (s.drop (p ++ suf).length).all Char.isDigit &&
      s.startsWith (p ++ suf) && s.length > (p ++ suf).length
    if ok then generated := generated.push s
    else problems := note "coverage" s!"{s}: generated row not attached to an exported declaration ({p}, {k})" problems
  let exported := exported ++ generated
  for (s, rs) in rows.toList do
    if rs.size != 1 then problems := note "coverage" s!"{s}: {rs.size} result rows" problems
    unless exported.contains s do problems := note "coverage" s!"{s}: result for a declaration that was not exported" problems
  for s in exported do
    unless rows.contains s do problems := note "coverage" s!"{s}: exported declaration has no result" problems
  let status (s : String) : String := match rows[s]? with
    | some #[r] => getStr r "status"
    | _ => "MISSING"
  unless stmtMode do
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
  if !stmtMode && getStr report "status" != "OK" then
    problems := note "roots" s!"report status is '{getStr report "status"}', not OK" problems
  if stmtMode && !["OK", "OK_OBLIGATIONS_PENDING", "ROOTS_NOT_TRANSLATED"].contains (getStr report "status") then
    problems := note "roots" s!"report status is '{getStr report "status"}'" problems
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
  -- statement mode: targets a pending artifact may also reference (pending artifacts, proof tasks)
  let mut allowedPending : Std.HashSet Name := {}
  let mut accepted : Array (String × Json) := #[]
  for s in (if stmtMode then exported else required) do
    match rows[s]? with
    | some #[r] =>
      let st := getStr r "status"
      if st == "TRANSLATED_AND_CHECKED" || (stmtMode && (acceptedSt ++ pendingSt).contains st) then
        let t := (getStr r "target").toName
        let isPending := pendingSt.contains st
        if isPending then allowedPending := allowedPending.insert t else allowed := allowed.insert t
        if getStr r "target_kind" == "inductive" then
          let ins (a : Std.HashSet Name) (n : Name) := a.insert n
          if isPending then allowedPending := ins allowedPending (t.str "rec") else allowed := ins allowed (t.str "rec")
          for c in (r.getObjValAs? (Array Json) "target_ctors").toOption.getD #[] do
            if isPending then allowedPending := allowedPending.insert (getStr c "name").toName
            else allowed := allowed.insert (getStr c "name").toName
        accepted := accepted.push (s, r)
        -- assembly: a proof task's final theorem is referenced like an accepted constant; an assembled
        -- row's former pending artifact stays in the imported library, referenced by carried-over
        -- pending artifacts only
        if asm then
          if let some pt := (r.getObjValAs? String "proof_target").toOption then allowed := allowed.insert pt.toName
          if let some af := (r.getObjValAs? String "assembled_from").toOption then
            allowedPending := allowedPending.insert af.toName |>.insert (af.toName.str "rec")
            for c in (r.getObjValAs? (Array Json) "target_ctors").toOption.getD #[] do
              allowedPending := allowedPending.insert ((getStr c "name").toName.replacePrefix `Rocq `RocqPending)
      else if st == "BOOTSTRAP_RESOLVED" then
        if let some rule := findBootstrap? s then
          for t in rule.target.types do allowed := allowed.insert t |>.insert (t.str "rec")
          for cs in rule.target.ctors do for c in cs do allowed := allowed.insert c
    | _ => pure ()
  if accepted.isEmpty then problems := note "coverage" "no accepted declaration" problems
  -- M6 construction primitives (docs/TRUST.md): Lean prelude inductive types used only by the
  -- accessibility lowering (Acc, PSigma, Exists, Or, False), the convoy lowering (Eq), the mutual
  -- fixpoint and course-of-values lowerings (PProd, PUnit), rule P (PULift); they are kernel-defined inductives
  -- without axioms (the axiom detector still runs on every target)
  for c in [``Acc, ``Acc.intro, ``Acc.rec, ``PSigma, ``PSigma.mk, ``Exists, ``Exists.intro, ``Exists.rec,
            ``Or, ``Or.inl, ``Or.inr, ``Or.rec, ``False, ``False.rec, ``Eq, ``Eq.refl, ``Eq.rec,
            ``PProd, ``PProd.mk, ``PUnit, ``PUnit.unit,
            -- rule P (docs/PROP_LIFT.md): Lean core's lift of a proposition to a type, with its constructor
            -- and projection (a structure of the prelude, no axiom)
            ``PULift, ``PULift.up, ``PULift.down] do
    allowed := allowed.insert c
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
  let mut axiomsBy : Array (String × Json) := #[]
  let mut pdc : Array Json := #[]
  let proofTargets : Std.HashSet Name := results.foldl (init := {}) fun m r =>
    match (r.getObjValAs? String "proof_target").toOption with | some t => m.insert t.toName | none => m
  for (s, r) in accepted do
    let tgt := getStr r "target"
    let some ci := env.find? tgt.toName
      | problems := note "presence" s!"{tgt} ({s}): not in the imported environment" problems; continue
    let st := getStr r "status"
    let isPending := pendingSt.contains st
    -- statement mode: a proof task's statement is a definition
    let kind := if stmtMode && getStr r "target_kind" == "statement" then "def" else getStr r "target_kind"
    if kindOf ci != kind then problems := note "kind" s!"{tgt}: imported {kindOf ci}, report says {kind}" problems
    if stmtMode then
      let ns := if isPending then `RocqPending else `Rocq
      unless ns.isPrefixOf tgt.toName do
        problems := note "namespaces" s!"{tgt}: {st} target outside {ns}" problems
      -- (A′: a definition row may be an `opaque` constant — opaque data translated with its body —
      -- never a theorem or an axiom, and never a statement)
      if ["theorem", "axiom"].contains (kindOf ci) || (kindOf ci == "opaque" && st.startsWith "STATEMENT_") then
        problems := note "statements" s!"{tgt}: {kindOf ci} in a statement-mode library" problems
      let nh := ((r.getObjValAs? (Array Json) "pending_hypotheses").toOption.getD #[]).size
      if isPending == (nh == 0) then
        problems := note "statements" s!"{tgt}: status {st} with {nh} hypotheses" problems
      if kind == "opaque" then
        let bad ← liftTermElabM <| forallBoundedTelescope ci.type (some nh) fun _ body => isProp body
        if bad then problems := note "statements" s!"{tgt}: opaque constant of a proposition (a proof)" problems
      if kind == "def" then
        let isStmt := st.startsWith "STATEMENT_"
        let bad ← liftTermElabM <| forallBoundedTelescope ci.type (some nh) fun _ body => do
          if isStmt then
            match ← whnf body with
            | .sort l => pure (tgt.endsWith ".statement" && !l.isZero || !(tgt.endsWith ".statement" || tgt.endsWith ".type"))
            | _ => pure true
          else pure (← isProp body)
        if bad then
          problems := note "statements" (if isStmt then s!"{tgt}: a proof task's statement is not `Prop` (or a sort for opaque data)"
            else s!"{tgt}: an accepted definition is a proof") problems
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
      unless allowed.contains c || (isPending && allowedPending.contains c) do
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
    -- assembly: an assembled row's axioms come from the proofs it contains; reported, within the
    -- allowance; the validated library (and every pending artifact) stays axiom-free
    if asm && getStr r "assembly" == "ASSEMBLED" then
      unless axs.isEmpty do axiomsBy := axiomsBy.push (tgt, Json.arr (axs.map (Json.str ·.toString)))
      for a in axs do
        unless allowedAx.contains a do problems := note "axioms" s!"{tgt}: depends on {a}, outside the allowance {allowedAx}" problems
      if let .defnInfo dv := ci then
        unless ← liftTermElabM (isProp ci.type) do
          for x in ← liftTermElabM (proofDependentElims env proofTargets dv.value) do
            pdc := pdc.push (Json.mkObj [("target", tgt), ("elimination", x)])
    else unless axs.isEmpty do problems := note "axioms" s!"{tgt}: depends on axioms {axs}" problems
  -- assembly: final theorems and assembly states
  let mut proofsChecked : Nat := 0
  if asm then
    let byLeaf : Std.HashMap String Json := manifestProofs.foldl (fun m e => m.insert (getStr e "leaf") e) {}
    let ptOf : Std.HashMap String String := results.foldl (init := {}) fun m r =>
      match (r.getObjValAs? String "proof_target").toOption with | some t => m.insert (getStr r "source") t | none => m
    for r in results do
      let s := getStr r "source"
      let st := getStr r "status"
      let a := getStr r "assembly"
      let isAcc := acceptedSt.contains st || st == "BOOTSTRAP_RESOLVED"
      if (a == "VALIDATED" || a == "ASSEMBLED") != isAcc then
        problems := note "assembly" s!"{s}: assembly state {a} with status {st}" problems
      if a == "ASSEMBLED" && ((r.getObjValAs? (Array Json) "pending_hypotheses").toOption.getD #[]).size != 0 then
        problems := note "assembly" s!"{s}: assembled with hypotheses" problems
      let some pt := (r.getObjValAs? String "proof_target").toOption | continue
      proofsChecked := proofsChecked + 1
      let some e := byLeaf[s]? | problems := note "proofs" s!"{s}: final theorem without a manifest proof" problems; continue
      let tmplN := (getStr e "template").toName
      let prereq := (e.getObjValAs? (Array String) "prerequisites").toOption.getD #[]
      match env.find? pt.toName, env.find? tmplN with
      | some (.thmInfo tv), some (.thmInfo _) =>
        let lps := ((r.getObjValAs? (Array String) "level_params").toOption.getD #[]).toList.map String.toName
        let want := mkConst (getStr r "target").toName (lps.map Level.param)
        unless tv.levelParams == lps && tv.type == want && exprJson tv.type == r.getObjValD "proof_type" do
          problems := note "proofs" s!"{pt}: type is not the accepted statement {getStr r "target"}" problems
        unless exprJson tv.value == r.getObjValD "proof_value" do
          problems := note "proofs" s!"{pt}: value differs from the report" problems
        let fn := tv.value.getAppFn
        let args := tv.value.getAppArgs
        unless fn.isConstOf tmplN && args.size == prereq.size &&
            (args.zip prereq).all (fun (x, h) => match x, ptOf[h]? with
              | .const n _, some t => n == t.toName
              | _, _ => false) do
          problems := note "proofs" s!"{pt}: value is not {tmplN} applied to its prerequisites' final theorems" problems
        let axs ← liftCoreM (collectAxioms pt.toName)
        if axs.contains ``sorryAx then problems := note "proofs" s!"{pt}: depends on sorryAx" problems
        for x in axs do
          unless allowedAx.contains x do problems := note "proofs" s!"{pt}: depends on {x}, outside the allowance" problems
        axiomsBy := axiomsBy.push (pt, Json.arr (axs.map (Json.str ·.toString)))
      | _, _ => problems := note "proofs" s!"{pt}: final theorem or template {tmplN} missing or not a theorem" problems
  -- interface (P0): protection binding from the contract (never from the report under audit)
  let mut ifaceChecked : Nat := 0
  match contract.getObjVal? "protection" with
  | .ok prot@(.obj _) =>
    let names := (prot.getObjValAs? (Array String) "protected").toOption.getD #[]
    let pset : Std.HashSet String := names.foldl (·.insert ·) {}
    let repProt := (report.getObjVal? "protection").toOption.getD .null
    if (repProt.getObjValAs? Nat "protected_in_export").toOption != some names.size ||
       (repProt.getObjVal? "manifest_sha256").toOption != (prot.getObjVal? "manifest_sha256").toOption then
      problems := note "interface" "the report's protection binding differs from the contract's" problems
    for r in results do
      let s := getStr r "source"
      if ((r.getObjValAs? Bool "protected").toOption.getD false) != pset.contains s then
        problems := note "interface" s!"{s}: protection flag differs from the contract" problems
    for (s, r) in accepted do
      if pset.contains s then
        ifaceChecked := ifaceChecked + 1
        let sl := (r.getObjValAs? (Array Json) "sort_lowered_levels").toOption.getD #[]
        let pin := ((r.getObjValAs? (Array Json) "r2bp_levels").toOption.getD #[]).filter fun x =>
          (x.getObjValAs? Bool "in_type").toOption == some true
        -- R2B-V (approved rule, docs/UNIVERSE_FAMILY_C.md §4): a definition's result sort lowered to the
        -- sort of its value; checked here in Lean: not a statement, and the imported declaration's result
        -- sort is exactly the sort its value inhabits
        let inherited := (r.getObjValAs? Bool "result_sort_inherited").toOption.getD false
        let mut inhOk := false
        if inherited && pin.isEmpty && !sl.isEmpty && !(getStr r "status").startsWith "STATEMENT_" then
          if let some ci := env.find? (getStr r "target").toName then
            if let some v := ci.value? (allowOpaque := true) then
              inhOk ← liftTermElabM <| forallTelescope ci.type fun xs cod => do
                match ← whnf cod with
                | .sort l =>
                  match ← whnf (← inferType (mkAppN v xs)) with
                  | .sort l' => pure (l.normalize == l'.normalize && l.isNeverZero)
                  | _ => pure false
                | _ => pure false
        unless (sl.isEmpty || inhOk) && pin.isEmpty do
          problems := note "interface" s!"{s}: protected public declaration translated with a specialized statement ({sl.size} R2B-S, {pin.size} R2B-P statement level(s))" problems
  | _ => problems := note "interface" "the contract carries no protection binding" problems
  -- R-SPLIT (detector `levels`): every copy's universe parameter sits at its binder's sort only
  for (s, r) in accepted do
    let ls := (r.getObjValAs? (Array Json) "level_split").toOption.getD #[]
    if ls.isEmpty then continue
    let nh := ((r.getObjValAs? (Array Json) "pending_hypotheses").toOption.getD #[]).size
    match env.find? (getStr r "target").toName with
    | none => problems := note "levels" s!"{s}: split declaration not imported" problems
    | some ci =>
      for x in ls do
        let ps := (x.getObjValAs? (Array Nat) "params").toOption.getD #[]
        let cs := (x.getObjValAs? (Array String) "copies").toOption.getD #[]
        if ps.size != cs.size || ps.size < 2 then
          problems := note "levels" s!"{s}: malformed split {x.compress}" problems
        for k in ps, c in cs do
          let p := levelParamName c
          unless ci.levelParams.contains p && splitPositionOk ci.type nh k p do
            problems := note "levels" s!"{s}: split level {c} is not exactly the sort of parameter binder {k}" problems
  -- R3G-F (detector `levels`): result-sort implicit levels change no quantification range
  for (s, r) in accepted do
    let rsi := (r.getObjValAs? (Array String) "result_sort_implicit_levels").toOption.getD #[]
    if rsi.isEmpty then continue
    match env.find? (getStr r "target").toName with
    | some (.inductInfo iv) =>
      let ctys := iv.ctors.filterMap fun c => (env.find? c).map (·.type)
      for l in rsi do
        let p := levelParamName l
        unless iv.levelParams.contains p && resultImplicitOk iv.type ctys p do
          problems := note "levels" s!"{s}: result-sort implicit level {l} is not confined to the block's result sort and to universe arguments" problems
    | _ => problems := note "levels" s!"{s}: result-sort implicit levels on a declaration that is not an imported inductive" problems
  -- R-CARRIER P2 (detector `levels`): each copy of an implicit level is a universe parameter of the
  -- imported declaration that occurs in its type (a statement row: in its statement, the value)
  for (s, r) in accepted do
    let lc := (r.getObjValAs? (Array Json) "level_copies").toOption.getD #[]
    if lc.isEmpty then continue
    match env.find? (getStr r "target").toName with
    | none => problems := note "levels" s!"{s}: declaration with level copies not imported" problems
    | some ci =>
      let stmtRow := (getStr r "status").startsWith "STATEMENT_"
      let where_ := if stmtRow then (ci.value? (allowOpaque := true)).getD ci.type else ci.type
      let ps := (collectLevelParams {} where_).params
      for x in lc do
        for c in (x.getObjValAs? (Array String) "copies").toOption.getD #[] do
          let p := levelParamName c
          unless ci.levelParams.contains p && ps.contains p do
            problems := note "levels" s!"{s}: level copy {c} is not a universe parameter occurring in the declaration's type" problems
  for (d, _) in problems do detectors := detectors.insert d (detectors.getD d 0 + 1)
  let dets := ["binding", "coverage", "roots", "presence", "kind", "safety", "levels", "type", "value", "ctors",
               "target_deps", "axioms", "rec_indices", "residual_levels", "instance_levels", "interface"].map fun d => (d, Json.str (if detectors.getD d 0 == 0 then "OK" else "FAIL"))
  let dets := if stmtMode then dets ++ ["namespaces", "statements"].map fun d => (d, Json.str (if detectors.getD d 0 == 0 then "OK" else "FAIL")) else dets
  let dets := if asm then dets ++ ["proofs", "assembly"].map fun d => (d, Json.str (if detectors.getD d 0 == 0 then "OK" else "FAIL")) else dets
  let asmFields : List (String × Json) := if asm then [("assembly", Json.bool true), ("proofs_checked", proofsChecked),
    ("axioms_by_target", Json.mkObj axiomsBy.toList), ("proof_dependent_computation", Json.arr pdc)] else []
  let modeField : List (String × Json) := if stmtMode then [("mode", Json.str "statement")] else []
  let fields : List (String × Json) := [
    ("schema", "rocq2lean-consumer/1"), ("status", if problems.isEmpty then "OK" else "AUDIT_REJECTED"),
    ("run_id", getStr contract "run_id"), ("accepted_checked", accepted.size),
    ("recursor_applications_checked", recApps),
    ("residual_levels_checked", residualsChecked),
    ("instance_levels_checked", instChecked),
    ("interface_checked", ifaceChecked),
    ("recursors", Json.arr (recs.toArray.map (recursorJson ·.2))),
    ("detectors", Json.mkObj dets),
    ("problems", Json.arr (problems.map fun (d, m) => Json.mkObj [("detector", d), ("message", m)]))]
  let res := Json.mkObj (modeField ++ fields ++ asmFields)
  IO.FS.writeFile outPath (res.pretty ++ "\n")
  unless problems.isEmpty do
    throwError "AUDIT_REJECTED (consumer):\n{String.intercalate "\n" (problems.map fun (d, m) => s!"[{d}] {m}").toList}"
  logInfo m!"rocq2lean verify: {accepted.size} accepted declaration(s) of the required closure match; no axioms"

end Rocq2Lean

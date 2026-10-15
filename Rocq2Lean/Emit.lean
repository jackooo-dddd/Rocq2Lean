import Lean
import Rocq2Lean.IR
import Rocq2Lean.Kernel
import Rocq2Lean.Translate
import Rocq2Lean.Split
import Rocq2Lean.Bootstrap

/-!
# Declaration emission

Processes the exported declarations in dependency order. Each one ends in exactly one status:

* `BOOTSTRAP_RESOLVED` — realised by a verified bootstrap rule;
* `TRANSLATED_AND_CHECKED` — translated and accepted by the Lean kernel (`addChecked`);
* `BLOCKED_SOURCE_BODY` — opaque body unavailable, or a genuine source assumption;
* `BLOCKED_DEPENDENCY` — a dependency did not succeed (the dependency path is recorded);
* `UNSUPPORTED_FEATURE`, `TRANSLATION_FAILED`, `EXPORT_VALIDATION_FAILED`, `KERNEL_REJECTED`,
  `AUDIT_REJECTED` — see `docs/SUPPORT_PROFILE.md`.

Nothing is ever added as an axiom, and a failed declaration is never replaced.
-/

namespace Rocq2Lean

open Lean Meta

structure DeclResult where
  source : String
  kind : String
  status : String
  rule : String := ""
  target : Option Name := none
  targetKind : String := ""
  message : String := ""
  path : List String := []
  blockedBy : Array String := #[]
  /-- Accepted target type and value, for the independent structural audit. -/
  targetType : Option Expr := none
  targetValue : Option Expr := none
  /-- Accepted constructor names and types (generated inductives). -/
  targetCtors : Array (Name × Expr) := #[]
  /-- Universe parameters (generalized source global levels). -/
  levelParams : List Name := []
  /-- Number of parameters (generated inductives). -/
  numParams : Nat := 0
  /-- Universe solving: diagnostics, number of defaulted levels, references checked (rule R3). -/
  levelDiagnostics : Array String := #[]
  levelDefaults : Nat := 0
  universeChecks : Nat := 0
  /-- Defaulted (residual) universe levels: the fresh parameters standing for them and the
  declaration's type/value with those parameters, which the kernel accepted (justification). -/
  residualParams : List Name := []
  residualDefaults : List Level := []
  /-- Generated inductives with level parameters: whether the source is template polymorphic, and
  for each template level the parameter (regular order) whose sort binds it (R5). -/
  isTemplate : Bool := false
  /-- Own source levels solved rather than generalized, with their solutions (R2S/R2B). -/
  bodyLevels : Array (String × Level) := #[]
  /-- Source levels of the universe parameters, in parameter order (R3 at references). -/
  paramLevels : Array String := #[]
  primitiveRecord : Bool := false
  /-- Inductive declarations: reference levels left unconstrained by typing, set to their least
  R3-admissible value 0 (R3″; every universe argument is R3-checked). -/
  minimalLevels : Nat := 0
  templateParams : Array (String × Nat) := #[]
  residualType : Option Expr := none
  residualValue : Option Expr := none
  /-- R6: number of universe variables of a universe-polymorphic source constant; they are the
  first universe parameters, `v_0 … v_{k-1}`. -/
  polyParams : Nat := 0
  /-- R2⁺: accepted on the retry with fact-reduced source universes. -/
  factReduced : Bool := false
  /-- R3G: source levels of referenced declarations that occur in the type only implicitly (through
  the reference) and that typing leaves free: universe parameters `u_l`, like explicit type levels. -/
  implicitLevels : Array String := #[]
  /-- R2F-c: own (explicit type and implicit) levels read through the fact interpretation
  `ι l = max (u_l, ι m + k …)` over the native facts among them (as R2F for inductives). -/
  levelInterp : Array (String × Level) := #[]
  /-- R8: motive levels translated as sort levels (`Type@{l} ↦ Sort u_l`, admitting Prop). -/
  admittingLevels : Array String := #[]
  /-- Accepted in the cumulativity tier (R3↑ lifting, R2B-P Prop offset), after the strict rules
  rejected the declaration. -/
  cumulativity : Bool := false
  /-- R2B-P: proof-local levels whose native `Set < m` was checked as `Set ≤ m`, with their solutions;
  each must be a valid Rocq instance of the source declaration (verify: Rocq kernel re-check). -/
  r2bpLevels : Array (String × Level) := #[]
  /-- R2B-P levels that occur in the declaration's type (a specialization of the source statement). -/
  r2bpInType : Array String := #[]
  /-- R2B-S: levels of the declaration's own result sort solved with `Set < l` read as `Set ≤ l`
  (a type definition at the level of its value), with their solutions. -/
  sortLevels : Array (String × Level) := #[]
  /-- R2B-V: the result sort is the sort of the value (its lowered levels are `sortLevels`). -/
  resultSortInherited : Bool := false
  /-- R-SPLIT (docs/LEVEL_SPLIT.md): source levels translated through the split view — each level, the
  parameter binders (positions) whose sorts it was, and their copies (one universe parameter each). -/
  levelSplit : Array (String × Array Nat × Array String) := #[]
  /-- R3G-F (docs/RESULT_SORT_LEVELS.md): implicit levels of an inductive block taken from references in
  its constructor fields at a level that is result-sort-only in the referenced declaration. -/
  resultSortImplicit : Array String := #[]
  /-- R-CARRIER P2 (docs/CARRIER_LEVELS.md): implicit levels named per free class — each source level
  and its copies (universe parameters `u_<l>__c<k>`, each standing for an argument `a ≤ l`). -/
  levelCopies : Array (String × Array String) := #[]
  /-- M6: constants δ-inlined in the body (`Set`-motive constants used at a `Prop` family). -/
  deltaInlined : Array String := #[]
  /-- R3↓: accepted with references instantiated below shared levels (cumulativity tier). -/
  universeLowered : Bool := false
  /-- Statement mode, pending validation: the leaf key of each hypothesis binder of the pending
  artifact (`RocqPending.*`), in order. -/
  pendingHyps : Array String := #[]
  /-- P0: the declaration belongs to the protected public interface bound in the contract. -/
  protectedIface : Bool := false
  /-- M6: a non-template inductive with plain universe parameters (`u_l` for each level, no R2F
  fact interpretation; tried first, the more general translation). -/
  plainLevels : Bool := false
  /-- Coherence by unification for blocks (docs/COHERENCE_READINGS.md §6): plain parameters, with the
  arity's final sort read through the R2F interpretation. -/
  sortInterp : Bool := false
  /-- Rule P: the number of binders under which the value is lifted by `PULift` (none: no lift). -/
  propLift : Option Nat := none
  /-- Rule P, term level: the number of `PULift.up`/`PULift.down` coercions inserted. -/
  propLiftCoercions : Nat := 0
  /-- Rule P, statements: the head-δ chain δβ-inlined to state a lifted codomain as its proposition. -/
  propLiftUnfold : Array String := #[]
  /-- Rule T (docs/COINDUCTIVE.md): a non-recursive coinductive block translated as an inductive. -/
  coinductiveAsInductive : Bool := false
  /-- Rule Q-a: the levels that occurred only as sort arguments of phantom checks (lowered per occurrence). -/
  phantomLowered : Array String := #[]
  /-- Timing (entry 14): the declaration's translation time and its attempts (tier, ms, status). -/
  timeMs : Nat := 0
  tierTimes : Array (String × Nat × String) := #[]
  /-- R3G for fields (discovery pass only): implicit levels found only in constructor fields. -/
  fieldImplicit : Array String := #[]
  /-- Assembly (docs/ASSEMBLY.md): the row's assembly state (empty outside assembly), a note, the
  pending artifact an assembled row replaces, and — for a proof task whose verified proof template
  was instantiated — the final theorem `Rocq.<leaf>` with its template, type and value. -/
  assembly : String := ""
  assemblyNote : String := ""
  assembledFrom : Option Name := none
  proofTarget : Option Name := none
  proofTemplate : Option Name := none
  proofType : Option Expr := none
  proofValue : Option Expr := none
  /-- Assembly: a row carried over unchanged from the validated report (its JSON). -/
  verbatim : Option Json := none
  /-- Assembly, proof tasks: `PROOF_ASSEMBLED`, `PROOF_NOT_SUPPLIED`, `ASSEMBLY_TRANSPORT_REQUIRED`,
  `OPAQUE_BINDING_PENDING` or `PROOF_VERIFIED_STATEMENT_PENDING`. -/
  proofState : String := ""
  /-- B (docs/TERMINATION.md): a row the translator generated for a declaration (its termination
  obligation's statement, its unfolding equation): the source declaration and the kind. -/
  synthesizedFrom : String := ""
  syntheticKind : String := ""
  /-- Rows generated together with this one (emitted before it). -/
  synthetic : Array DeclResult := #[]
  deriving Inhabited

def DeclResult.ok (r : DeclResult) : Bool :=
  r.status == "TRANSLATED_AND_CHECKED" || r.status == "BOOTSTRAP_RESOLVED"

/-- Assembly: a proof task whose final theorem `Rocq.<leaf>` was assembled is available to its
dependents like an accepted declaration. -/
def DeclResult.available (r : DeclResult) : Bool := r.ok || r.proofTarget.isSome

/-- An attempt that added its declaration: translated, or (statement mode) kernel-checked as a pending
validation artifact; the retry ladders stop there. -/
def DeclResult.accepted (r : DeclResult) : Bool := r.ok || r.status == "PENDING_KERNEL_CHECKED"

/-- Source checking flags that the pilot accepts: everything checked, no impredicative Set, no UIP. -/
def relaxedFlags (native : Json) : Array String := Id.run do
  let flags := (native.getObjVal? "typing_flags").toOption.getD .null
  let get (k : String) : Option Bool := (flags.getObjValAs? Bool k).toOption
  let mut bad := #[]
  for k in ["check_guarded", "check_positive", "check_universes", "check_eliminations"] do
    if get k != some true then bad := bad.push k
  for k in ["impredicative_set", "allow_uip"] do
    if get k != some false then bad := bad.push k
  return bad

private def fromTransError (base : DeclResult) (e : TransError) : DeclResult :=
  { base with status := e.status, message := e.msg, path := e.path.reverse }

/-- Statement mode: a declaration that exists only as a statement (its proof is a task for the Lean
proving agent) or that needs such a proof. It is not available as a Lean term yet; whatever needs it
is pending, not failed. -/
def pendingStatus (s : String) : Bool :=
  s == "STATEMENT_KERNEL_CHECKED" || s == "STATEMENT_PENDING_KERNEL_CHECKED" || s == "PENDING_KERNEL_CHECKED" ||
  s == "OBLIGATIONS_PENDING"

/-- Dependencies that are missing, failed, or pending on proofs (statement mode). -/
private def blockedDeps (results : Std.HashMap String DeclResult) (deps : Array String) :
    Array String × Array String × Array String :=
  deps.foldl (init := (#[], #[], #[])) fun (missing, failed, pending) d =>
    match results[d]? with
    | none => (missing.push d, failed, pending)
    | some r => if r.available then (missing, failed, pending)
      else if pendingStatus r.status then (missing, failed, pending.push d) else (missing, failed.push d, pending)

/-- Global levels of an inductive block (single body): arity and constructor types, sorted. -/
def globalsOfInd (i : IR.InductiveDecl) : Array String :=
  (i.bodies.foldl (fun acc (b : IR.OneInd) => b.ctors.foldl (fun acc c => globalsOf c.type acc) (globalsOf b.type acc)) {}).toArray.qsort (· < ·)

/-- Global levels of a constant that are generalized: those of its type (sorted); proof-local
levels of the body are solved instead (R2B). -/
def globalsOf' (c : IR.ConstantDecl) : Array String :=
  (globalsOf c.type).toArray

/-- The target declaration of a constant, by target kind. -/
def mkConstDecl (name : Name) (kind : String) (lps : List Name) (ty val : Expr) : MetaM Declaration := do
  match kind with
  | "def" =>
    let h := ReducibilityHints.regular (getMaxHeight (← getEnv) val + 1)
    return .defnDecl { name, levelParams := lps, type := ty, value := val, hints := h, safety := .safe, all := [name] }
  | "theorem" => return .thmDecl { name, levelParams := lps, type := ty, value := val, all := [name] }
  | _ => return .opaqueDecl { name, levelParams := lps, type := ty, value := val, isUnsafe := false, all := [name] }

/-- Insert a declaration through the kernel (`addChecked`). Assembly (`reuse`, docs/ASSEMBLY.md):
the validated statement library is imported, so a declaration whose names it already contains is
not added again — it must be *identical* to the imported one (same kind, universe parameters, type,
value / constructors), which the kernel checked when the library was built; anything else is
rejected. A declaration with new names is kernel-checked as usual. -/
def addOrReuse (reuse : Bool) (decl : Declaration) : CoreM KernelResult := do
  unless reuse do return ← addChecked decl
  let env ← getEnv
  let differs (n : Name) : KernelResult := .rejected s!"{n} differs from the declaration of the validated library"
  let same (a b : Expr) : Bool := a == b
  match decl with
  | .defnDecl v =>
    match env.find? v.name with
    | none => addChecked decl
    | some (.defnInfo w) => return if w.levelParams == v.levelParams && same w.type v.type && same w.value v.value then .accepted else differs v.name
    | some _ => return differs v.name
  | .thmDecl v =>
    match env.find? v.name with
    | none => addChecked decl
    | some (.thmInfo w) => return if w.levelParams == v.levelParams && same w.type v.type && same w.value v.value then .accepted else differs v.name
    | some _ => return differs v.name
  | .opaqueDecl v =>
    match env.find? v.name with
    | none => addChecked decl
    | some (.opaqueInfo w) => return if w.levelParams == v.levelParams && same w.type v.type && same w.value v.value then .accepted else differs v.name
    | some _ => return differs v.name
  | .inductDecl lps np types _ =>
    let present := types.filter fun t => env.contains t.name
    if present.isEmpty then return ← addChecked decl
    unless present.length == types.length do return .rejected "an inductive block is only partly present in the validated library"
    for t in types do
      match env.find? t.name with
      | some (.inductInfo w) =>
        unless w.levelParams == lps && w.numParams == np && same w.type t.type && w.ctors == t.ctors.map (·.name) do
          return differs t.name
        for c in t.ctors do
          match env.find? c.name with
          | some (.ctorInfo cv) => unless same cv.type c.type do return differs c.name
          | _ => return differs c.name
      | _ => return differs t.name
    return .accepted
  | _ => addChecked decl

/-- Justification of defaulted universe levels (docs/UNIVERSE_TRANSLATION.md, R3'): the declaration
with each residual level as a fresh universe parameter must be accepted by the kernel, i.e. it is
well typed for *every* value of those levels, so the default `0` chooses nothing. (Assembly: the
target name exists in the imported library, so the check uses an auxiliary name.) -/
def justifyResiduals (name : Name) (kind : String) (lps resid : List Name) (gty gval : Expr) (reuse : Bool := false) :
    MetaM (Option String) := do
  if resid.isEmpty then return none
  let name := if reuse then name ++ `_rocq2lean_residual_check else name
  match ← checkOnly (← mkConstDecl name kind (lps ++ resid) gty gval) with
  | .accepted => return none
  | .rejected msg => return some s!"defaulted universe level(s) {resid} not justified: the declaration is not valid for every value ({msg})"

/-- B: a translator-generated termination-obligation leaf (`transFixWf`). -/
def isTerminationLeaf (l : String) : Bool := (l.splitOn "__rocq2lean_termination_").length == 2

/-- The type of the `j`-th leading binder of `e` (a ∀ or λ telescope). -/
def binderTypeAt? : Expr → Nat → Option Expr
  | .forallE _ t _ _, 0 | .lam _ t _ _, 0 => some t
  | .forallE _ _ b _, j + 1 | .lam _ _ b _, j + 1 => binderTypeAt? b j
  | _, _ => none

/-- `e` with the type of its `j`-th leading binder replaced by `t`. -/
def setBinderTypeAt : Expr → Nat → Expr → Expr
  | .forallE n _ b bi, 0, t => .forallE n t b bi
  | .lam n _ b bi, 0, t => .lam n t b bi
  | .forallE n d b bi, j + 1, t => .forallE n d (setBinderTypeAt b j t) bi
  | .lam n d b bi, j + 1, t => .lam n d (setBinderTypeAt b j t) bi
  | e, _, _ => e

/-! ### C: no specialization at a level the source leaves free

Independent copy in `tools/audit.py` (`check_statement_generality`). A universe argument of a
reference `c.{σ…} a₁ … aₙ` for a source level `l` of `c` that is not a level of the declaration is
*free* when the source graph does not force `l ≤ Set` and no applied argument determines it (`c`'s
parameter for `l` occurs in no applied binder's domain; a pending artifact's hypothesis binders do not
count: their levels are the translator's choice). Fixing a free level (`∀ Job : Equality.type.{0,0}`)
makes the declaration range over a smaller universe than the source's. Type arguments fixed by
sibling arguments (`@Eq A a b`) are not inspected. -/

private def binderDomains (t : Expr) (n : Nat) : Array Expr := Id.run do
  let mut out := #[]
  let mut t := t
  while out.size < n do
    match t with
    | .forallE _ d b _ => out := out.push d; t := b
    | _ => break
  return out

/-- Leading hypothesis binders (`h_<leaf>`) of a pending artifact. -/
private def hypBinderCount (n : Name) (t : Expr) : Nat := Id.run do
  unless n.toString.startsWith "RocqPending." do return 0
  let mut k := 0
  let mut t := t
  repeat
    match t with
    | .forallE x _ b _ =>
      if x.toString.startsWith "h_" then k := k + 1; t := b else break
    | _ => break
  return k

private def freeLevelRef (env : Environment) (facts : IR.UniverseFacts) (own : List Name) (n : Name)
    (us : List Level) (nargs : Nat) : Option String := Id.run do
  let some ci := env.find? n | return none
  let lps := ci.levelParams
  if lps.length != us.length then return none
  let doms := (binderDomains ci.type nargs).extract (hypBinderCount n ci.type) nargs
  for (p, σ) in lps.zip us do
    unless p.toString.startsWith "u_" do continue      -- (R6 universe variables, Lean's own constants)
    if own.contains p then continue                     -- (a level of the declaration: R3)
    -- R-CARRIER P2: a declaration that owns a copy of the level (`u_l__c<k>`, one per independent class)
    -- owns the level, as for `own.contains p` above: its arguments are R3/coherence-checked (the referenced
    -- parameter may itself be a copy of the same source level)
    let base (x : Name) : String := (x.toString.splitOn "__c").head!
    if own.any (fun q => q != p && base q == base p && (q.toString.splitOn "__c").length > 1) then continue
    -- (an argument max(q₁, …) of own parameters (or copies) whose source levels are all *equal* to the
    -- referenced level in the source graph (≤ both ways) is that level's reading, not a specialization)
    let srcOf (x : Name) : Option String := facts.levels.find? (fun l => levelParamName l == Name.mkSimple (base x))
    if let some lp := srcOf p then
      if let some (c, ps) := levelNF σ.normalize then
        if c == 0 && !ps.isEmpty && ps.all (fun (q, k) => k == 0 && own.contains q &&
            match srcOf q with
            | some m => entails facts m lp 0 && entails facts lp m 0
            | none => false) then continue
      -- (rule R, general form: an argument over own levels equal to the referenced level at every model
      -- of the source facts, e.g. a referenced definition's R2F reading `max (u_l, u_m, …)` with `m ≤ l`, is
      -- that level, not a specialization)
      let ownSrc : Array String := own.toArray.filterMap fun q =>
        if (q.toString.splitOn "__c").length > 1 then none else facts.levels.find? (levelParamName · == q)
      if (p.toString.splitOn "__c").length == 1 && σ.hasParam && equalAtModels facts (ownSrc.push lp) σ (.param p) then continue
    if !σ.hasParam then
      if let some l := facts.levels.find? (fun l => levelParamName l == p) then
        if entails facts l "Set" 0 then continue
    if doms.any (fun d => (collectLevelParams {} d).params.contains p) then continue
    return some s!"{n}: the level of {p} is free in the source (no applied argument determines it, the source graph does not force it) but its argument is {σ}, not {p}"
  return none

private def siblingFixed (env : Environment) (n : Name) (nargs : Nat) : Array Nat := Id.run do
  let some ci := env.find? n | return #[]
  let doms := binderDomains ci.type nargs
  let mut out := #[]
  for j in [0:doms.size] do
    if doms[j]!.isSort && ((List.range doms.size).any fun k => j < k && doms[k]!.hasLooseBVar (k - j - 1)) then
      out := out.push j
  return out

partial def freeLevelPin (env : Environment) (facts : IR.UniverseFacts) (own : List Name) (e : Expr) : Option String :=
  match e with
  | .app .. =>
    let f := e.getAppFn
    let args := e.getAppArgs
    let r := match f with
      | .const n us => freeLevelRef env facts own n us args.size
      | _ => freeLevelPin env facts own f
    if r.isSome then r else
    let skip := match f with
      | .const n _ => siblingFixed env n args.size
      | _ => #[]
    Id.run do
      for i in [0:args.size] do
        if skip.contains i then continue
        if let some m := freeLevelPin env facts own args[i]! then return some m
      return none
  | .const n us => freeLevelRef env facts own n us 0
  | .forallE _ d b _ | .lam _ d b _ => freeLevelPin env facts own d <|> freeLevelPin env facts own b
  | .letE _ t v b _ => freeLevelPin env facts own t <|> freeLevelPin env facts own v <|> freeLevelPin env facts own b
  | .mdata _ b | .proj _ _ b => freeLevelPin env facts own b
  | _ => none

private def peelBinders (e : Expr) (k : Nat) : Expr :=
  match k, e with
  | k + 1, .forallE _ _ b _ | k + 1, .lam _ _ b _ => peelBinders b k
  | _, e => e

/-- The binder domains of a definition's type (its quantification ranges), after `k` hypotheses. -/
private def typeDomains (t : Expr) : Array Expr := Id.run do
  let mut out := #[]
  let mut t := t
  repeat
    match t with
    | .forallE _ d b _ => out := out.push d; t := b
    | _ => break
  return out

/-- P3: leading hypothesis binders of the same leaf at the same type (after universe solving) are
collapsed into the first; returns the new type, value and the indices of the kept binders. -/
def collapseHyps (ty val : Expr) (names : Array String) : MetaM (Expr × Expr × Array Nat) := do
  let n := names.size
  forallBoundedTelescope ty n fun xs tb => do
    let vb ← instantiateLambda val xs
    let mut keep : Array Nat := #[]
    let mut dupOf : Array (Expr × Expr) := #[]
    for j in [0:xs.size] do
      -- (types compared with every universe level normalized: `max a b` and `max b a` are one type, as for
      -- the audit's copy of this check)
      let normLv (e : Expr) : Expr := e.replaceLevel fun l => some l.normalize
      let tj := normLv ((← instantiateMVars (← inferType xs[j]!)).replaceFVars (dupOf.map (·.1)) (dupOf.map (·.2)))
      let mut canon : Option Nat := none
      for i in keep do
        if canon.isNone && names[i]! == names[j]! then
          if normLv (← instantiateMVars (← inferType xs[i]!)) == tj then canon := some i
      match canon with
      | some i => dupOf := dupOf.push (xs[j]!, xs[i]!)
      | none => keep := keep.push j
    if keep.size == xs.size then return (ty, val, keep)
    let rec go (k : Nat) (vars : Array Expr) (sub : Array (Expr × Expr)) : MetaM (Expr × Expr) := do
      let tr (e : Expr) : Expr := (e.replaceFVars (dupOf.map (·.1)) (dupOf.map (·.2))).replaceFVars (sub.map (·.1)) (sub.map (·.2))
      if h : k < keep.size then
        let x := xs[keep[k]]!
        let t := tr (← instantiateMVars (← inferType x))
        withLocalDeclD (← x.fvarId!.getUserName) t fun y => go (k + 1) (vars.push y) (sub.push (x, y))
      else
        return (← mkForallFVars vars (tr tb), ← mkLambdaFVars vars (tr vb))
    termination_by keep.size - k
    let (t', v') ← go 0 #[] #[]
    return (t', v', keep)

/-! ### Binder-level independence (statements; independent copy in tools/audit.py)

The quantification ranges of a statement are the sorts of its binders. The translation must keep the
binder levels as independent as the source keeps them: if, for every value of the universe
parameters, the translated level of binder level `b₁` is at most that of `b₂` (for instance the two
are identified by unification through a reference whose parameters share one level), the source must
entail `b₁ ≤ b₂`; a binder level translated to a closed level must be forced `≤ Set` by the source.
Otherwise the statement ranges over fewer types than the source (narrowing). -/

/-- The levels occurring in the binder domains of the ∀-telescope of a source statement. -/
partial def binderLevelsIR : IR.Term → Array String
  | .prod _ a b => ((globalsOf a).toArray ++ binderLevelsIR b).toList.eraseDups.toArray
  | _ => #[]

/-! ### Jointly occurring level metavariables (P2, ITERATION_LOG entry 7)

After unification, a few level metavariables may occur only together, as the summands (with equal
offsets) of one `max` in every level expression of the declaration (Lean's unifier cannot invert
`max`, so a reference's level class is left as `max ?a ?b`). The declaration then depends only on
their maximum: identifying them loses no generality (every value of the maximum is reached with
`?a = ?b`), and the class becomes one metavariable that R3G names after its source level. Nothing
else is identified; the reference-generality and binder-independence checks validate the result. -/

partial def collectLevelsOf (e : Expr) (acc : Array Level) : Array Level :=
  match e with
  | .sort l => acc.push l
  | .const _ ls => acc ++ ls.toArray
  | .app f a => collectLevelsOf a (collectLevelsOf f acc)
  | .lam _ t b _ | .forallE _ t b _ => collectLevelsOf b (collectLevelsOf t acc)
  | .letE _ t v b _ => collectLevelsOf b (collectLevelsOf v (collectLevelsOf t acc))
  | .mdata _ b | .proj _ _ b => collectLevelsOf b acc
  | _ => acc

/-- The metavariable summands `?m + k` of a level, and whether it contains `imax` (then none of its
metavariables is identified). -/
partial def mvarSummands : Level → Array (LMVarId × Nat) × Bool
  | .mvar m => (#[(m, 0)], false)
  | .succ l => let (a, b) := mvarSummands l; (a.map fun (m, k) => (m, k + 1), b)
  | .max a b => let (x, f) := mvarSummands a; let (y, g) := mvarSummands b; (x ++ y, f || g)
  | .imax a b => let (x, _) := mvarSummands a; let (y, _) := mvarSummands b; (x ++ y, true)
  | _ => (#[], false)

/-- `l` instantiated; a `max` of one metavariable with itself (after identification) is that
metavariable. -/
def instCollapse (l : Level) : MetaM Level := do
  let v ← instantiateLevelMVars l
  let n := v.normalize
  return if n.isMVar then n else v

/-- Identify the metavariables of every jointly occurring group; returns the groups identified. -/
def identifyJointMVars (es : Array Expr) : MetaM (Array (Array LMVarId)) := do
  let mut groups : Array (Array (LMVarId × Nat) × Bool) := #[]
  for e in es do
    for l in collectLevelsOf (← instantiateMVars e) #[] do
      let (g, im) := mvarSummands (← instantiateLevelMVars l)
      unless g.isEmpty do groups := groups.push (g, im)
  let setOf (g : Array (LMVarId × Nat)) : Array LMVarId := (g.map (·.1)).toList.eraseDups.toArray
  let mut done : Array LMVarId := #[]
  let mut out := #[]
  for (g, im) in groups do
    let S := setOf g
    if im || S.size < 2 || S.any done.contains then continue
    -- every expression mentioning a member mentions exactly S, each member with one common offset
    let ok := groups.all fun (g', im') =>
      let S' := setOf g'
      !(S'.any S.contains) || (!im' && S'.size == S.size && S'.all S.contains &&
        (g'.map (·.2)).toList.eraseDups.length == 1)
    if ok then
      for m in S[1:] do assignLevelMVar m (.mvar S[0]!)
      done := done ++ S
      out := out.push S
  return out

/-- A normalized level as (constant, summands `p + k`); none outside the fragment (imax, mvars). -/
partial def levelParts : Level → Option (Nat × Array (Name × Nat))
  | .zero => some (0, #[])
  | .succ l => (levelParts l).map fun (c, ps) => (c + 1, ps.map fun (p, k) => (p, k + 1))
  | .param p => some (0, #[(p, 0)])
  | .max a b => do
    let (c1, p1) ← levelParts a
    let (c2, p2) ← levelParts b
    pure (max c1 c2, p1 ++ p2)
  | _ => none

/-- `σ₁ ≤ σ₂` for every value of the parameters. -/
def levelDominated (σ₁ σ₂ : Level) : Bool :=
  match levelParts σ₁.normalize, levelParts σ₂.normalize with
  | some (c1, p1), some (c2, p2) =>
    p1.all (fun (p, k) => p2.any fun (q, k') => q == p && k ≤ k') &&
      (c1 == 0 || c1 ≤ c2 || p2.any fun (_, k') => c1 ≤ k')
  | _, _ => false

def binderIndependence (facts : IR.UniverseFacts) (binders : Array String) (σ : String → Option Level) : Option String := Id.run do
  let tr := binders.filterMap fun b => (σ b).map (b, ·)
  for (b, l) in tr do
    if !l.hasParam && !(entails facts b "Set" 0) then
      return some s!"binder level {b} would be fixed at {l} (the source does not force it to Set)"
  for (b1, l1) in tr do
    for (b2, l2) in tr do
      if b1 != b2 && levelDominated l1 l2 && !(entails facts b1 b2 0) then
        return some s!"binder levels {b1} ≤ {b2} would be forced by the translation ({l1} ≤ {l2}), not by the source"
  return none

private partial def irEndsInSort : IR.Term → Bool
  | .prod _ _ b => irEndsInSort b
  | .sort _ => true
  | _ => false

/-- R2B-V: `σ` (over the parameters `u_g`, `g ∈ globals`) is at most source level `m`: every summand
`g + k` has `g + k ≤ m` and every constant `k` has `Set + k ≤ m` in the native facts. -/
private partial def lowersTo (facts : IR.UniverseFacts) (globals : Array String) (σ : Level) (m : String) : Bool :=
  let rec go (l : Level) (k : Nat) : Bool :=
    match l with
    | .zero => entails facts "Set" m k
    | .succ l => go l (k + 1)
    | .max a b | .imax a b => go a k && go b k
    | .param p => match globals.find? (fun g => levelParamName g == p) with
      | some g => entails facts g m k
      | none => false
    | .mvar _ => false
  go σ.normalize 0

partial def processConstantCore (genv : GEnv) (results : Std.HashMap String DeclResult) (c : IR.ConstantDecl)
    (factReduce : Bool := false) (interp : Bool := false) (admit : Bool := false) (cumul : Bool := false)
    (extraOwn : Array String := #[]) (discover : Bool := false) (lower : Bool := false) (delta : Bool := false)
    (stmt : Bool := false) (inferSort : Bool := false) (wfTerm : Bool := false) (inheritSort : Bool := false)
    (hypExact : Bool := false) (joint : Bool := false) (unify : Bool := false) (propLift : Bool := false)
    (phantom : Bool := false) :
    MetaM DeclResult := do
  let base : DeclResult := { source := c.name, kind := "constant", status := "" }
  let (missing, failed, pending) := blockedDeps results (c.typeDeps ++ c.bodyDeps)
  unless missing.isEmpty do
    return { base with status := "EXPORT_VALIDATION_FAILED",
                       message := s!"dependencies absent from the export: {missing}", blockedBy := missing }
  unless failed.isEmpty do
    return { base with status := "BLOCKED_DEPENDENCY", message := s!"failed dependencies: {failed}",
                       blockedBy := failed }
  -- statement mode, pending validation: a declaration needing unproved prerequisites is translated with
  -- them as hypotheses and kernel-checked as `RocqPending.<name>` (a validation artifact, never part of
  -- the accepted library); a prerequisite that is itself not validated leaves it unvalidated
  let unavailable := pending.filter fun d => !(genv.leafStmt.contains d || genv.pendingDefs.contains d || genv.inds.contains d)
  unless unavailable.isEmpty do
    return { base with status := "OBLIGATIONS_PENDING",
                       message := s!"needs pending declarations not validated: {unavailable}", blockedBy := pending }
  -- (B: a definition whose recursion needs a termination obligation is translated with it as a
  -- hypothesis, `wfTerm`, after the plain attempt asked for one)
  let hypsRef? : Option (IO.Ref (Array (MVarId × String))) ← if pending.isEmpty && !wfTerm then pure none else some <$> IO.mkRef #[]
  let bad := relaxedFlags c.native
  unless bad.isEmpty do
    return { base with status := "AUDIT_REJECTED", message := s!"source declared with relaxed checking: {bad}" }
  -- R6 (docs/UNIVERSE_TRANSLATION.md): the universe variables of a polymorphic constant become its
  -- first Lean universe parameters `v_i`; Rocq's constraints among them are not transported: the
  -- kernel checks the body for *every* value of the parameters (which may reject a body that needs
  -- a constraint, never accepts one that is ill-typed for some instance).
  let polyNames : List Name := match c.universes with
    | .polymorphic names _ => (List.range names.size).map polyParamName
    | _ => []
  let polyLvls : Array Level := (polyNames.map Level.param).toArray
  match c.bodyState, c.body with
  | "assumption", _ =>
    return { base with status := "BLOCKED_SOURCE_BODY",
                       message := "genuine source assumption; the pilot admits no source axioms" }
  | "unavailable", _ =>
    return { base with status := "BLOCKED_SOURCE_BODY", message := "body not available in the export" }
  | "unsupported_primitive", _ =>
    return { base with status := "UNSUPPORTED_FEATURE", message := "primitive or symbol constant" }
  | st, some body =>
    -- M6 (last tier): δ-inline `Set`-motive constants (`Prop ≤ Set` at a family argument)
    let (body, inlined) := if delta then inlineConsts genv.irBodies genv.setMotive body else (body, {})
    if delta && inlined.isEmpty then
      return { base with status := "UNSUPPORTED_FEATURE", message := "no Set-motive constant to inline" }
    let inlinedA := inlined.toArray.qsort (· < ·)
    -- (A′: `opaque_data` — an opaque Set/Type constant whose prepared body was exported — is
    -- translated with its body as a Lean `opaque` constant: never unfolded, as Rocq never unfolds Qed)
    unless st == "transparent" || st == "opaque_present" || st == "sealed_implementation" || st == "opaque_data" do
      return { base with status := "EXPORT_VALIDATION_FAILED", message := s!"unknown body state '{st}'" }
    let name := if hypsRef?.isSome then pendingTargetName c.name else targetName c.name
    if (← getEnv).contains name && !genv.reuseExisting then
      return { base with status := "TRANSLATION_FAILED", message := s!"target name {name} already in use" }
    -- R2S: every own global level (type and body) starts as a level metavariable; references to a
    -- declaration sharing a source level use that variable (coherence by construction). After
    -- Lean's unifier has identified the levels typing forces together, the type levels still free
    -- become universe parameters `u_l`; the others are *solved* (σ l over the parameters), and the
    -- native facts among the declaration's levels must hold for the solution (R2S/R2B obligation).
    -- Body-only levels left free default to their minimal model (R2B, justified by R3′).
    -- R3G: implicit levels found by a discovery pass (`extraOwn`) are own type levels from the start
    -- (a statement definition's levels are those of its value, the statement)
    let explicitTy := (if stmt then globalsOf body (globalsOf c.type) else globalsOf c.type).toArray
    let typeLevels := (explicitTy ++ extraOwn).toList.eraseDups.toArray.qsort (· < ·)
    -- R2B-V (docs/UNIVERSE_FAMILY_C.md §4): the levels of a type-valued definition's result sort (and
    -- only there) are not parameters; the declared result sort is the sort of the translated value
    let resultLv : Array String := if inheritSort then (globalsOf c.type).toArray.filter (onlyInResultSort c.type ·) else #[]
    if inheritSort && (stmt || resultLv.isEmpty || !irEndsInSort c.type) then
      return { base with status := "UNSUPPORTED_FEATURE", message := "R2B-V: not a type-valued definition with result-sort levels" }
    let typeLevels := typeLevels.filter (!resultLv.contains ·)
    -- R8: motive levels of the type (only when requested; see the translation ladder)
    let admitLv := if admit then (motiveLevels c.type).filter explicitTy.contains else #[]
    let own := ((globalsOf body (globalsOf c.type)).toArray ++ extraOwn).toList.eraseDups.toArray.qsort (· < ·)
    let mut gl : Std.HashMap String Level := {}
    let mut ownMVars : Array (String × Level) := #[]
    for m in own do
      let v ← mkFreshLevelMVar
      gl := gl.insert m v
      ownMVars := ownMVars.push (m, v)
    -- coherence by unification (docs/COHERENCE_READINGS.md §6): per-occurrence shared levels
    let sharedRef? : Option (IO.Ref (Array (LMVarId × String))) ← if unify then some <$> IO.mkRef #[] else pure none
    let coerceRef? : Option (IO.Ref Nat) ← if propLift then some <$> IO.mkRef 0 else pure none
    let ty ← match ← runTrans genv (withPath "type" (transClosed c.type)) gl polyLvls factReduce admitLv lower hypsRef? c.name hypExact sharedRef? coerceRef? phantom with
      | .ok e => pure e
      | .error e => return fromTransError base e
    let val ← match ← runTrans genv (withPath "body" (transClosed body)) gl polyLvls factReduce admitLv lower hypsRef? c.name hypExact sharedRef? coerceRef? phantom with
      | .ok e => pure e
      | .error e =>
        if e.msg.startsWith "termination obligation required" && !wfTerm && genv.stmtMode then
          return ← processConstantCore genv results c factReduce interp admit cumul extraOwn discover lower delta stmt inferSort (wfTerm := true) (inheritSort := inheritSort) (hypExact := hypExact) (unify := unify) (propLift := propLift) (phantom := phantom)
        return fromTransError base e
    -- pending validation: the hypotheses become the artifact's leading binders *before* universe
    -- solving, so that the levels of their types (references to prerequisite statements) are
    -- unified, defaulted, recorded and checked (R3) like every other level of the declaration
    let hyps ← match hypsRef? with | some ref => ref.get | none => pure #[]
    let (ty, val) ← if hyps.isEmpty then pure (ty, val) else
      pure (← abstractHyps hyps ty false, ← abstractHyps hyps val true)
    -- rule P (docs/PROP_LIFT.md, approved 2026-10-15): a definition declared at `∀ Γ, Type@{l}`
    -- whose value is a proposition (Rocq's Prop ≤ Type cumulativity) has its value lifted,
    -- `fun Γ => PULift.{u_l+1, 0} P : Type u_l`; reported as the number of non-hypothesis binders.
    -- Term level: the `PULift.up`/`down` inserted during translation (`liftCoerce`), counted.
    -- (the value against the declared type, under the value's own λs: Rocq's conversion of the body with
    -- the type, e.g. `fun b p h => o b p h` declared at `… → Rnat b (pred_N p)` with `o`'s statement the
    -- proposition; `o b p h` becomes `PULift.up (o b p h)`)
    let val ← match coerceRef? with
      | none => pure val
      | some cnt => lambdaTelescope val fun xs b => do
        let some cod ← (try some <$> instantiateForall ty xs catch _ => pure none) | return val
        let n0 ← cnt.get
        let b' ← liftCoerceValue b cod cnt genv.liftTargets
        if (← cnt.get) == n0 then return val
        mkLambdaFVars xs b'
    let coercions ← match coerceRef? with | some r => r.get | none => pure 0
    let (val, propLiftDepth) ← if !propLift then pure (val, none) else do
      let r? ← forallTelescope ty fun xs cod => do
        let cod ← whnf cod
        let .sort sl := cod | return none
        if sl.isZero then return none
        let b := (mkAppN val xs).headBeta
        unless (← whnf (← inferType b)).isProp do return none
        return some (← mkLambdaFVars xs (mkApp (mkConst ``PULift [sl, .zero]) b), xs.size - hyps.size)
      match r? with
      | some (v, k) => pure (v, some k)
      | none =>
        if coercions == 0 then
          return { base with status := "UNSUPPORTED_FEATURE", message := "rule P: no proposition used at a type" }
        pure (val, none)
    -- an opaque-data interface `Rocq.<name>.type := ⟦T⟧` is declared at the sort Lean infers for ⟦T⟧:
    -- Rocq's native sort of T is an upper bound that cumulativity absorbs and Lean cannot; the
    -- interface is T itself, not its sort (the audit checks the type is a sort, the value is T)
    let ty ← if inferSort then instantiateMVars (← inferType val) else pure ty
    -- R2B-V: ∀ Γ, Sort s  ↦  ∀ Γ, (the sort of the value applied to Γ)
    let ty ← if !inheritSort then pure ty else
      try
        forallTelescope ty fun xs cod => do
          unless (← whnf cod).isSort do throwError "the type does not end in a sort"
          -- (checked first: argument typing unifies the levels of the value's references)
          let b := mkAppN val xs
          Meta.check b
          let s ← whnf (← instantiateMVars (← inferType b))
          unless s.isSort do throwError "the value is not a type"
          -- (a lowering of a universe level only: the value must be a type, never a proposition —
          -- Rocq places a Prop-valued body in Type by Prop ≤ Type cumulativity; Prop is not a level)
          unless s.sortLevel!.isNeverZero do throwError "the value is a proposition (Prop ≤ Type cumulativity), not a type"
          mkForallFVars xs s
      catch e => return { base with status := "UNSUPPORTED_FEATURE", message := s!"R2B-V: {← e.toMessageData.toString}" }
    -- after unification: every own level still free that occurs in the (solved) type becomes a
    -- parameter — a type level, or a body level that a type level's solution now mentions
    let implicitRef ← IO.mkRef (#[] : Array String)
    -- R-CARRIER P2: implicit levels named per class (source level, its copies)
    let splitRef ← IO.mkRef (#[] : Array (String × Array String))
    let interpRef ← IO.mkRef (#[] : Array (String × Level))
    let cycleRef ← IO.mkRef (#[] : Array String)
    let keepParams : MetaM Unit := do
      -- R3G discovery pass: report the source levels of free metavariable classes of the *type* at
      -- references (a level below every other level of its class, not own, not template, whose
      -- every argument still contains a free metavariable); nothing is assigned
      if discover then
        -- (C: a statement row's statement is its value: implicit levels are read there)
        let tyI ← instLevelMVars (if stmt then val else ty)
        let valI ← instLevelMVars val
        let argsFor (e : Expr) : MetaM (Array (String × Level)) := do
          let mut out := #[]
          for (n, ls) in constOccurrences e do
            if let some gs := genv.constGlobals[n]? then
              let ls := ls.drop (genv.polyByTarget[n]?.getD 0)
              if gs.size == ls.length then
                for l in gs, σ in ls do out := out.push (l, ← instCollapse σ)
          return out
        let inTy ← argsFor tyI
        let all := inTy ++ (← argsFor valI)
        let mut picks : Array String := #[]
        let mut done : Array Level := #[]
        -- (P0) a template level in the class constrains nothing: Rocq instantiates a template
        -- parameter afresh at each use (R5, as in `checkUniverseObligations`), so no fact `l ≤ l'`
        -- is required for it. Requiring one made the choice depend on unrelated loaded libraries
        -- (a global constraint some other library happened to add), i.e. on the request.
        for (_, σ) in inTy do
          unless σ.isMVar && !done.contains σ do continue
          done := done.push σ
          let cls := (all.filter (·.2 == σ)).map (·.1)
          let tyCls := (inTy.filter (·.2 == σ)).map (·.1)
          let pick := tyCls.toList.eraseDups.find? fun l =>
            !own.contains l && !picks.contains l && !genv.templateLevels.contains l &&
            cls.all (fun l' => genv.templateLevels.contains l' || entails genv.facts l l' 0) && (all.filter (·.1 == l)).all (·.2.hasMVar)
          if let some l := pick then picks := picks.push l
        implicitRef.set picks
        return
      -- (P2: jointly occurring metavariables are one class — in statements, where no level may be
      -- defaulted away; a definition keeps the residual-default path, R3↓ at 0)
      -- (definitions: only on the retry tier `joint`, when the first accepted translation defaulted levels)
      if stmt || joint then
        -- (the hypothesis telescope is not scanned: its instances are the translator's choice, set to
        -- match the uses; the kernel re-checks them)
        discard <| identifyJointMVars #[peelBinders ty hyps.size, peelBinders val hyps.size]
      -- type levels first, so that a class of levels identified by unification is represented by
      -- a type level (its source level is what R3 checks at references)
      unless interp do
        for (m, v) in ownMVars do
          if typeLevels.contains m then
            if let .mvar r ← instantiateLevelMVars v then assignLevelMVar r (.param (levelParamName m))
        -- (C: for a statement row, the levels of the statement are those of its value)
        let tyI0 ← instLevelMVars (if stmt then val else ty)
        let ((), tyMVars) := (levelMVarsOf tyI0).run #[]
        -- statement mode: the source levels of the type's reference arguments (to tell a body level
        -- shared with a referenced declaration from one unification merely identified with an argument)
        let mut tyRefArgs : Array (String × Level) := #[]
        if genv.stmtMode then
          for (n, ls) in constOccurrences tyI0 do
            if let some gs := genv.constGlobals[n]? then
              let ls := ls.drop (genv.polyByTarget[n]?.getD 0)
              if gs.size == ls.length then
                for l in gs, σ in ls do tyRefArgs := tyRefArgs.push (l, ← instCollapse σ)
        for (m, v) in ownMVars do
          if let .mvar r ← instantiateLevelMVars v then
            if tyMVars.contains r then
              if !genv.stmtMode || typeLevels.contains m then
                assignLevelMVar r (.param (levelParamName m))
              -- statement mode, a body level in the type: if it is the argument of a reference for that
              -- very level (a level shared with a referenced monomorphic declaration, e.g. `id` and `ID`),
              -- it is a type level through that reference (reported implicit; the audit checks the
              -- reference); otherwise it is left to the R3G pick below, which names the class after the
              -- referenced level, and this level is solved to it (fact-checked)
              else if tyRefArgs.any (fun (l, σ) => l == m && σ == .mvar r) then
                assignLevelMVar r (.param (levelParamName m))
                implicitRef.modify fun a => if a.contains m then a else a.push m
      -- R3G: a universe argument still free in the *type*, at a reference to a declaration whose
      -- parameter stands for source level `l`, is the source level `l` itself (Rocq references
      -- monomorphic declarations at their own levels): it becomes the parameter `u_l`, so the
      -- declaration stays as general as typing allows instead of being fixed at a default. The
      -- kernel checks the declaration for every value of it.
      -- A free metavariable may stand for several source levels (Lean's unifier identified the
      -- arguments of several references). It is taken as `u_l` for a level `l` that occurs in the
      -- *type* and lies below every other level of its class (`l ≤ l'` entailed by the native
      -- facts), so every other argument of the class satisfies R3's no-raising condition (which
      -- `checkUniverseObligations` re-checks). Own levels and template levels are never chosen.
      -- C (docs/UNIVERSE_TRANSLATION.md, R3G for statements): a statement row's type is `Prop` and its
      -- statement is its value, so the free reference levels of the statement are read in the value; a
      -- statement is never specialized by defaulting such a level to 0
      let tyI ← instLevelMVars (if stmt then val else ty)
      let valI ← instLevelMVars val
      let argsFor (e : Expr) : MetaM (Array (String × Level)) := do
        let mut out := #[]
        for (n, ls) in constOccurrences e do
          if let some gs := genv.constGlobals[n]? then
            let ls := ls.drop (genv.polyByTarget[n]?.getD 0)
            if gs.size == ls.length then
              for l in gs, σ in ls do out := out.push (l, ← instCollapse σ)
        return out
      let inTy ← argsFor tyI
      let all := inTy ++ (← argsFor valI)
      -- (statement mode: a class that contains an own level is represented by that own level)
      -- (R2B-V: the result-sort levels being replaced by the value's sort do not represent a class)
      -- (only own *type* levels represent a class: a proof-local level is solved, fact-checked by R2S, and
      -- never decides the class — R-CARRIER, factory_57's 551 against isSub's motive level 542)
      let ownCur ← (ownMVars.filter fun (m, _) => !resultLv.contains m && (typeLevels.contains m || stmt)).mapM fun (_, v) => instantiateLevelMVars v
      let mut done : Array Level := #[]
      let mut chosen : Array (String × Array LMVarId) := #[]
      -- (R2F-c: classes of the body are candidates too; their levels become own levels)
      for (_, σ) in (if interp then all else inTy) do
        unless σ.isMVar && !done.contains σ do continue
        done := done.push σ
        let cls := (all.filter (·.2 == σ)).map (·.1)
        let tyCls := ((if interp then all else inTy).filter (·.2 == σ)).map (·.1)
        -- every argument for `l` anywhere must still be free: they all become `u_l` (coherence)
        let mut cur : Array (String × Level) := #[]
        for (l', σ') in all do cur := cur.push (l', ← instCollapse σ')
        -- (statement mode: an argument for `l` that unification already fixed to an expression, e.g. a
        -- referenced declaration's R2F reading of its own parameter, is left as is; R3 coherence, the
        -- kernel and the audit check it like every argument)
        -- (R-CARRIER P2: an argument already named after a copy of `l` counts as free for `l`)
        let isCopyOf (l : String) (x : Level) : Bool := match x with
          | .param p => (p.toString.splitOn (toString (levelParamName l) ++ "__c")).length > 1
          | _ => false
        let pick := tyCls.toList.eraseDups.find? fun l =>
          !own.contains l && !genv.templateLevels.contains l && cls.all (fun l' => genv.templateLevels.contains l' || entails genv.facts l l' 0) &&
          (if genv.stmtMode then (cur.filter (·.1 == l)).any (·.2 == σ) && !ownCur.contains σ
           else (cur.filter (·.1 == l)).all (fun (_, x) => x.isMVar || isCopyOf l x))
        if let some l := pick then
          -- R-CARRIER P2 (docs/CARRIER_LEVELS.md): the distinct free classes of arguments for `l` in the
          -- type (operands typing does not relate) are named separately, `l__c<k>`; with one class, `u_l`
          let mut tyClasses : Array Level := #[]
          -- Count operand classes in the source interface, excluding generated prerequisite binders.
          -- Their universe instances are chosen by the translator (as for joint identification),
          -- and must not create extra independent classes beside the declaration's own operands.
          for (l', σ') in ← argsFor (← instLevelMVars (peelBinders (if stmt then val else ty) hyps.size)) do
            if l' == l then
              let x ← instCollapse σ'
              if (x.isMVar || isCopyOf l x) && !tyClasses.contains x then tyClasses := tyClasses.push x
          let split := genv.carrierSplit && !interp && tyClasses.size ≥ 2
          let k := (tyClasses.idxOf? σ).getD 0
          let name := if split then s!"{l}__c{k}" else l
          if split then
            splitRef.modify fun a =>
              let cs := (List.range tyClasses.size).toArray.map (s!"{l}__c{·}")
              if a.any (·.1 == l) then a else a.push (l, cs)
          let mut ms : Array LMVarId := #[]
          for (l', σ') in cur do
            if l' == l then
              if let .mvar r ← instCollapse σ' then
                -- (split: only this class; arguments of other type classes get their own copy, and
                -- classes of the value alone join the first copy below)
                if !split || (.mvar r) == σ then
                  if interp then ms := ms.push r else assignLevelMVar r (.param (levelParamName name))
          if interp then chosen := chosen.push (l, ms)
          implicitRef.modify fun a => if a.contains name then a else a.push name
      -- R-CARRIER P2: free arguments for a split level outside the type's classes (the value's) take
      -- the first copy
      for (l, cs) in ← splitRef.get do
        for (l', σ') in all do
          if l' == l then
            if let .mvar r ← instCollapse σ' then assignLevelMVar r (.param (levelParamName cs[0]!))
      -- R2F-c: the explicit type levels and the chosen implicit levels are the declaration's own
      -- levels, each read as ι l = max (u_l, ι m + k) over the native facts m (+1) ≤ l among them
      -- (`ownLevelInterp`, as for inductives): every own fact holds for every parameter value,
      -- and at u := ρ (any model ρ of the facts) ι is ρ itself.
      if interp then
        -- only type levels still free are interpreted; a level that typing already fixed is a solved
        -- level (R2S) and keeps its R2B fact check
        let mut freeT : Array String := #[]
        -- (coherence by unification: a type level that typing solved through one of its own occurrences,
        -- `?l := max (…, u_l)`, is interpreted too; its solution must be its R2F reading, checked below)
        let mut cycT : Array String := #[]
        for (m, v) in ownMVars do
          if typeLevels.contains m then
            let vi ← instantiateLevelMVars v
            if vi.isMVar then freeT := freeT.push m
            else if unify && (collectLevelParams {} (.sort vi)).params.contains (levelParamName m) then
              freeT := freeT.push m
              cycT := cycT.push m
        let ownI := (freeT ++ chosen.map (·.1)).toList.eraseDups.toArray.qsort (· < ·)
        -- (R3G-F levels are minimal only where they are implicit: not levels of this declaration's source)
        let explicitLv := globalsOf (c.body.getD (.sort .prop)) (globalsOf c.type)
        let ι := ownLevelInterp genv.facts ownI
          ((genv.rsOfDeps (c.typeDeps ++ c.bodyDeps)).fold (fun acc l => if explicitLv.contains l then acc else acc.insert l) {})
          genv.decoupled
        interpRef.set (ownI.map fun l => (l, ι[l]!))
        for (m, v) in ownMVars do
          if ownI.contains m then
            if let .mvar r ← instantiateLevelMVars v then assignLevelMVar r ι[m]!
        for (l, ms) in chosen do
          for r in ms do
            if let .mvar r' ← instantiateLevelMVars (.mvar r) then assignLevelMVar r' ι[l]!
        for (m, v) in ownMVars do
          if cycT.contains m then
            unless (← instantiateLevelMVars v).normalize == ι[m]!.normalize do
              cycleRef.modify (·.push s!"{m} solved as {← instantiateLevelMVars v}, not its R2F reading {ι[m]!}")
    -- default of a still-free proof-local level: its minimal model over the *current* values of the
    -- type levels (parameters or solutions)
    let dflt (id : LMVarId) : MetaM Level := do
      match ownMVars.find? (fun (_, v) => v == .mvar id) with
      | some (m, _) =>
        let mut cur : Std.HashMap String Level := {}
        for (t, v) in ownMVars do
          if typeLevels.contains t then cur := cur.insert t (← instantiateLevelMVars v)
        pure (minimalModelLevel genv.facts cur m)
      | none => pure .zero
    -- coherence by unification: per-occurrence shared levels left free by typing are the own variables
    -- (after the value's type is unified with the declared type, before the parameters are named)
    let rebindThenKeep : MetaM Unit := do
      if let some ref := sharedRef? then rebindShared ref gl genv.facts
      keepParams
    let (ty, val, diags, resid, gty, gval, rdefaults) ← solveLevels ty val dflt rebindThenKeep (solve := lower || joint)
    unless (← cycleRef.get).isEmpty do
      return { base with status := "UNIVERSE_REJECTED", message := s!"coherence by unification: {← cycleRef.get}" }
    -- R-CARRIER P2 post-pass: a remaining `u_l` of a split level (e.g. own-level hypothesis types) is its
    -- first copy; copies that no longer occur in the type (a statement: its value) are merged into one that
    -- does; a level left with one copy is `u_l` again; the remaining copies are renumbered l__c0, l__c1, …
    let mut ren : Std.HashMap Name Name := {}
    let mut finalSplits : Array (String × Array String) := #[]
    let tyHere := if stmt then val else ty
    for (l, cs) in ← splitRef.get do
      let pu := levelParamName l
      let firstC := levelParamName cs[0]!
      let occ0 := (collectLevelParams {} ((tyHere.replaceLevel fun x => match x with
        | .param n => if n == pu then some (.param firstC) else none
        | _ => none))).params
      let occurring := cs.filter fun c => occ0.contains (levelParamName c)
      if occurring.size ≤ 1 then
        for c in cs do ren := ren.insert (levelParamName c) pu
      else
        let keep := occurring.mapIdx fun k _ => s!"{l}__c{k}"
        ren := ren.insert pu (levelParamName keep[0]!)
        for c in cs do
          match occurring.idxOf? c with
          | some k => ren := ren.insert (levelParamName c) (levelParamName keep[k]!)
          | none => ren := ren.insert (levelParamName c) (levelParamName keep[0]!)
        finalSplits := finalSplits.push (l, keep)
    let rn (e : Expr) : Expr := if ren.isEmpty then e else e.replaceLevel fun x => match x with
      | .param n => (ren[n]?).map (.param ·)
      | _ => none
    let (ty, val, gty, gval) := (rn ty, rn val, rn gty, rn gval)
    unless ren.isEmpty do
      -- implicit levels: every renamed copy / level replaced by its final name (source spelling)
      let finals : Array String := finalSplits.foldl (· ++ ·.2) #[]
      let split0 ← splitRef.get
      implicitRef.modify fun a =>
        let a := a.filter fun x => !split0.any (fun (l, cs) => x == l || cs.contains x)
        let collapsed := split0.filter (fun (l, _) => !finalSplits.any (·.1 == l)) |>.map (·.1)
        (a ++ finals ++ collapsed).toList.eraseDups.toArray
    let splits := finalSplits
    let genv := if splits.isEmpty then genv else
      { genv with facts := genv.facts.extend (splits.foldl (· ++ ·.2) #[]) (splits.foldl (fun acc (l, cs) =>
          acc ++ Split.copiedRelations genv.facts #[{ level := l, params := #[], names := cs }]) #[]) }
    let backCopy : String → String := fun x => ((splits.find? (·.2.contains x)).map (·.1)).getD x
    -- P3 retry tier: hypotheses of one leaf that ended at the same type are collapsed into the first
    let (ty, val, hyps) ← if !hypExact || hyps.isEmpty then pure (ty, val, hyps) else do
      unless resid.isEmpty do
        return { base with status := "UNSUPPORTED_FEATURE", message := "P3 tier: residual levels with per-instance hypotheses" }
      let (ty', val', keep) ← collapseHyps ty val (hyps.map (·.2))
      pure (ty', val', keep.map (hyps[·]!))
    if discover then
      return { base with status := "DISCOVERED", implicitLevels := (← implicitRef.get).qsort (· < ·) }
    -- C (docs/UNIVERSE_FAMILY_C.md): every level of a statement is a level of the statement; one left
    -- free after unification and R3G would be fixed by its default, specializing the statement
    -- (narrowing): refused, never defaulted
    -- (P1, ITERATION_LOG entry 7: a statement level left free is defaulted like any residual level,
    -- and the defaulted statement must then pass the binder-independence and generality checks below
    -- — it may not narrow a quantification range; the residual record is kernel-justified as usual)
    let base := { base with levelDiagnostics := diags, levelDefaults := resid.length }
    let mut sol : Std.HashMap String Level := {}
    let mut paramLevels : Array String := #[]
    let levelInterp ← interpRef.get
    -- statement mode: every own level reported as read through ι must actually be ι l (two own levels
    -- that unification identified are not both their own R2F reading: the tier is refused)
    if genv.stmtMode then
      for (m, v) in ownMVars do
        if let some (_, x) := levelInterp.find? (·.1 == m) then
          unless (← instantiateLevelMVars v).normalize == x.normalize do
            return { base with status := "UNIVERSE_REJECTED",
                               message := s!"R2F-c: own level {m} was identified with another own level by unification; it is not its own reading" }
    for (m, v) in ownMVars do
      let s ← instantiateLevelMVars v
      -- (R2B-V: a result-sort level that no longer occurs anywhere — the result sort is the value's —
      -- has no counterpart in the target: recorded at 0, a lowering)
      let s := if resultLv.contains m && s.isMVar then .zero else s
      if levelInterp.any (·.1 == m) then continue        -- R2F-c own level: a parameter, read through ι
      if s == .param (levelParamName m) then paramLevels := paramLevels.push m
      else sol := sol.insert m s.normalize
    let implicitLevels := ((← implicitRef.get) ++ extraOwn.filter (!explicitTy.contains ·)).toList.eraseDups.toArray.qsort (· < ·)
    let globals := (paramLevels ++ implicitLevels ++ levelInterp.map (·.1)).toList.eraseDups.toArray.qsort (· < ·)
    let lparams := polyNames ++ globals.toList.map levelParamName
    -- R3 coherence for R2F-c own levels: an argument for `l` must be ι l
    let solι := levelInterp.foldl (fun (m : Std.HashMap String Level) (l, x) => m.insert l x) sol
    let base := { base with bodyLevels := own.filterMap fun m => sol[m]?.map (m, ·) }
    for m in own do
      if sol.contains m then
        if resultLv.contains m then continue          -- (R2B-V: a lowering, checked below)
        if let .error msg := checkBodyLevel genv.facts globals sol m admitLv cumul then
          return { base with status := "UNIVERSE_REJECTED", message := msg }
    -- levels for which the relaxation was actually needed (the strict check fails): proof-local ones
    -- (R2B-P, source instance checked at verify) and levels of the type's own result sort (R2B-S)
    let mut r2bp : Array (String × Level) := #[]
    let mut sortLv : Array (String × Level) := #[]
    if cumul then
      let tyGlobals := globalsOf c.type
      for m in own do
        if let some σ := sol[m]? then
          if !(checkBodyLevel genv.facts globals sol m admitLv false).toBool then
            -- a level of the type that is not only the result sort: the row is the source statement
            -- specialized at the checked instance (R2B-P with `in_type`; never on a requested root)
            if tyGlobals.contains m && onlyInResultSort c.type m then sortLv := sortLv.push (m, σ)
            else r2bp := r2bp.push (m, σ)
    -- R2B-V: each result-sort level is solved to a level its native facts place below it (a
    -- lowering, never a raising: every summand of σ is entailed ≤ the level)
    if inheritSort then
      for m in resultLv do
        if let some σ := sol[m]? then
          unless lowersTo genv.facts globals σ m do
            return { base with status := "UNIVERSE_REJECTED", message := s!"R2B-V: result-sort level {m} would be raised to {σ}" }
          unless sortLv.any (·.1 == m) do sortLv := sortLv.push (m, σ)
    let inherited := inheritSort && !sortLv.isEmpty && sortLv.all (resultLv.contains ·.1)
    -- R2B-P on a pending artifact: its source instance cannot be re-checked by Rocq (the pending
    -- artifact is the prepared declaration with hypotheses); refused, as the CLI validation requires
    if !r2bp.isEmpty && !hyps.isEmpty then
      return { base with status := "UNIVERSE_REJECTED",
                         message := s!"R2B-P levels {r2bp.map (·.1)} on a pending artifact: the source instance is not checkable" }
    -- P0 interface protection: a protected public declaration keeps its source statement. A
    -- statement specialization (R2B-S lowers the result sort; R2B-P fixes a level of the type) is
    -- refused for it, as root or as dependency; there is no approved representation change.
    -- statement mode: every level of a statement definition is a level of the statement (its value);
    -- no relaxation may specialize it (R2B-P / R2B-S would narrow the theorem statement)
    -- (the declared sort of an opaque-data interface type `Rocq.<name>.type` is not a statement: its
    -- result sort may follow the external definitions' R2B-S lowering, as any non-protected definition)
    if stmt && !(r2bp.isEmpty && (sortLv.isEmpty || c.name.endsWith ".type")) then
      return { base with status := "INTERFACE_REJECTED",
                         message := s!"statement specialization refused (R2B-P levels {r2bp.map (·.1)}, R2B-S levels {sortLv.map (·.1)})" }
    if genv.protectedNames.contains c.name then
      let stmt := (r2bp.map (·.1)).filter (globalsOf c.type).contains
      -- (R2B-V: a result sort taken from the value lowers no quantification range; approved
      -- representation rule, docs/UNIVERSE_FAMILY_C.md §4)
      unless (sortLv.isEmpty || inherited) && stmt.isEmpty do
        return { base with status := "INTERFACE_REJECTED",
                           message := s!"protected public declaration: statement specialization refused (R2B-S result-sort levels {sortLv.map (·.1)}, R2B-P statement levels {stmt})" }
    let nchecks ← match checkUniverseObligations genv globals ty solι admitLv cumul lower,
                         checkUniverseObligations genv globals val solι admitLv cumul lower with
      | .ok a, .ok b => pure (a + b)
      | .error msg, _ | _, .error msg =>
        return { base with status := "UNIVERSE_REJECTED", message := msg }
    let base := { base with universeChecks := nchecks }
    -- C: a statement (anywhere) and a protected definition (its quantification ranges) are never
    -- specialized at a level the source leaves free (refused, as R2B-P/R2B-S are: no narrowing)
    -- binder-level independence of a statement (its quantification ranges)
    if stmt then
      let σ (b : String) : Option Level :=
        match levelInterp.find? (·.1 == b) with
        | some (_, x) => some x
        | none => if paramLevels.contains b then some (.param (levelParamName b)) else sol[b]?
      if let some m := binderIndependence genv.facts (binderLevelsIR body) σ then
        return { base with status := "UNIVERSE_REJECTED", message := s!"statement specialization refused: {m}" }
    let env ← getEnv
    let pinned : Option String :=
      if stmt then
        freeLevelPin env genv.facts lparams (peelBinders ty hyps.size) <|>
          freeLevelPin env genv.facts lparams (peelBinders val hyps.size)
      else if genv.protectedNames.contains c.name then
        (typeDomains (peelBinders ty hyps.size)).findSome? (freeLevelPin env genv.facts lparams)
      else none
    if let some m := pinned then
      return { base with status := "UNIVERSE_REJECTED",
                         message := if stmt then s!"statement specialization refused: {m}"
                                    else s!"protected public declaration: universe specialization refused (a quantification range would be narrowed): {m}" }
    unless (← whnf (← inferType ty)).isSort do
      return { base with status := "TRANSLATION_FAILED", message := "translated type is not a type" }
    -- a sealed-module implementation (e.g. HB.lock) is translated as a transparent definition: its
    -- implementation's unlock lemma is `erefl` and needs the δ-rule (the target gains a definitional
    -- unfolding that the sealed source hides; every source proof still checks)
    let kind ← if c.bodyState == "transparent" || c.bodyState == "sealed_implementation" then pure "def"
      else if ← isProp ty then pure "theorem" else pure "opaque"
    -- B (docs/TERMINATION.md): a termination obligation (a translator-generated leaf) gets its own
    -- statement `Rocq.<leaf>.statement : Prop := ∀ Γ, ∀ s, Acc R s`, kernel-checked; the artifact's
    -- hypothesis binder is typed by that statement (δ-equal), like every other leaf's
    let mut synth : Array DeclResult := #[]
    let mut ty := ty
    let mut val := val
    for j in [0:hyps.size] do
      let leaf := hyps[j]!.2
      -- (only this declaration's own obligations; a dependent's hypothesis is already typed by it)
      unless leaf.startsWith (c.name ++ "__rocq2lean_termination_") do continue
      let some p := binderTypeAt? ty j
        | return { base with status := "TRANSLATION_FAILED", message := "termination hypothesis binder not found" }
      -- B-P (docs/TERMINATION.md): a termination statement that mentions earlier hypotheses (a pending
      -- function in a recursive call's argument, `div.gcdn`'s `modn`) is a pending proof task over the
      -- prerequisites it uses (closed under their own dependencies, in telescope order):
      -- `RocqPending.<leaf>.statement : ∀ hs, Prop := fun hs => ∀ Γ, ∀ s, Acc C R s`, and the binder is it
      -- applied to those hypotheses
      let (sty, sval, deps) ← forallBoundedTelescope ty (some j) fun hs _ => do
        let p' := p.instantiateRev hs
        let mut need : Std.HashSet FVarId := {}
        let mut todo := (collectFVars {} p').fvarIds
        while !todo.isEmpty do
          let v := todo.back!
          todo := todo.pop
          if need.contains v || !hs.any (·.fvarId! == v) then continue
          need := need.insert v
          todo := todo ++ (collectFVars {} (← inferType (mkFVar v))).fvarIds
        let ds := (List.range hs.size).toArray.filter fun k => need.contains hs[k]!.fvarId!
        let dv := ds.map (hs[·]!)
        return (← mkForallFVars dv (mkSort .zero), ← mkLambdaFVars dv p', ds)
      if sty.hasLooseBVars || sval.hasLooseBVars then
        return { base with status := "UNSUPPORTED_FEATURE", message := "termination lowering: the termination statement depends on non-hypothesis binders" }
      let used := (collectLevelParams {} sval).params ++ (collectLevelParams {} sty).params
      if polyNames.any used.contains then
        return { base with status := "UNSUPPORTED_FEATURE", message := "termination lowering: termination statement of a universe-polymorphic definition" }
      let slps := lparams.filter used.contains
      let tpend := !deps.isEmpty
      let sname := if tpend then pendingTargetName (leaf ++ ".statement") else targetName (leaf ++ ".statement")
      match ← addOrReuse (genv.reuseExisting || (← getEnv).contains sname) (← mkConstDecl sname "def" slps sty sval) with
      | .rejected msg => return { base with status := "KERNEL_REJECTED", message := s!"termination statement {leaf}: {msg}" }
      | .accepted => pure ()
      -- (the binder j sees the j earlier binders as bvars j-1 … 0)
      let sc := mkAppN (mkConst sname (slps.map Level.param)) (deps.map fun k => mkBVar (j - 1 - k))
      ty := setBinderTypeAt ty j sc
      val := setBinderTypeAt val j sc
      synth := synth.push { source := leaf, kind := "constant",
                            status := if tpend then "STATEMENT_PENDING_KERNEL_CHECKED" else "STATEMENT_KERNEL_CHECKED",
                            pendingHyps := deps.map (hyps[·]!.2),
                            rule := "termination/statement", target := some sname, targetKind := "statement",
                            targetType := some sty, targetValue := some sval, levelParams := slps,
                            paramLevels := (globals.filter fun g => slps.contains (levelParamName g)).map backCopy,
                            synthesizedFrom := c.name, syntheticKind := "termination" }
    -- (B: a definition translated with a termination hypothesis that assembly resolved to a final
    -- theorem has no hypothesis left: it is the accepted declaration)
    let isPending := hypsRef?.isSome && !(wfTerm && pending.isEmpty && hyps.isEmpty)
    let name := if isPending then name else targetName c.name
    let base := { base with target := some name, targetKind := kind, rule := s!"constant/{c.bodyState}" }
    if let some msg ← justifyResiduals name kind lparams resid gty gval genv.reuseExisting then
      return { base with status := "UNIVERSE_REJECTED", message := msg }
    let base := if resid.isEmpty then base
      else { base with residualParams := resid, residualDefaults := rdefaults, residualType := gty, residualValue := gval }
    match ← addOrReuse genv.reuseExisting (← mkConstDecl name kind lparams ty val) with
    | .accepted =>
      -- B: the unfolding equation of a termination-lowered fixpoint at the top of the body, stated
      -- from the source body (a proof task; with the artifact's hypotheses when pending)
      let ownTerm := c.name ++ "__rocq2lean_termination_"
      let usedWf := hyps.any (·.2.startsWith ownTerm) ||
        (val.find? fun e => match e with | .const n _ => (n.toString.splitOn ownTerm).length == 2 | _ => false).isSome
      if usedWf then
        let leafU := c.name ++ "__rocq2lean_unfold_1"
        let uref ← IO.mkRef (#[] : Array (MVarId × String))
        let selfX : TransM Expr := do
          let e := mkConst name (lparams.map Level.param)
          if hyps.isEmpty then pure e else applyHyps uref e (hyps.map (·.2))
        match ← runTrans genv (withPath "unfolding equation" (do transUnfoldEq body (← selfX))) gl polyLvls factReduce admitLv lower (some uref) c.name with
        | .ok (some eq0) =>
          let uh ← uref.get
          let eqV ← instantiateMVars (← abstractHyps uh eq0 true)
          let uty ← instantiateMVars (← abstractHyps uh (mkSort .zero) false)
          let upend := !uh.isEmpty
          let un := if upend then pendingTargetName (leafU ++ ".statement") else targetName (leafU ++ ".statement")
          if eqV.hasExprMVar || eqV.hasLevelMVar then
            synth := synth.push { source := leafU, kind := "constant", status := "TRANSLATION_FAILED", message := "unfolding equation with unresolved metavariables",
                                  synthesizedFrom := c.name, syntheticKind := "unfolding_equation" }
          else
          match ← addOrReuse (genv.reuseExisting || (← getEnv).contains un) (← mkConstDecl un "def" lparams uty eqV) with
          | .accepted =>
            synth := synth.push { source := leafU, kind := "constant",
                                  status := if upend then "STATEMENT_PENDING_KERNEL_CHECKED" else "STATEMENT_KERNEL_CHECKED",
                                  rule := "termination/unfolding_equation", target := some un, targetKind := "statement",
                                  targetType := some uty, targetValue := some eqV, levelParams := lparams, paramLevels := globals.map backCopy,
                                  pendingHyps := uh.map (·.2), synthesizedFrom := c.name, syntheticKind := "unfolding_equation",
                                  }
          | .rejected msg =>
            synth := synth.push { source := leafU, kind := "constant", status := "KERNEL_REJECTED", message := msg,
                                  synthesizedFrom := c.name, syntheticKind := "unfolding_equation" }
        | .ok none => pure ()
        | .error e =>
          synth := synth.push { source := leafU, kind := "constant", status := e.status, message := s!"unfolding equation: {e.msg}",
                                synthesizedFrom := c.name, syntheticKind := "unfolding_equation" }
      return { base with status := if isPending then "PENDING_KERNEL_CHECKED" else "TRANSLATED_AND_CHECKED",
                                      synthetic := synth,
                                      pendingHyps := hyps.map (·.2), targetType := ty, targetValue := val,
                                      levelParams := lparams, paramLevels := globals.map backCopy, levelCopies := splits, polyParams := polyNames.length,
                                      factReduced := factReduce, implicitLevels, levelInterp, propLift := propLiftDepth, propLiftCoercions := coercions,
                                      admittingLevels := admitLv, cumulativity := cumul, r2bpLevels := r2bp, sortLevels := sortLv, resultSortInherited := inherited,
                                      r2bpInType := (r2bp.map (·.1)).filter (globalsOf c.type).contains,
                                      universeLowered := lower, deltaInlined := inlinedA }
    | .rejected msg => return { base with status := "KERNEL_REJECTED", message := msg }
  | st, _ =>
    return { base with status := "EXPORT_VALIDATION_FAILED", message := s!"body state '{st}' inconsistent with body" }

/-- Template binding of a template inductive (R5), from the Rocq kernel's own record
(`native.template_info`, round-trip checked): each template level is bound by exactly one
parameter whose sort is exactly `Type@{l}`, every global level of the declaration is a template
level, and the quoted parameter types agree. Returns `(level, parameter position)` pairs. -/
def templateBinding (i : IR.InductiveDecl) (globals : Array String) :
    Except (String × String) (Array (String × Nat)) := do
  let ti := i.native.getObjValD "template_info"
  let some defaults := (ti.getObjValAs? (Array String) "defaults").toOption | throw ("EXPORT_VALIDATION_FAILED", "template inductive without template_info")
  let some pargs := (ti.getObjValAs? (Array Json) "param_arguments").toOption | throw ("EXPORT_VALIDATION_FAILED", "template_info without param_arguments")
  -- other (non-template) global levels are allowed: they are solved by unification (R5S)
  let _ := globals
  if i.params.any (·.body.isSome) then throw ("UNSUPPORTED_FEATURE", "template inductive with let-bound parameters")
  unless pargs.size == i.params.size do throw ("EXPORT_VALIDATION_FAILED", "template_info parameter count differs from the quoted parameters")
  let mut out : Array (String × Nat) := #[]
  for pa in pargs, k in [0:pargs.size] do
    if pa.isNull then continue
    let us := (pa.getObjValAs? (Array Json) "u").toOption.getD #[]
    -- `quality_sort`: the parameter also binds a sort quality (Rocq: "can be instantiated to
    -- Prop"); the kernel's template defaults fix the quality to Type, which is the instance
    -- translated here. References instantiating it at Prop are rejected explicitly (R5).
    let kind := (pa.getObjValAs? String "k").toOption
    let ok := (kind == some "type" || kind == some "quality_sort") && us.size == 1 &&
      (us[0]!.getObjValAs? Nat "n").toOption == some 0 && !(us[0]!.getObjValD "bound").isNull
    unless ok do throw ("UNSUPPORTED_FEATURE", s!"template parameter {k} binds a level with an offset or an algebraic universe")
    let l := (us[0]!.getObjValAs? String "l").toOption.getD ""
    -- the quoted parameter (MetaRocq, innermost-first) must be an arity ending in exactly that
    -- sort: `Type@{l}` or `∀ zs, Type@{l}` (e.g. sigT's `P : A → Type@{l}`)
    let rec codomain : IR.Term → IR.Term
      | .prod _ _ b => codomain b
      | t => t
    match codomain i.params[i.params.size - 1 - k]!.type with
    | .sort (.type #[{ level := .global l', offset := 0 }]) =>
      unless l' == l do throw ("EXPORT_VALIDATION_FAILED", s!"template parameter {k}: quoted sort level {l'} differs from the kernel's {l}")
    | _ => throw ("UNSUPPORTED_FEATURE", s!"template parameter {k}: its type is not an arity ending in Type@\{{l}}")
    out := out.push (l, k)
  for d in defaults do
    unless (out.filter (·.1 == d)).size == 1 do throw ("UNSUPPORTED_FEATURE", s!"template level {d} is not bound by exactly one parameter")
  return out

/-- R3G-F: the levels read minimally in a block's R2F interpretation — its own R3G-F levels and those in
its dependency closure, where they are implicit (not levels of this block's source). -/
def rsMinimalFor (genv : GEnv) (i : IR.InductiveDecl) (rsOwn : Array String) : Std.HashSet String :=
  let expl := globalsOfInd i
  let base := (rsOwn.foldl (·.insert ·) (genv.rsOfDeps i.typeDeps)).fold (fun acc l => if expl.contains l then acc else acc.insert l) {}
  base

def processInductiveCore (genv : GEnv) (results : Std.HashMap String DeclResult) (i : IR.InductiveDecl)
    (raw : Json) (extraOwn : Array String := #[]) (discover : Bool := false) (lower : Bool := false)
    (plain : Bool := false) (rsOwn : Array String := #[]) (unify : Bool := false) :
    MetaM (DeclResult × Option IndTarget) := do
  let base : DeclResult := { source := i.name, kind := "inductive", status := "" }
  let (missing, failed, pending) := blockedDeps results (i.typeDeps.filter (· != i.name))
  unless missing.isEmpty && failed.isEmpty do
    return ({ base with status := if missing.isEmpty then "BLOCKED_DEPENDENCY" else "EXPORT_VALIDATION_FAILED",
                        message := s!"dependencies missing {missing} / failed {failed}",
                        blockedBy := missing ++ failed }, none)
  -- statement mode, pending validation (as for constants): the block is translated with its unproved
  -- prerequisites as leading hypothesis parameters, as `RocqPending.<name>`
  let unavailable := pending.filter fun d => !(genv.leafStmt.contains d || genv.pendingDefs.contains d || genv.inds.contains d)
  unless unavailable.isEmpty do
    return ({ base with status := "OBLIGATIONS_PENDING",
                        message := s!"needs pending declarations not validated: {unavailable}", blockedBy := pending }, none)
  let hypsRef? : Option (IO.Ref (Array (MVarId × String))) ← if pending.isEmpty then pure none else some <$> IO.mkRef #[]
  let bad := relaxedFlags i.native
  unless bad.isEmpty do
    return ({ base with status := "AUDIT_REJECTED", message := s!"source declared with relaxed checking: {bad}" }, none)
  match findBootstrap? i.name with
  | some rule =>
    match ← verifyBootstrap rule i raw with
    | .ok () =>
      return ({ base with status := "BOOTSTRAP_RESOLVED", rule := rule.id, target := rule.target.types[0]?,
                          targetKind := "inductive (bootstrap)" }, some rule.target)
    | .error msg => return ({ base with status := "AUDIT_REJECTED", rule := rule.id, message := msg }, none)
  | none => do
    let (r, t) ← generateInductive base i hypsRef?
    pure ({ r with coinductiveAsInductive := i.finite == "CoFinite" }, t)

where
  /-- M3a: emit a fresh Lean inductive for a single-body, monomorphic, non-coinductive block. -/
  generateInductive (base : DeclResult) (i : IR.InductiveDecl) (hypsRef? : Option (IO.Ref (Array (MVarId × String)))) :
      MetaM (DeclResult × Option IndTarget) := do
    let unsupported (msg : String) := ({ base with status := "UNSUPPORTED_FEATURE", message := msg }, none)
    if let .polymorphic .. := i.universes then return unsupported "universe-polymorphic inductive"
    -- rule T (docs/COINDUCTIVE.md, approved 2026-10-15): a non-recursive coinductive block (one body, no
    -- constructor argument or index mentions it) is its least fixed point too; translated as the inductive
    -- (a `cofix` stays refused by the term translation)
    if i.finite == "CoFinite" && !nonRecursiveBlock i then return unsupported "recursive coinductive type"
    unless i.bodies.size == 1 do return unsupported s!"mutual block of {i.bodies.size} inductives"
    let body := i.bodies[0]!
    -- Primitive records (M5): structure-like (one constructor, no indices, non-recursive), so Lean's
    -- kernel projections and structure eta apply; projections are translated to `Expr.proj`.
    let isRecord := !body.projs.isEmpty
    if isRecord then
      unless body.ctors.size == 1 && body.indices.isEmpty && body.projs.size == body.ctors[0]!.args.size do
        return unsupported "primitive record that is not structure-like (one constructor, no indices, one projection per field)"
    if (← getEnv).contains (inductiveNames i.name body.name #[]).1 && !genv.reuseExisting then
      return ({ base with status := "TRANSLATION_FAILED", message := "target name already in use" }, none)
    let (tname, cnames) := inductiveNames i.name body.name (body.ctors.map (·.name))
    let pend (n : Name) : Name := if hypsRef?.isSome then n.replacePrefix `Rocq `RocqPending else n
    let (tname, cnames) := (pend tname, cnames.map pend)
    -- Source global levels of the declaration become universe parameters (R2T); for a template
    -- inductive they must be exactly its template levels, each bound by one parameter sort (R5).
    let isTemplate := (i.native.getObjValAs? Bool "template").toOption == some true
    -- R3G for blocks: implicit levels (discovered in a first pass) are own levels of the block from
    -- the start, interpreted by R2F together with the explicit ones
    -- (R3G for template blocks, entry 14: their implicit levels are ordinary, non-template parameters,
    -- left free by the constructors like the other non-template levels of the block)
    let allGlobals := (globalsOfInd i ++ extraOwn).toList.eraseDups.toArray.qsort (· < ·)
    let templateParams ← if isTemplate then
        match templateBinding i allGlobals with
        | .ok b => pure b
        | .error (st, msg) => return ({ base with status := st, message := msg }, none)
      else pure #[]
    -- Template inductives: the template levels are the parameters (R5); any other global level of
    -- the block (e.g. Corelib mem_pred's conclusion Type@{max(Set, pred.u0)}, where pred is used on
    -- the parameter by cumulativity) is solved by unifying the constructor types (R5S).
    -- Non-template inductives: every global level is a parameter, read through its fact-respecting
    -- interpretation (R2F).
    let globals := if isTemplate then (templateParams.map (·.1)).qsort (· < ·) else allGlobals
    let extra := allGlobals.filter (!globals.contains ·)
    let lparams := globals.toList.map levelParamName
    let plain := plain && !isTemplate
    let mut gl : Std.HashMap String Level :=
      if isTemplate || plain then globals.foldl (fun m n => m.insert n (.param (levelParamName n))) {}
      else ownLevelInterp genv.facts globals (rsMinimalFor genv i rsOwn) genv.decoupled
    let mut extraMVars : Array (String × Level) := #[]
    for m in extra do
      let v ← mkFreshLevelMVar
      gl := gl.insert m v
      extraMVars := extraMVars.push (m, v)
    -- coherence by unification (docs/COHERENCE_READINGS.md §6): per-occurrence shared levels
    let sharedRef? : Option (IO.Ref (Array (LMVarId × String))) ← if unify then some <$> IO.mkRef #[] else pure none
    let ty ← match ← runTrans genv (withPath "arity" (transClosed body.type)) gl (lowerShared := lower) (hyps := hypsRef?) (sharedFresh := sharedRef?) with
      | .ok e => pure e
      | .error e => return (fromTransError base e, none)
    -- (plain parameters per occurrence: the block's own sort is its R2F reading, which equals the source
    -- sort at every model of the facts and bounds the fields' readings, e.g. `Finite.type`'s at 110)
    let sortInterp := plain && unify
    let ty ← if !sortInterp then pure ty else
      match ← runTrans genv (withPath "sort" (transSort body.sort)) (ownLevelInterp genv.facts globals (rsMinimalFor genv i rsOwn) genv.decoupled) with
      | .ok s =>
        let rec repl : Expr → Expr
          | .forallE n d b bi => .forallE n d (repl b) bi
          | .sort _ => s
          | e => e
        pure (repl ty)
      | .error e => return (fromTransError base e, none)
    -- constructor types are translated and type-checked against a local `self` of the arity type
    -- (the block is not declared yet), which is then replaced by the constant at the parameters
    let r : Except TransError (Array Constructor × FVarId) ← withLocalDeclD `self ty fun sv => do
      let mut out : Array Constructor := #[]
      for c in body.ctors, cn in cnames do
        let r ← (withReader (fun ctx => { ctx with locals := #[sv] })
                   (withPath s!"ctor {c.name}" (do return eraseBinderScopes (← instLevelMVars (← trans c.type))))).run { genv, globalLevels := gl, lowerShared := lower, hyps := hypsRef?, sharedFresh := sharedRef? } |>.run
        match r with
        | .ok cty =>
          -- R3″/R5S: unify level metavariables of the block by type-checking the constructor type
          try Meta.check cty catch _ => pure ()
          out := out.push { name := cn, type := cty }
        | .error e => return .error e
      return .ok (out, sv.fvarId!)
    let (rawCtors, selfId) ← match r with
      | .ok cs => pure cs
      | .error e => return (fromTransError base e, none)
    try Meta.check ty catch _ => pure ()
    if let some ref := sharedRef? then rebindShared ref gl genv.facts
    -- a non-template level that unification leaves free is a genuine independent level of the
    -- block: it becomes a (non-template) universe parameter, R3 applies at references (R2T)
    let mut sol : Std.HashMap String Level := {}
    let mut freeExtra : Array String := #[]
    for (m, v) in extraMVars do
      if let .mvar r ← instantiateLevelMVars v then
        assignLevelMVar r (.param (levelParamName m))
        freeExtra := freeExtra.push m
    for (m, v) in extraMVars do
      let s ← instantiateLevelMVars v
      if s.hasMVar then
        return ({ base with status := "UNSUPPORTED_FEATURE",
                            message := s!"level {m} of the template inductive is only partly determined by its constructors" }, none)
      unless freeExtra.contains m do sol := sol.insert m s.normalize
    -- (an implicit level of a template block is a parameter or nothing: one the constructors solve is
    -- refused, and the block is translated without it)
    if let some m := extraOwn.find? (fun m => !(globalsOfInd i).contains m && sol.contains m) then
      return ({ base with status := "UNIVERSE_REJECTED", message := s!"implicit level {m} of the template block is solved by its constructors" }, none)
    let globals := (globals ++ freeExtra).qsort (· < ·)
    let lparams := globals.toList.map levelParamName
    -- pending validation: the hypotheses created so far are the block's leading parameters; the
    -- block refers to itself applied to them
    let hyps ← match hypsRef? with | some ref => ref.get | none => pure #[]
    let self := mkAppN (mkConst tname (lparams.map Level.param)) (hyps.map fun (m, _) => mkMVar m)
    let mut ctors : Array Constructor := #[]
    for c in rawCtors do
      let cty ← instLevelMVars (c.type.replaceFVar (mkFVar selfId) self)
      let onlyHyps ← if hyps.isEmpty then pure false else
        pure ((← getMVars cty).all fun m => hyps.any (·.1 == m))
      if cty.hasFVar || (cty.hasExprMVar && !onlyHyps) then
        return ({ base with status := "TRANSLATION_FAILED", message := s!"constructor {c.name} has escaping free or meta variables" }, none)
      ctors := ctors.push { c with type := cty }
    let ty ← instLevelMVars ty
    for m in extra.filter (!freeExtra.contains ·) do
      if let .error msg := checkBodyLevel genv.facts globals sol m then
        return ({ base with status := "UNIVERSE_REJECTED", message := msg }, none)
    let base := { base with bodyLevels := extra.filterMap fun m => sol[m]?.map (m, ·) }
    -- R3G (inductives), discovery pass: a level metavariable left free at a reference to a
    -- declaration whose parameter stands for source level `l` is `l` itself. The pass reports the
    -- levels so found (same choice and coherence conditions as for constants); the block is then
    -- translated again with them as own levels (`extraOwn`).
    if discover then
      let mut occ : Array (String × Level) := #[]
      for e in #[ty] ++ ctors.map (·.type) do
        for (n, ls) in constOccurrences (← instLevelMVars e) do
          -- (rule H: a prerequisite hypothesis's statement is instantiated where it is used — the
          -- translator's choice, as in R-CARRIER refinement 1 — so its arguments decide no class)
          if genv.leafStmtTargets.contains n then continue
          if let some gs := genv.constGlobals[n]? then
            let ls := ls.drop (genv.polyByTarget[n]?.getD 0)
            if gs.size == ls.length then
              for l in gs, σ in ls do occ := occ.push (l, ← instantiateLevelMVars σ)
      -- candidates: classes occurring in the arity (parameter and index types), where a level can
      -- never make a constructor field too big for the block's sort
      let mut inArity : Array Level := #[]
      for (n, ls) in constOccurrences (← instLevelMVars ty) do
        if let some gs := genv.constGlobals[n]? then
          let ls' := ls.drop (genv.polyByTarget[n]?.getD 0)
          for σ in ls do inArity := inArity.push (← instantiateLevelMVars σ)
          -- (rule R: an arity argument `max (?x, …)` that unification built from a referenced declaration's
          -- R2F reading; its metavariable `?x`, an argument for the same source level elsewhere, is the class)
          if gs.size == ls'.length then
            for l in gs, σ in ls' do
              let σ ← instantiateLevelMVars σ
              unless σ.isMVar do
                for m in (σ.collectMVars {}).toArray do
                  if occ.any (fun (l', x) => l' == l && x == .mvar m) then inArity := inArity.push (.mvar m)
      let mut picks : Array String := #[]
      let mut done : Array Level := #[]
      for (_, σ) in occ.filter (fun (_, σ) => inArity.contains σ) do
        unless σ.isMVar && !done.contains σ do continue
        done := done.push σ
        let cls := (occ.filter (·.2 == σ)).map (·.1)
        let pick := cls.toList.eraseDups.find? fun l =>
          !globals.contains l && !picks.contains l && !genv.templateLevels.contains l &&
          cls.all (fun l' => genv.templateLevels.contains l' || entails genv.facts l l' 0) && (occ.filter (·.1 == l)).all (·.2.hasMVar)
        if let some l := pick then picks := picks.push l
      -- R3G-F (docs/RESULT_SORT_LEVELS.md): a class occurring only in constructor fields, at references
      -- for a level that is result-sort-only in the referenced declaration and that the native facts
      -- bound by a level of this block's result sort (so in Rocq the field fits the block's sort): that
      -- level, rather than R3″'s 0
      let resLv : Array String := if i.bodies.size == 1 then
          match i.bodies[0]!.sort with
          | .type u => u.filterMap fun e => match e.level with | .global n => some n | _ => none
          | _ => #[]
        else #[]
      let mut occF : Array (Name × String × Level) := #[]
      for c in ctors do
        for (n, ls) in constOccurrences (← instLevelMVars c.type) do
          if let some gs := genv.constGlobals[n]? then
            let ls := ls.drop (genv.polyByTarget[n]?.getD 0)
            if gs.size == ls.length then
              for l in gs, σ in ls do occF := occF.push (n, l, ← instantiateLevelMVars σ)
      let mut rsPicks : Array String := #[]
      let doneArity := done
      if !isTemplate && !resLv.isEmpty then
        for (_, _, σ) in occF do
          unless σ.isMVar && !done.contains σ && !inArity.contains σ do continue
          done := done.push σ
          let occσ := occF.filter (·.2.2 == σ)
          let cls := occσ.map (·.2.1)
          let pick := cls.toList.eraseDups.find? fun l =>
            !globals.contains l && !picks.contains l && !rsPicks.contains l && !genv.templateLevels.contains l &&
            occσ.all (fun (n, l', _) => l' == l && ((genv.resultOnly[n]?).getD #[]).contains l) &&
            resLv.any (fun s => entails genv.facts l s 0)
          if let some l := pick then rsPicks := rsPicks.push l
      -- R3G for fields (entry 13): a class occurring only in constructor fields that R3G-F does not take is
      -- the source level of its references too, under the same conditions as an arity class; the block
      -- is tried with it first, and without it (R3″'s 0) when the kernel finds a field too big
      let mut fieldPicks : Array String := #[]
      let mut doneF := doneArity
      if !isTemplate then
        for (_, _, σ) in occF do
          unless σ.isMVar && !doneF.contains σ && !inArity.contains σ do continue
          doneF := doneF.push σ
          let cls := (occ.filter (·.2 == σ)).map (·.1)
          let pick := cls.toList.eraseDups.find? fun l =>
            !globals.contains l && !picks.contains l && !rsPicks.contains l && !fieldPicks.contains l &&
            !genv.templateLevels.contains l &&
            cls.all (fun l' => genv.templateLevels.contains l' || entails genv.facts l l' 0) && (occ.filter (·.1 == l)).all (·.2.hasMVar)
          if let some l := pick then fieldPicks := fieldPicks.push l
      return ({ base with status := "DISCOVERED", implicitLevels := (picks ++ rsPicks ++ fieldPicks).qsort (· < ·),
                          resultSortImplicit := rsPicks.qsort (· < ·), fieldImplicit := fieldPicks.qsort (· < ·) }, none)
    -- R3″: references inside the block (to generalized constants / level-parameter inductives) carry
    -- level metavariables; those not fixed by type-checking (nor taken by R3G) take their least
    -- R3-admissible value 0, and R3 is checked on every universe argument of the block.
    let mut ms : Array LMVarId := #[]
    for e in #[ty] ++ ctors.map (·.type) do
      let e ← instLevelMVars e
      let ((), m) := (levelMVarsOf e).run ms
      ms := m
    for m in ms do assignLevelMVar m .zero
    let ty ← instLevelMVars ty
    ctors ← ctors.mapM fun c => do return { c with type := ← instLevelMVars c.type }
    let mut nchecks := 0
    -- R3 coherence: an argument for an own level of a non-template block must be the level standing
    -- for it, its R2F interpretation ι l (u_l itself when no fact constrains l)
    let interpMap : Std.HashMap String Level :=
      if isTemplate || plain then {} else (ownLevelInterp genv.facts globals (rsMinimalFor genv i rsOwn) genv.decoupled)
    -- R3G (as the audit requires, independently): an implicit level is the argument — its parameter, or its
    -- R2F image — of some reference for that level in the block (else it stands for nothing, and an
    -- occurrence lowered below it would be a specialization; entry 14)
    unless discover do
      for l in extraOwn.filter (!(globalsOfInd i).contains ·) do
        let want := ((interpMap[l]?).getD (.param (levelParamName l))).normalize
        let mut found := false
        for e in #[ty] ++ ctors.map (·.type) do
          for (n, ls) in constOccurrences e do
            if let some gs := genv.constGlobals[n]? then
              let ls := ls.drop (genv.polyByTarget[n]?.getD 0)
              if gs.size == ls.length then
                for g in gs, σ in ls do
                  if g == l && σ.normalize == want then found := true
        unless found do
          return ({ base with status := "UNIVERSE_REJECTED", message := s!"implicit level {l} is not the argument of a reference for that level" }, none)
    for e in #[ty] ++ ctors.map (·.type) do
      match checkUniverseObligations genv globals e interpMap (allowLower := lower) with
      | .ok n => nchecks := nchecks + n
      | .error msg => return ({ base with status := "UNIVERSE_REJECTED", message := msg }, none)
    let base := { base with minimalLevels := ms.size, universeChecks := nchecks }
    -- C: a protected inductive's quantification ranges (arity and constructor binder domains) are
    -- never specialized at a level the source leaves free (its own self-references are not yet in
    -- the environment and are skipped)
    if genv.protectedNames.contains base.source then
      let env ← getEnv
      if let some m := (#[ty] ++ ctors.map (·.type)).findSome? fun e => (typeDomains e).findSome? (freeLevelPin env genv.facts lparams) then
        return ({ base with status := "UNIVERSE_REJECTED",
                            message := s!"protected public declaration: universe specialization refused (a quantification range would be narrowed): {m}" }, none)
    -- M6: non-uniform parameters (the native `nparams_rec`, round-trip checked) become the first
    -- indices of the Lean inductive; the arity and constructor types are unchanged
    let nparamsRec := (i.native.getObjValAs? Nat "nparams_rec").toOption.getD i.npars
    unless nparamsRec ≤ i.npars do
      return ({ base with status := "EXPORT_VALIDATION_FAILED", message := s!"nparams_rec {nparamsRec} exceeds npars {i.npars}" }, none)
    if nparamsRec < i.npars && (isRecord || isTemplate) then
      return ({ base with status := "UNSUPPORTED_FEATURE",
                          message := "non-uniform parameters of a primitive record or template inductive" }, none)
    -- pending validation: the hypotheses become the first parameters (the leaves used after the arity
    -- and constructors were translated must all be among them)
    let hyps ← match hypsRef? with | some ref => ref.get | none => pure #[]
    let ty ← if hyps.isEmpty then pure ty else instLevelMVars (← abstractHyps hyps ty false)
    unless hyps.isEmpty do
      ctors ← ctors.mapM fun c => do return { c with type := ← instLevelMVars (← abstractHyps hyps c.type false) }
      if ty.hasLevelMVar || ctors.any (·.type.hasLevelMVar) then
        return ({ base with status := "UNSUPPORTED_FEATURE",
                            message := "pending inductive: universe levels of its hypothesis parameters left unsolved" }, none)
    let nparamsRec := nparamsRec + hyps.size
    let decl := Declaration.inductDecl lparams nparamsRec [{ name := tname, type := ty, ctors := ctors.toList }] false
    let base := { base with target := some tname, targetKind := "inductive",
                            rule := if isTemplate then "inductive/generated-template"
                                    else if lparams.isEmpty then "inductive/generated" else "inductive/generated-levels" }
    match ← addOrReuse genv.reuseExisting decl with
    | .accepted =>
      let univ := if lparams.isEmpty then UnivRule.mono else .params lparams.length isTemplate
      let tgt : IndTarget := { types := #[tname], ctors := #[cnames], univ, rule := "generated",
                               templateParamPos := templateParams.map (·.2), isStructure := isRecord,
                               templateLevelIdx := (List.range globals.size).toArray.filter
                                 (fun k => templateParams.any (·.1 == globals[k]!)),
                               nonUniform := i.npars - (nparamsRec - hyps.size), pendingHyps := hyps.map (·.2) }
      return ({ base with status := if hyps.isEmpty then "TRANSLATED_AND_CHECKED" else "PENDING_KERNEL_CHECKED",
                          pendingHyps := hyps.map (·.2), targetType := ty, numParams := nparamsRec, primitiveRecord := isRecord,
                          universeLowered := lower, plainLevels := plain, sortInterp := plain && unify,
                          levelParams := lparams, paramLevels := globals, isTemplate, templateParams,
                          implicitLevels := extraOwn.filter (!(globalsOfInd i).contains ·),
                          resultSortImplicit := rsOwn,
                          targetCtors := ctors.map fun c => (c.name, c.type) }, some tgt)
    | .rejected msg => return ({ base with status := "KERNEL_REJECTED", message := msg }, none)

/-! ## Report -/

/-- Speed (entry 14): the source levels of the generalized declarations a declaration depends on
(accepted, pending, statements, blocks), as their parameters stand for them. -/
def depGlobalLevels (genv : GEnv) (deps : Array String) : Std.HashSet String := Id.run do
  let mut out : Std.HashSet String := {}
  for d in deps do
    let mut ts : Array Name := #[]
    if let some t := genv.consts[d]? then ts := ts.push t
    if let some (t, _) := genv.pendingDefs[d]? then ts := ts.push t
    if let some (t, _) := genv.leafStmt[d]? then ts := ts.push t
    if let some it := genv.inds[d]? then ts := ts ++ it.types ++ it.ctors.foldl (· ++ ·) #[]
    for t in ts do
      if let some gs := genv.constGlobals[t]? then
        for g in gs do out := out.insert g
  return out

/-- Speed (entry 14): whether R2⁺ can change any sort of a source term (`factReduceUniverse` drops a
summand somewhere). If not, a fact-reduced tier translates exactly as its plain counterpart. -/
partial def termFactReducible (f : IR.UniverseFacts) : IR.Term → Bool
  | .sort (.type u) => (factReduceUniverse f u).size != u.size
  | .cast t _ ty => termFactReducible f t || termFactReducible f ty
  | .prod _ a b | .lam _ a b => termFactReducible f a || termFactReducible f b
  | .letIn _ v t b => termFactReducible f v || termFactReducible f t || termFactReducible f b
  | .app g as => termFactReducible f g || as.any (termFactReducible f)
  | .evar _ as => as.any (termFactReducible f)
  | .case _ _ _ _ ps _ r c brs => ps.any (termFactReducible f) || termFactReducible f r ||
      termFactReducible f c || brs.any (termFactReducible f ·.2)
  | .proj _ _ _ t => termFactReducible f t
  | .fix defs _ | .cofix defs _ => defs.any fun (_, t, b, _) => termFactReducible f t || termFactReducible f b
  | _ => false

partial def termHasFix : IR.Term → Bool
  | .fix .. | .cofix .. => true
  | .cast t _ ty => termHasFix t || termHasFix ty
  | .prod _ a b | .lam _ a b => termHasFix a || termHasFix b
  | .letIn _ v t b => termHasFix v || termHasFix t || termHasFix b
  | .app g as => termHasFix g || as.any termHasFix
  | .case _ _ _ _ ps _ r c brs => ps.any termHasFix || termHasFix r || termHasFix c || brs.any (termHasFix ·.2)
  | .proj _ _ _ t => termHasFix t
  | _ => false

/-- Speed (entry 14): a late, last-resort tier with its own, smaller heartbeat budget (a fifth of the
declaration's) under a fresh counter; an attempt exhausting it is a failed attempt (`RESOURCE_LIMIT`,
state restored), not the end of the declaration's other tiers. -/
def budgeted (src kind : String) (x : MetaM DeclResult) : MetaM DeclResult := do
  let saved ← saveState
  tryCatchRuntimeEx
    (withTheReader Core.Context (fun c => { c with maxHeartbeats := c.maxHeartbeats / 5 }) (withCurrHeartbeats x))
    fun e => do
      saved.restore
      pure { source := src, kind, status := if e.isRuntime then "RESOURCE_LIMIT" else "TRANSLATION_FAILED",
             message := s!"late tier: {(← e.toMessageData.toString).take 300}" }

/-- Timing (entry 14): every translation attempt of a declaration is logged with its tier's flags, its
time and its status, and the log is reported per row (`tier_times`). -/
def tierLabel (kind : String) (flags : List (String × Bool)) (eo : Nat) : String :=
  let fs := flags.filterMap fun (n, b) => if b then some n else none
  s!"{kind}[{",".intercalate fs}]{if eo == 0 then "" else s!" eo{eo}"}"

/-- Rule P, statements (docs/PROP_LIFT.md §3.3): the head-δ chain `[c₁, …, cₙ]` of a term (under its
products) that reaches a definition translated with a lifted value: each `cᵢ` a transparent monomorphic
constant whose body, β-applied to the arguments, has head `cᵢ₊₁`; `cₙ` is a `prop_lift` row. -/
partial def liftChain (bodies : Std.HashMap String IR.Term) (results : Std.HashMap String DeclResult)
    (t : IR.Term) (fuel : Nat := 8) : Option (Array String) :=
  match t with
  | .prod _ _ b => liftChain bodies results b fuel
  | t => go t fuel
where
  go (t : IR.Term) (fuel : Nat) : Option (Array String) :=
    let (c, args) := match t with
      | .app (.const c _) args => (some c, args)
      | .const c _ => (some c, #[])
      | _ => (none, #[])
    match c, fuel with
    | none, _ | _, 0 => none
    | some c, fuel + 1 =>
      if ((results[c]?).bind (·.propLift)).isSome then some #[c] else
      match bodies[c]? with
      | some b => (go (IR.betaApp b args).flattenApps fuel).map (#[c] ++ ·)
      | none => none

def processConstant (genv : GEnv) (results : Std.HashMap String DeclResult) (c : IR.ConstantDecl)
    (factReduce : Bool := false) (interp : Bool := false) (admit : Bool := false) (cumul : Bool := false)
    (extraOwn : Array String := #[]) (discover : Bool := false) (lower : Bool := false) (delta : Bool := false)
    (stmt : Bool := false) (inferSort : Bool := false) (wfTerm : Bool := false) (inheritSort : Bool := false)
    (hypExact : Bool := false) (joint : Bool := false) (unify : Bool := false) (propLift : Bool := false)
    (phantom : Bool := false) :
    MetaM DeclResult := do
  let t0 ← IO.monoMsNow
  let lbl0 := tierLabel "c" [("fr", factReduce), ("it", interp), ("ad", admit), ("cu", cumul), ("di", discover), ("lo", lower),
      ("de", delta), ("wf", wfTerm), ("rv", inheritSort), ("p3", hypExact), ("jo", joint), ("un", unify), ("pl", propLift), ("ph", phantom)] extraOwn.size
  -- (an attempt aborted by its budget is logged too, then the exception goes on to `budgeted`)
  let r ← tryCatchRuntimeEx (processConstantCore genv results c factReduce interp admit cumul extraOwn discover lower delta stmt inferSort
      wfTerm inheritSort hypExact joint unify propLift phantom) fun e => do
    if let some ref := genv.tierLog then ref.modify (·.push (lbl0, (← IO.monoMsNow) - t0, "RESOURCE_LIMIT | aborted"))
    throw e
  if let some ref := genv.tierLog then
    let lbl := tierLabel "c" [("fr", factReduce), ("it", interp), ("ad", admit), ("cu", cumul), ("di", discover), ("lo", lower),
      ("de", delta), ("wf", wfTerm), ("rv", inheritSort), ("p3", hypExact), ("jo", joint), ("un", unify), ("pl", propLift), ("ph", phantom)] extraOwn.size
    -- (a refused attempt's reason, abbreviated: diagnostics only, the timing file is not the report)
    let st := if r.accepted || r.status == "UNSUPPORTED_FEATURE" then r.status else s!"{r.status} | {r.message.take 600}"
    ref.modify (·.push (lbl, (← IO.monoMsNow) - t0, st))
  return r

def processInductive (genv : GEnv) (results : Std.HashMap String DeclResult) (i : IR.InductiveDecl)
    (raw : Json) (extraOwn : Array String := #[]) (discover : Bool := false) (lower : Bool := false)
    (plain : Bool := false) (rsOwn : Array String := #[]) (unify : Bool := false) :
    MetaM (DeclResult × Option IndTarget) := do
  let t0 ← IO.monoMsNow
  let r ← processInductiveCore genv results i raw extraOwn discover lower plain rsOwn unify
  if let some ref := genv.tierLog then
    let lbl := tierLabel "i" [("di", discover), ("lo", lower), ("pl", plain), ("un", unify)] extraOwn.size
    ref.modify (·.push (lbl, (← IO.monoMsNow) - t0, r.1.status))
  return r

partial def levelJson : Level → Json
  | .zero => Json.mkObj [("k", "zero")]
  | .succ l => Json.mkObj [("k", "succ"), ("l", levelJson l)]
  | .max a b => Json.mkObj [("k", "max"), ("a", levelJson a), ("b", levelJson b)]
  | .imax a b => Json.mkObj [("k", "imax"), ("a", levelJson a), ("b", levelJson b)]
  | .param n => Json.mkObj [("k", "param"), ("n", n.toString)]
  | .mvar _ => Json.mkObj [("k", "mvar")]

/-- Lean `Expr` as JSON, for the independent audit. Binder names are kept but are not compared. -/
partial def exprJson : Expr → Json
  | .bvar i => Json.mkObj [("k", "bvar"), ("i", i)]
  | .fvar _ => Json.mkObj [("k", "fvar")]
  | .mvar _ => Json.mkObj [("k", "mvar")]
  | .sort l => Json.mkObj [("k", "sort"), ("l", levelJson l)]
  | .const n ls => Json.mkObj [("k", "const"), ("n", n.toString), ("u", Json.arr (ls.map levelJson).toArray)]
  | .app f a => Json.mkObj [("k", "app"), ("f", exprJson f), ("a", exprJson a)]
  | .lam n t b _ => Json.mkObj [("k", "lam"), ("n", n.toString), ("t", exprJson t), ("b", exprJson b)]
  | .forallE n t b _ => Json.mkObj [("k", "forall"), ("n", n.toString), ("t", exprJson t), ("b", exprJson b)]
  | .letE n t v b _ =>
    Json.mkObj [("k", "let"), ("n", n.toString), ("t", exprJson t), ("v", exprJson v), ("b", exprJson b)]
  | .lit (.natVal n) => Json.mkObj [("k", "natlit"), ("v", n)]
  | .lit (.strVal s) => Json.mkObj [("k", "strlit"), ("v", s)]
  | .mdata _ e => Json.mkObj [("k", "mdata"), ("e", exprJson e)]
  | .proj s i e => Json.mkObj [("k", "proj"), ("s", s.toString), ("i", i), ("e", exprJson e)]

def DeclResult.toJson (r : DeclResult) : Json :=
  -- (two typed halves: one long list literal is beyond the elaborator's coercion heuristics)
  let universes : List (String × Json) := [
    ("universe_cumulativity", Json.bool r.cumulativity),
    ("universe_lowered", Json.bool r.universeLowered),
    ("plain_levels", Json.bool r.plainLevels),
    ("sort_interp", Json.bool r.sortInterp),
    ("prop_lift", match r.propLift with | some k => Json.num k | none => Json.null),
    ("prop_lift_coercions", Json.num r.propLiftCoercions),
    ("prop_lift_unfold", Json.arr (r.propLiftUnfold.map Json.str)),
    ("phantom_lowered", Json.arr (r.phantomLowered.map Json.str)),
    ("coinductive_as_inductive", Json.bool r.coinductiveAsInductive),

    ("delta_inlined", Json.arr (r.deltaInlined.map Json.str)),
    ("r2bp_levels", Json.arr (r.r2bpLevels.map fun (m, l) =>
      Json.mkObj [("level", m), ("sigma", levelJson l), ("in_type", Json.bool (r.r2bpInType.contains m))])),
    ("sort_lowered_levels", Json.arr (r.sortLevels.map fun (m, l) => Json.mkObj [("level", m), ("sigma", levelJson l)])),
    ("result_sort_inherited", Json.bool r.resultSortInherited),
    ("result_sort_implicit_levels", Json.arr (r.resultSortImplicit.map Json.str)),
    ("level_copies", Json.arr (r.levelCopies.map fun (l, cs) => Json.mkObj [("level", Json.str l), ("copies", Json.arr (cs.map Json.str))])),
    ("level_split", Json.arr (r.levelSplit.map fun (l, ps, cs) =>
      Json.mkObj [("level", Json.str l), ("params", Json.arr (ps.map fun (k : Nat) => Json.num k)), ("copies", Json.arr (cs.map Json.str))])),
    ("protected", Json.bool r.protectedIface),
    ("pending_hypotheses", Json.arr (r.pendingHyps.map Json.str))]
  let rest : List (String × Json) := [
    ("source", r.source), ("kind", r.kind), ("status", r.status), ("rule", r.rule),
    ("target", match r.target with | some n => Json.str n.toString | none => .null),
    ("target_kind", r.targetKind), ("message", r.message),
    ("path", Json.arr (r.path.map Json.str).toArray),
    ("blocked_by", Json.arr (r.blockedBy.map Json.str)),
    ("target_type", match r.targetType with | some e => exprJson e | none => .null),
    ("target_value", match r.targetValue with | some e => exprJson e | none => .null),
    ("level_params", Json.arr (r.levelParams.map (Json.str ·.toString)).toArray),
    ("num_params", r.numParams),
    ("template", r.isTemplate),
    ("primitive_record", r.primitiveRecord),
    ("universe_minimal_levels", r.minimalLevels),
    ("solved_levels", Json.arr (r.bodyLevels.map fun (m, l) => Json.mkObj [("level", m), ("sigma", levelJson l)])),
    ("template_params", Json.arr (r.templateParams.map fun (l, k) => Json.mkObj [("level", l), ("param", k)])),
    ("universe_level_defaults", r.levelDefaults),
    ("universe_poly_params", r.polyParams),
    ("sort_fact_reduced", r.factReduced),
    ("implicit_levels", Json.arr (r.implicitLevels.map Json.str)),
    ("admitting_levels", Json.arr (r.admittingLevels.map Json.str)),
    ("level_interp", Json.arr (r.levelInterp.map fun (l, x) => Json.mkObj [("level", l), ("sigma", levelJson x)])),
    ("universe_checks", r.universeChecks),
    ("universe_diagnostics", Json.arr (r.levelDiagnostics.map Json.str)),
    ("universe_residuals", if r.residualParams.isEmpty then .null else Json.mkObj [
      ("params", Json.arr (r.residualParams.map (Json.str ·.toString)).toArray),
      ("defaults", Json.arr (r.residualDefaults.map levelJson).toArray),
      ("justification", "kernel accepted the declaration with these levels as fresh universe parameters"),
      ("generic_type", match r.residualType with | some e => exprJson e | none => .null),
      ("generic_value", match r.residualValue with | some e => exprJson e | none => .null)]),
    ("target_ctors", Json.arr (r.targetCtors.map fun (n, e) =>
      Json.mkObj [("name", n.toString), ("type", exprJson e)]))]
  -- assembly (docs/ASSEMBLY.md): the row's assembly state; a carried-over row is its validated JSON
  let asm : List (String × Json) := if r.assembly.isEmpty then [] else [
    ("assembly", r.assembly), ("assembly_note", r.assemblyNote), ("proof_state", r.proofState),
    ("assembled_from", match r.assembledFrom with | some n => Json.str n.toString | none => .null),
    ("proof_target", match r.proofTarget with | some n => Json.str n.toString | none => .null),
    ("proof_template", match r.proofTemplate with | some n => Json.str n.toString | none => .null),
    ("proof_type", match r.proofType with | some e => exprJson e | none => .null),
    ("proof_value", match r.proofValue with | some e => exprJson e | none => .null)]
  -- B: a translator-generated row names its source declaration and kind
  let syn : List (String × Json) := if r.synthesizedFrom.isEmpty then [] else
    [("synthesized_from", r.synthesizedFrom), ("synthetic_kind", r.syntheticKind)]
  match r.verbatim with
  | some v@(.obj _) => asm.foldl (fun j (k, x) => j.setObjVal! k x) v
  | _ => Json.mkObj (rest ++ universes ++ syn ++ asm)

/-! ## Assembly (docs/ASSEMBLY.md)

The validated statement library (`Rocq2LeanOut`) and the verified proof templates
(`RocqProofTemplates.T<task_id>.proof`, each proving its task statement, generalized over the task's
prerequisites) are imported. The export is translated again, in order:

* a row the validated library accepted is translated again and must be *identical* to the imported
  declaration (`addOrReuse`); it is not added a second time;
* a proof task whose statement is accepted and whose template was supplied gets its final theorem
  `Rocq.<leaf> : Rocq.<leaf>.statement := T Rocq.<p₁> … Rocq.<pₖ>` (its prerequisites' final
  theorems), *if the kernel accepts that instantiation at the final statement*. A template about a
  pending artifact does not prove a statement about a re-emitted inductive (a new type): the kernel
  refuses, and the row records `ASSEMBLY_TRANSPORT_REQUIRED` — nothing is cast or identified;
* a pending row whose prerequisite leaves all have final theorems, and whose dependencies are all
  available, is translated again without hypotheses, as `Rocq.<name>` (`ASSEMBLED`);
* every other row is carried over unchanged from the validated report (its pending artifact stays in
  `Rocq2LeanOut`; `PENDING`, `OPAQUE_BINDING_PENDING`, `ASSEMBLY_BLOCKED`, `NOT_TRANSLATED`).

Opaque data is never assembled here: no submitted value may stand for a source body (A′). -/

/-- Assembly input: the validated report's rows by source, and the verified proof templates by proof
task (leaf key ↦ template constant). -/
structure AsmInput where
  validated : Std.HashMap String Json
  templates : Std.HashMap String Name
  deriving Inhabited

private def jStr (j : Json) (k : String) : String := (j.getObjValAs? String k).toOption.getD ""

def asmAcceptedSt : List String := ["TRANSLATED_AND_CHECKED", "STATEMENT_KERNEL_CHECKED", "BOOTSTRAP_RESOLVED"]
def asmPendingSt : List String := ["PENDING_KERNEL_CHECKED", "STATEMENT_PENDING_KERNEL_CHECKED"]

/-- A row carried over from the validated report. -/
def asmCopy (d : IR.Decl) (v : Json) (state note : String) : DeclResult :=
  { source := d.name, kind := match d with | .constant _ => "constant" | _ => "inductive",
    status := jStr v "status", message := jStr v "message",
    target := if (jStr v "target").isEmpty then none else some (jStr v "target").toName,
    pendingHyps := (v.getObjValAs? (Array String) "pending_hypotheses").toOption.getD #[],
    blockedBy := (v.getObjValAs? (Array String) "blocked_by").toOption.getD #[],
    assembly := state, assemblyNote := note, verbatim := some v }

/-- The dependencies of a declaration (its statement's, for a proof task). -/
def declDeps (d : IR.Decl) : Array String := match d with
  | .constant c => c.typeDeps ++ c.bodyDeps
  | .inductive i => i.typeDeps.filter (· != i.name)

/-- Before translating `d` in assembly: `some row` when the validated row is carried over unchanged. -/
def asmBefore (a : AsmInput) (opaqueData : Std.HashSet String) (results : Std.HashMap String DeclResult)
    (d : IR.Decl) : DeclResult ⊕ Unit :=
  match a.validated[d.name]? with
  | none => .inl { source := d.name, kind := "", status := "ASSEMBLY_REJECTED", assembly := "ASSEMBLY_REJECTED",
                   assemblyNote := "no row in the validated report" }
  | some v =>
    let st := jStr v "status"
    if asmAcceptedSt.contains st then .inr ()
    else if !asmPendingSt.contains st then .inl (asmCopy d v "NOT_TRANSLATED" s!"validated status {st}")
    else
      let hs := (v.getObjValAs? (Array String) "pending_hypotheses").toOption.getD #[]
      let waiting := hs.filter fun h => !((results[h]?.map (·.proofTarget.isSome)).getD false)
      if !waiting.isEmpty then
        let opq := waiting.filter opaqueData.contains
        if opq.isEmpty then .inl (asmCopy d v "PENDING" s!"waiting for proofs of {waiting}")
        else
          let rest := waiting.filter (!opq.contains ·)
          let more := if rest.isEmpty then "" else s!" and proofs of {rest}"
          .inl (asmCopy d v "OPAQUE_BINDING_PENDING"
            s!"waiting for opaque data values {opq} (not assembled: no submitted value stands for a source body; A′){more}")
      else
        let blocked := (declDeps d).filter fun x => match results[x]? with
          | some r => !r.available
          | none => false
        if blocked.isEmpty then .inr ()
        else .inl (asmCopy d v "ASSEMBLY_BLOCKED" s!"dependencies not assembled: {blocked}")

/-- The final theorem of a proof task: its verified template instantiated at its prerequisites' final
theorems, at the final (accepted, audited) statement. Refused — `ASSEMBLY_TRANSPORT_REQUIRED` — unless
the kernel accepts exactly that; the submitted proof is never rewritten or cast. -/
def assembleProof (results : Std.HashMap String DeclResult) (r : DeclResult) (leaf : String) (tmpl : Name)
    (hyps : Array String) : MetaM DeclResult := do
  let transport (msg : String) : DeclResult :=
    { r with proofState := "ASSEMBLY_TRANSPORT_REQUIRED", proofTemplate := some tmpl,
             assemblyNote := s!"verified template {tmpl} not reusable at the final statement: {msg}" }
  let some stmt := r.target | return transport "no statement target"
  let thm := targetName leaf
  if (← getEnv).contains thm then return transport s!"{thm} already declared"
  let some tci := (← getEnv).find? tmpl | return transport "template not imported"
  let mut val := mkConst tmpl (← tci.levelParams.mapM fun _ => mkFreshLevelMVar)
  for h in hyps do
    let some pt := (results[h]?).bind (·.proofTarget) | return transport s!"prerequisite {h} has no final theorem"
    let hci ← getConstInfo pt
    val := mkApp val (mkConst pt (← hci.levelParams.mapM fun _ => mkFreshLevelMVar))
  let want := mkConst stmt (r.levelParams.map Level.param)
  let ok ← try isDefEq (← inferType val) want catch _ => pure false
  unless ok do return transport "the instantiated template's type is not convertible to the final statement"
  val ← instantiateMVars val
  if val.hasLevelMVar || val.hasExprMVar then return transport "universe levels of the instantiation left unresolved"
  match ← addChecked (.thmDecl { name := thm, levelParams := r.levelParams, type := want, value := val, all := [thm] }) with
  | .accepted =>
    return { r with proofState := "PROOF_ASSEMBLED", proofTarget := some thm, proofTemplate := some tmpl,
                    proofType := some want, proofValue := some val }
  | .rejected msg => return transport s!"kernel: {msg.take 600}"

/-- After translating `d` in assembly: classify the row against its validated row, and assemble the
final theorem of a proof task. Returns the row and whether the translation result (and its `GEnv`
update) is kept. -/
def asmAfter (a : AsmInput) (opaqueData : Std.HashSet String) (results : Std.HashMap String DeclResult)
    (d : IR.Decl) (r : DeclResult) : MetaM (DeclResult × Bool) := do
  let some v := a.validated[d.name]? | return (r, false)
  let vst := jStr v "status"
  let mut r := r
  if asmAcceptedSt.contains vst then
    -- the validated row, reproduced exactly (determinism of the translation, identity with the import)
    let rj := r.toJson
    let keys := ["status", "target", "target_kind", "target_type", "target_value", "target_ctors", "level_params",
                 "pending_hypotheses"]
    let diff := keys.filter fun k => rj.getObjValD k != v.getObjValD k
    if diff.isEmpty then r := { r with assembly := "VALIDATED" }
    else return ({ r with assembly := "REUSE_MISMATCH", assemblyNote := s!"differs from the validated row in {diff}" }, true)
  else
    if !asmAcceptedSt.contains r.status then
      return (asmCopy d v "ASSEMBLY_REJECTED" s!"translation without hypotheses gave {r.status}: {r.message.take 600}", false)
    r := { r with assembly := "ASSEMBLED", assembledFrom := (if (jStr v "target").isEmpty then none else some (jStr v "target").toName) }
  -- proof tasks: the final theorem
  if r.status == "STATEMENT_KERNEL_CHECKED" then
    if opaqueData.contains d.name then
      r := { r with proofState := "OPAQUE_BINDING_PENDING",
                    assemblyNote := "opaque data: a value is not accepted from a submission (A′ translates the source body)" }
    else match a.templates[d.name]? with
      | none => r := { r with proofState := "PROOF_NOT_SUPPLIED" }
      | some tmpl =>
        let hs := (v.getObjValAs? (Array String) "pending_hypotheses").toOption.getD #[]
        r ← assembleProof results r d.name tmpl hs
  return (r, true)

/-- Translate all declarations of an export, in order (`asm?`: assembly, see above). -/
def translateSource (src : IR.Source) (protectedNames : Std.HashSet String := {}) (asm? : Option AsmInput := none) :
    MetaM (Array DeclResult) := do
  let irBodies := src.decls.foldl (init := ({} : Std.HashMap String IR.Term)) fun m d => match d with
    | .constant c => match c.body, c.universes with
      | some b, .monomorphic => if c.bodyState == "transparent" then m.insert c.name b else m
      | _, _ => m
    | _ => m
  let setMotive := src.decls.foldl (init := ({} : Std.HashSet String)) fun m d => match d with
    | .constant c => if irBodies.contains c.name && c.type.hasSetMotive then m.insert c.name else m
    | _ => m
  let erasingPoly := src.decls.foldl (init := ({} : Std.HashMap String IR.Term)) fun m d => match d with
    | .constant c => match erasingPolyBody? c with | some b => m.insert c.name b | none => m
    | _ => m
  let phantomDefs := src.decls.foldl (init := ({} : Std.HashMap String (Array (Nat × Nat)))) fun m d => match d with
    | .constant c => match phantomDefPairs? c with | some ps => m.insert c.name ps | none => m
    | _ => m
  let phantomProofs := src.decls.foldl (init := ({} : Std.HashSet String)) fun m d => match d with
    | .constant c => if phantomDefs.contains c.name && !(c.bodyState == "transparent" && c.body.isSome) then m.insert c.name else m
    | _ => m
  let stmtMode := ((src.header.getObjVal? "mode").toOption.bind (fun m => (m.getObjValAs? String "name").toOption)) == some "statement"
  -- R-CARRIER P1: parameter carrier levels of every exported block, once, from the source
  let carrierSet : Std.HashSet String := src.decls.foldl (fun acc d => match d with
    | .inductive i => if (i.native.getObjValAs? Bool "template").toOption == some true then acc
                      else (Split.carrierLevels i).foldl (·.insert ·) acc
    | _ => acc) {}
  let decoupled : Std.HashSet (String × String) := src.decls.foldl (fun acc d => match d with
    | .inductive i => if (i.native.getObjValAs? Bool "template").toOption == some true then acc
                      else (Split.decoupledPairs i).foldl (·.insert ·) acc
    | _ => acc) {}
  let tierLog ← IO.mkRef (#[] : Array (String × Nat × String))
  let mut genv : GEnv := { facts := src.facts, irBodies, setMotive, erasingPoly, phantomDefs, phantomProofs, protectedNames, stmtMode, reuseExisting := asm?.isSome, carrierSet, decoupled, tierLog := some tierLog }
  let mut results : Std.HashMap String DeclResult := {}
  let mut out := #[]
  let opaqueData : Std.HashSet String := src.decls.foldl (init := {}) fun m d => match d with
    | .constant c => if c.bodyState == "opaque_interface" then m.insert c.name else m
    | _ => m
  -- B (docs/TERMINATION.md): the validated rows generated for each declaration, in report order
  let generatedOf : Std.HashMap String (Array (String × Json)) := match asm? with
    | none => {}
    | some a => a.validated.fold (init := {}) fun m k v =>
      let p := jStr v "synthesized_from"
      if p.isEmpty then m else m.insert p ((m.getD p #[]).push (k, v))
  for d in src.decls do
    -- assembly, B: a termination obligation of `d` (its statement is in the validated library) gets its
    -- final theorem before `d` is translated again, so that the lowering can use it
    if let some a := asm? then
      for (k, v) in (generatedOf.getD d.name #[]).qsort (·.1 < ·.1) do
        unless jStr v "synthetic_kind" == "termination" do continue
        let lps := ((v.getObjValAs? (Array String) "level_params").toOption.getD #[]).toList.map String.toName
        let c0 := asmCopy d v "VALIDATED" ""
        let mut tr : DeclResult := { c0 with source := k, levelParams := lps }
        if jStr v "status" != "STATEMENT_KERNEL_CHECKED" then
          tr := { tr with assembly := "NOT_TRANSLATED", assemblyNote := s!"validated status {jStr v "status"}" }
        else match a.templates[k]? with
          | none => tr := { tr with proofState := "PROOF_NOT_SUPPLIED" }
          | some tmpl => tr ← assembleProof results tr k tmpl #[]
        if let some thm := tr.proofTarget then
          genv := { genv with consts := genv.consts.insert k thm, constLevels := genv.constLevels.insert k tr.levelParams.length }
        if let some n := tr.target then
          genv := { genv with leafStmt := genv.leafStmt.insert k (n, #[]), leafStmtTargets := genv.leafStmtTargets.insert n }
        results := results.insert k tr
        out := out.push tr
    -- assembly: a row that stays as validated is carried over without translation
    if let some a := asm? then
      if let .inl r := asmBefore a opaqueData results d then
        let r := { r with protectedIface := protectedNames.contains r.source }
        results := results.insert r.source r
        out := out.push r
        -- (B: its other generated rows are carried over with it)
        for (k, v) in (generatedOf.getD d.name #[]).qsort (·.1 < ·.1) do
          unless jStr v "synthetic_kind" == "termination" do
            let x0 := asmCopy d v r.assembly r.assemblyNote
            let x := { x0 with source := k }
            results := results.insert k x
            out := out.push x
        continue
    -- the heartbeat budget is per declaration; a declaration exceeding it is a RESOURCE_LIMIT row
    let saved ← saveState
    if let some ref := genv.tierLog then ref.set #[]
    let tDecl ← IO.monoMsNow
    -- (an internal error of one declaration is its TRANSLATION_FAILED row, not the end of the run)
    -- resource limits per declaration (docs/TRUST.md): reflection proofs (ring/lia certificates)
    -- evaluate the translated normalizers on concrete data during the checks
    let limits := fun (c : Core.Context) => { c with maxRecDepth := 8192, maxHeartbeats := c.maxHeartbeats * 5 }
    let r? ← tryCatchRuntimeEx (Sum.inl <$> withTheReader Core.Context limits
        (withCurrHeartbeats (translateSplit genv results d))) fun e => do
      saved.restore
      pure (Sum.inr (e.isRuntime, ← e.toMessageData.toString))
    let (r, genv?) := match r? with
      | .inl (r, genv') => (r, some genv')
      | .inr (rt, msg) =>
        ({ source := d.name, kind := match d with | .constant _ => "constant" | _ => "inductive",
           status := if rt then "RESOURCE_LIMIT" else "TRANSLATION_FAILED",
           message := if rt then s!"resource limit per declaration: {msg.take 300}" else s!"internal error: {msg.take 600}" }, none)
    let mut r := r
    r := { r with timeMs := (← IO.monoMsNow) - tDecl, tierTimes := ← match genv.tierLog with | some ref => ref.get | none => pure #[] }
    match asm? with
    | none => if let some g := genv? then genv := g
    | some a =>
      let (r', keep) ← asmAfter a opaqueData results d r
      r := r'
      if keep then if let some g := genv? then genv := g
      -- a proof task's final theorem is referenced like an accepted constant by its dependents
      if let some thm := r.proofTarget then
        genv := { genv with consts := genv.consts.insert d.name thm,
                            constLevels := genv.constLevels.insert d.name r.levelParams.length,
                            constGlobals := if r.levelParams.isEmpty then genv.constGlobals
                              else genv.constGlobals.insert thm r.paramLevels }
        if r.polyParams > 0 then
          genv := { genv with constPoly := genv.constPoly.insert d.name r.polyParams,
                              polyByTarget := genv.polyByTarget.insert thm r.polyParams }
    r := { r with protectedIface := protectedNames.contains r.source }
    -- (B: termination statements are reported before their declaration, unfolding equations after
    -- it: each row only references rows reported earlier)
    let gen := r.synthetic
    r := { r with synthetic := #[] }
    let mut after : Array DeclResult := #[]
    for x0 in gen do
      let mut x := x0
      -- assembly, B: a generated row is classified against its validated row like any row (a termination
      -- obligation was handled above: only one with hypotheses could be generated again here)
      if let some a := asm? then
        match a.validated[x.source]? with
        | none => x := { x with assembly := "ASSEMBLY_REJECTED", assemblyNote := "no row in the validated report" }
        | some v =>
          if asmAcceptedSt.contains (jStr v "status") then
            let xj := x.toJson
            let diff := ["status", "target", "target_kind", "target_type", "target_value", "level_params", "pending_hypotheses"].filter
              fun k => xj.getObjValD k != v.getObjValD k
            x := if diff.isEmpty then { x with assembly := "VALIDATED" }
              else { x with assembly := "REUSE_MISMATCH", assemblyNote := s!"differs from the validated row in {diff}" }
          else if asmAcceptedSt.contains x.status then
            x := { x with assembly := "ASSEMBLED", assembledFrom := (if (jStr v "target").isEmpty then none else some (jStr v "target").toName) }
          else
            x := { x with assembly := "ASSEMBLY_REJECTED", assemblyNote := s!"generated again as {x.status}" }
          if x.status == "STATEMENT_KERNEL_CHECKED" && x.proofTarget.isNone && !x.assembly.startsWith "ASSEMBLY_REJ" then
            match a.templates[x.source]? with
            | none => x := { x with proofState := "PROOF_NOT_SUPPLIED" }
            | some tmpl =>
              x ← assembleProof results x x.source tmpl ((v.getObjValAs? (Array String) "pending_hypotheses").toOption.getD #[])
      if x.syntheticKind == "termination" then
        results := results.insert x.source x
        out := out.push x
      else after := after.push x
    results := results.insert r.source r
    out := out.push r
    for x in after do
      results := results.insert x.source x
      out := out.push x
  return out
where
  /-- R-SPLIT (docs/LEVEL_SPLIT.md, experimental): a declaration with an eligible level is first
  translated through its split view (each copy a universe parameter; the copies inherit the level's
  upper bounds); if that view is not accepted, the declaration is translated as before. References
  read every copy as the source level itself (R3 at references: an argument `a ≤ l`). -/
  translateSplit (genv0 : GEnv) (results : Std.HashMap String DeclResult) (d : IR.Decl) : MetaM (DeclResult × GEnv) := do
    let some (d', infos) := Split.view d | translateDecl genv0 results d
    let copies := infos.foldl (fun a inf => a ++ inf.names) #[]
    let back : String → String := fun x => (infos.find? (·.names.contains x)).map (·.level) |>.getD x
    let facts' := genv0.facts.extend copies (Split.copiedRelations genv0.facts infos)
    let saved ← saveState
    let (r, genv) ← translateDecl { genv0 with facts := facts' } results d'
    -- (every copy must stay a universe parameter: a copy solved or defaulted would not be the split view)
    let generic := copies.all fun c => r.levelParams.contains (levelParamName c)
    if generic && (r.ok || r.status == "PENDING_KERNEL_CHECKED" || r.status == "STATEMENT_KERNEL_CHECKED" ||
        r.status == "STATEMENT_PENDING_KERNEL_CHECKED") then
      -- references: each copy stands for the source level
      let mut cg := genv.constGlobals
      for n in (r.target.toList ++ (r.targetCtors.map (·.1)).toList) do
        if let some gs := cg[n]? then cg := cg.insert n (gs.map back)
      let note := s!"R-SPLIT: {infos.map fun i => (i.level, i.params)}"
      return ({ r with levelSplit := infos.map fun i => (i.level, i.params, i.names),
                       levelDiagnostics := r.levelDiagnostics.push note },
              { genv with constGlobals := cg })
    saved.restore
    let (r0, g0) ← translateDecl genv0 results d
    let why := if generic then s!"{r.status}: {r.message.take 300}" else "a copy was not kept as a universe parameter"
    return ({ r0 with levelDiagnostics := r0.levelDiagnostics.push s!"R-SPLIT view not accepted ({why}); unsplit translation" }, g0)

  /-- One declaration (the attempts and retry tiers), with the environment it extends. -/
  translateDecl (genv0 : GEnv) (results : Std.HashMap String DeclResult) (d : IR.Decl) : MetaM (DeclResult × GEnv) := do
    let mut genv := genv0
    let r ← match d with
      | .constant c0 =>
        -- Statement mode (docs/STATEMENT_ONLY_DESIGN.md): a proof-valued constant or an extracted
        -- obligation is translated as its statement, `def Rocq.<name>.statement : Prop := ⟦T⟧`, by the
        -- same path as any definition, with every universe level of the statement an own type level
        -- (a parameter: a statement is never specialized by defaulting a level). The constant itself
        -- gets no Lean term: what needs it is pending (its proof is a task for the proving agent).
        -- a definition whose termination Rocq's guard established on a proof subterm that is now an
        -- obligation (exporter: "termination": deferred): no Lean rule yet; never translated with an
        -- unchecked recursion
        if ((src.rawDecls[c0.name]?).bind (fun j => (j.getObjVal? "termination").toOption)).isSome then
          return ({ source := c0.name, kind := "constant", status := "UNSUPPORTED_FEATURE",
                    message := "termination deferred (recursion on a proof subterm that became an obligation): no translation rule" }, genv)
        if c0.bodyState == "obligation_extraction_failed" then
          return ({ source := c0.name, kind := "constant", status := "OBLIGATION_EXTRACTION_REFUSED",
                    message := "Rocq's kernel did not accept the definition with its proof subterms extracted (e.g. computation that eliminates a proof); exported without body" }, genv)
        let isStmt := c0.bodyState == "statement_only" || c0.bodyState == "obligation" || c0.bodyState == "opaque_interface"
        -- opaque data (Qed, type not a proposition): Rocq never unfolds it; its type is kernel-checked as
        -- `def Rocq.<name>.type : Sort u := ⟦T⟧` (the exporter's native sort of `T`) and providing a value
        -- is the task
        let sortT? : Option IR.Term := if c0.bodyState == "opaque_interface" then
            match (src.rawDecls[c0.name]?).bind (fun j => (j.getObjVal? "type_sort").toOption) with
            | some j => (IR.parseTerm j).toOption
            | none => none
          else none
        if c0.bodyState == "opaque_interface" && sortT?.isNone then
          return ({ source := c0.name, kind := "constant", status := "EXPORT_VALIDATION_FAILED",
                    message := "opaque data without its native sort" }, genv)
        -- (an opaque interface's declared sort is inferred from its translated type, `inferSort`; the
        -- native sort only certifies that the export carries one and contributes no levels: `Set`)
        let c : IR.ConstantDecl := if isStmt then
            { c0 with name := c0.name ++ (if c0.bodyState == "opaque_interface" then ".type" else ".statement"),
                      type := if sortT?.isSome then .sort (.type #[{ level := .set, offset := 0 }]) else .sort .prop,
                      body := some c0.type,
                      bodyState := "transparent", typeDeps := #[], bodyDeps := c0.typeDeps }
          else c0
        -- R8 first when the type has motive levels: the sort-level form is strictly more general
        -- (u := v+1 gives the R2 form), so it is kept whenever the kernel accepts it
        -- R3G discovery pass (adds nothing): implicit levels of the type, then every attempt below with
        -- them as own levels; if all fail, the same attempts without them (the earlier behaviour)
        -- (The discovery pass for constants, `discover := true`, is not used yet: implicit levels
        -- relate to other references only through `max` arguments that Lean's level unifier cannot
        -- invert, which made more general constants break their own dependants. In-place R3G below.)
        -- (an opaque interface's levels include those of its native sort, which can name a level that
        -- its type only reaches through a referenced constant)
        let exts : List (Array String) := [if isStmt then (globalsOf c0.type).toArray.qsort (· < ·) else #[]]
        let mut r : DeclResult := default
        let mut first : Option DeclResult := none
        let mut lastTier : Option DeclResult := none
        -- P0: a tier that would only succeed by specializing a protected statement
        let mut iface : Option DeclResult := none
        -- rule Q-a (docs/PHANTOM_SORT.md): the declaration with its phantom checks' sort arguments marked, and
        -- the levels occurring only there
        let (cQ, gone) : IR.ConstantDecl × Array String := Id.run do
          if genv.phantomDefs.isEmpty then return (c, #[])
          let (tyQ, ch1) := erasePhantomSorts genv.phantomDefs c.type
          let (bdQ, ch2) := match c.body with
            | some b => let (b', ch) := erasePhantomSorts genv.phantomDefs b; (some b', ch)
            | none => (none, false)
          if !(ch1 || ch2) then return (c, #[])
          let before := match c.body with | some b => globalsOf b (globalsOf c.type) | none => globalsOf c.type
          let after := match bdQ with | some b => globalsOf b (globalsOf tyQ) | none => globalsOf tyQ
          return ({ c with type := tyQ, body := bdQ }, (before.toArray.filter (!after.contains ·)).qsort (· < ·))
        for eo in exts do
          let sBefore ← saveState
          -- (rule Q-a first, when it applies: strictly more general, as it leaves the phantom-only levels out
          -- and every other level as before; otherwise a plain attempt may identify the carriers of a phantom
          -- check, a narrowing)
          -- (a declaration using a proof of a phantom check, HB's `id_phant` — a prerequisite then used at a
          -- different lowered sort at each occurrence — starts with per-instance hypotheses, P3: 587/608 on the
          -- GEL frontier; the plain attempt follows if it fails, so only the order differs)
          let rQ ← if gone.isEmpty then pure none else do
            let p3First := (c0.typeDeps ++ c0.bodyDeps).any genv.phantomProofs.contains
            let mut res : Option DeclResult := none
            for p3 in (if p3First then [true, false] else [false]) do
              let q ← processConstant genv results cQ (stmt := isStmt) (inferSort := c0.bodyState == "opaque_interface")
                (extraOwn := eo.filter (!gone.contains ·)) (hypExact := p3) (phantom := true)
              if q.accepted then
                res := some { q with phantomLowered := gone }
                break
              sBefore.restore
            pure res
          let r0 ← if let some q := rQ then pure q else
            if (motiveLevels c.type).isEmpty then processConstant genv results c (stmt := isStmt) (inferSort := c0.bodyState == "opaque_interface") (extraOwn := eo) else do
              let a ← processConstant genv results c (stmt := isStmt) (inferSort := c0.bodyState == "opaque_interface") (admit := true) (extraOwn := eo)
              if a.accepted then pure a else processConstant genv results c (stmt := isStmt) (inferSort := c0.bodyState == "opaque_interface") (extraOwn := eo)
          first := some r0          -- the diagnosis kept is that of the last (earlier-behaviour) attempt
          r := r0
          -- P2 for definitions (ITERATION_LOG entry 10): a definition accepted only with defaulted levels is
          -- retried with jointly occurring level metavariables identified (as for statements) and the M6
          -- bounded solver on postponed `max` constraints (`max(?a, X) = max(?b, X)` ↦ `?a := ?b`: the
          -- two references at one instance, as in the source); the retry is kept only when it is accepted
          -- with fewer defaulted levels
          if r.accepted && !isStmt && genv.stmtMode && r.levelDefaults > 0 then
            let sAcc ← saveState
            let mut better := false
            for it in [false, true] do
              sBefore.restore
              let r' ← processConstant genv results c (stmt := isStmt) (inferSort := c0.bodyState == "opaque_interface")
                (interp := it) (extraOwn := eo) (joint := true)
              -- (only parameters of the type: a level of the value alone generalizes nothing a use can see,
              -- and its argument at uses is then undetermined — e.g. ssrnat.leq inside fintype.ordinal)
              let tyPs := match r'.targetType with
                | some t => (collectLevelParams {} t).params
                | none => #[]
              if r'.accepted && r'.levelDefaults < r.levelDefaults && r'.levelParams.all tyPs.contains then
                r := { r' with levelDiagnostics := r'.levelDiagnostics.push s!"P2-def: {r.levelDefaults} defaulted level(s) reduced to {r'.levelDefaults} (joint identification, bounded solver)" }
                better := true
                break
            unless better do sAcc.restore
          if r.accepted then break
          -- Universe retry ladder (docs/UNIVERSE_TRANSLATION.md): a kernel or universe rejection under
          -- R2 is retried with fact-reduced universes (R2⁺), then with the fact interpretation of the
          -- own levels (R2F-c), then both; the first accepted translation is kept.
          let retry (st : String) := st == "KERNEL_REJECTED" || st == "UNIVERSE_REJECTED"
          if retry r.status then
            -- strict tiers first; the cumulativity tier (R3↑, R2B-P) only when they all fail
            -- R3↓ last (cumulativity tier, reported): references instantiated below shared levels
            -- coherence by unification (§6 of docs/COHERENCE_READINGS.md) after the strict tiers: the same
            -- checks, with shared levels instantiated per occurrence and rebound where typing leaves them free
            -- (speed, entry 14: per-occurrence tiers only for a constant sharing a level with a reference)
            let cDep := depGlobalLevels genv (c.typeDeps ++ c.bodyDeps)
            let cShared := (globalsOf (c.body.getD (.sort .prop)) (globalsOf c.type)).toList.any cDep.contains || !eo.isEmpty
            let cReducible := termFactReducible genv.facts c.type || (c.body.map (termFactReducible genv.facts)).getD false
            for (fr, it, cu, lo, un) in [(true, false, false, false, false), (false, true, false, false, false), (true, true, false, false, false),
                                     (false, false, false, false, true), (false, true, false, false, true), (true, true, false, false, true),
                                     (false, false, true, false, false), (true, false, true, false, false), (false, true, true, false, false),
                                     (true, true, true, false, false), (false, false, true, true, false), (true, false, true, true, false),
                                     (false, true, true, true, false), (true, true, true, true, false)] do
              if un && !cShared then continue
              -- (an R2⁺ tier with nothing to reduce is its plain counterpart, which already failed)
              if fr && !cReducible then continue
              let late := cu || lo || un
              let att := processConstant genv results c (stmt := isStmt) (inferSort := c0.bodyState == "opaque_interface") (factReduce := fr) (interp := it) (cumul := cu) (extraOwn := eo) (lower := lo) (unify := un)
              let r' ← if late then budgeted c.name "constant" att else att
              lastTier := some r'
              if r'.status == "INTERFACE_REJECTED" then iface := some r'
              if r'.accepted then
                r := r'
                break
            -- M6 last: δ-inline Set-motive constants (Prop ≤ Set at a family argument), then retry
            if !r.accepted then
              for (fr, it, cu, lo) in [(false, false, false, false), (true, true, true, true)] do
                let r' ← processConstant genv results c (stmt := isStmt) (inferSort := c0.bodyState == "opaque_interface") (factReduce := fr) (interp := it) (cumul := cu) (extraOwn := eo)
                  (lower := lo) (delta := true)
                if r'.status != "UNSUPPORTED_FEATURE" then lastTier := some r'
                if r'.status == "INTERFACE_REJECTED" then iface := some r'
                if r'.accepted then
                  r := r'
                  break
          -- δβ-inlining of erasing polymorphic definitions for constants (entry 15, last tier): the constant's
          -- type and value with those applications δβ-reduced (definitional; the audit re-derives the names
          -- and audits the row against the inlined source), when the attempts above failed
          if !r.accepted && (retry r.status) && !genv.erasingPoly.isEmpty then
            let names : Std.HashSet String := genv.erasingPoly.fold (fun acc k _ => acc.insert k) {}
            let (tyE, u1) := inlineConsts genv.erasingPoly names c.type
            let (bdE, u2) := match c.body with
              | some b => let (b', u) := inlineConsts genv.erasingPoly names b; (some b', u)
              | none => (none, {})
            let used := (u1.insertMany u2).toArray.qsort (· < ·)
            unless used.isEmpty do
              let cE := { c with type := tyE, body := bdE }
              -- (a statement's own levels are those of the inlined statement: a level that occurred only in
              -- an inlined reference's instance, e.g. `reverse_coercion@{eqtype.58}`, is no longer one; S9 audit)
              let eoE := match bdE with
                | some b => eo.filter (globalsOf b (globalsOf tyE)).contains
                | none => eo.filter (globalsOf tyE).contains
              for (it, cu, lo, un) in [(false, false, false, false), (true, false, false, false), (false, false, false, true),
                                       (true, false, false, true), (false, true, true, false), (false, true, true, true)] do
                let r' ← budgeted c.name "constant" <| processConstant genv results cE (stmt := isStmt)
                  (inferSort := c0.bodyState == "opaque_interface") (interp := it) (cumul := cu) (extraOwn := eoE) (lower := lo) (unify := un)
                if r'.status != "UNSUPPORTED_FEATURE" then lastTier := some r'
                if r'.accepted then
                  r := { r' with deltaInlined := used }
                  iface := none
                  break
          -- rule P (approved): a proposition used at a type, lifted by `PULift` (last tier; only a declaration
          -- whose value is a proposition at a declared `Type`, refused otherwise at once)
          let castFail := r.status == "TRANSLATION_FAILED" && (r.message.startsWith "default cast annotation is not convertible" ||
            r.message.startsWith "scrutinee type is not an application of")
          -- (speed, exact gate: coercions need a dependency reaching a lifted definition; a value lift needs a
          -- definition declared at a `Type`)
          let liftPossible := (c0.typeDeps ++ c0.bodyDeps).any genv.liftReach.contains || (!isStmt && irEndsInSort c0.type)
          if !r.accepted && c0.bodyState != "opaque_interface" && (retry r.status || castFail) && liftPossible then
            -- (with the ladder's variants: R2F-c, cumulativity, R3↓, per-occurrence coherence)
            for (it, cu, lo, un) in [(false, false, false, false), (true, false, false, false), (false, true, false, false),
                                     (false, false, true, false), (false, false, false, true), (true, false, false, true), (false, true, true, false)] do
              let r' ← budgeted c.name "constant" <| processConstant genv results c (stmt := isStmt) (inferSort := c0.bodyState == "opaque_interface")
                (interp := it) (cumul := cu) (extraOwn := eo) (lower := lo) (unify := un) (propLift := true)
              -- (no lift to insert, or a translation failure or exhausted budget the universe variants cannot change)
              if r'.status == "UNSUPPORTED_FEATURE" || r'.status == "TRANSLATION_FAILED" || r'.status == "RESOURCE_LIMIT" then
                if r'.status != "UNSUPPORTED_FEATURE" then lastTier := some r'
                break
              lastTier := some r'
              if r'.accepted then
                r := r'
                iface := none
                break
          -- rule P, statements (docs/PROP_LIFT.md §3.3): an unprotected statement whose codomain is a lifted type
          -- (an obligation of a proof used at `Rnat …`, `Rnat := fun_hrel …`) is stated as the proposition: the
          -- head-δ chain to the lifted definition δβ-inlined (Rocq conversion); its uses get `PULift.up`
          if !r.accepted && isStmt && c0.bodyState != "opaque_interface" && !genv.protectedNames.contains c0.name && (retry r.status) then
            if let some chain := (c.body.bind (liftChain genv.irBodies results ·)) then
              let names : Std.HashSet String := chain.foldl (·.insert ·) {}
              let (bU, _) := inlineConsts genv.irBodies names c.body.get!
              let cU := { c with body := some bU }
              for (it, cu, pl) in [(false, false, false), (true, false, false), (false, true, false), (false, false, true)] do
                let r' ← budgeted c.name "constant" <| processConstant genv results cU (stmt := true)
                  (interp := it) (cumul := cu) (extraOwn := eo) (propLift := pl)
                if r'.status != "UNSUPPORTED_FEATURE" then lastTier := some r'
                if r'.accepted then
                  r := { r' with propLiftUnfold := chain }
                  iface := none
                  break
          -- rule Q-a (docs/PHANTOM_SORT.md, approved 2026-10-15): the sort arguments of phantom checks
          -- (HB's `unify T1 T2 t1 t2 s := phantom T1 t1 → phantom T2 t2`) at the types of their values, per
          -- occurrence; levels occurring only there are no longer the declaration's (no parameter, no fact)
          if !r.accepted && (retry r.status || r.status == "INTERFACE_REJECTED") && !gone.isEmpty then
                let eoQ := eo.filter (!gone.contains ·)
                -- (with per-instance prerequisite hypotheses, P3: a proof of a phantom check, HB's `id_phant`,
                -- is a prerequisite used at a different lowered sort at each occurrence)
                -- (order from the timing data, GEL frontier: P3 587/608 successes, cu+lo 38, cu 1, it+P3 2; it, un
                -- and it+un 0/647 each — tried last, not pruned: no claim depends on the order)
                for (it, cu, lo, un, p3) in [(false, false, false, false, true), (false, true, true, false, false),
                                             (false, true, false, false, false), (true, false, false, false, true),
                                             (true, false, false, false, false), (false, false, false, true, false),
                                             (true, false, false, true, false), (false, false, true, false, true),
                                             (false, false, false, true, true)] do
                  let r' ← budgeted c.name "constant" <| processConstant genv results cQ (stmt := isStmt)
                    (inferSort := c0.bodyState == "opaque_interface") (interp := it) (cumul := cu) (extraOwn := eoQ)
                    (lower := lo) (unify := un) (hypExact := p3) (phantom := true)
                  if r'.status != "UNSUPPORTED_FEATURE" then lastTier := some r'
                  -- (speed: an exhausted budget is not changed by the next variant)
                  if r'.status == "RESOURCE_LIMIT" then break
                  if r'.accepted then
                    r := { r' with phantomLowered := gone }
                    iface := none
                    break
          -- R3G for definitions, last resort (entry 15): a failing definition is retried with the implicit levels
          -- of its references (discovery pass) as its own levels, instead of leaving those references' levels
          -- to their defaults (`refines`' relation level forced to 0 below `Set < l`; Classic `job_eqdef`'s
          -- carrier pinned to 0). Only declarations that fail without it: no accepted row, hence no dependant,
          -- changes (the reason the pass is not used in place)
          -- (not for a declaration with phantom checks: Q-a lowers those, and the constant discovery pass recursed
          -- without bound on HB's `BaseAddMagma_isAddMagma.phant_Build`, aborting a whole run — S15)
          -- (speed, entry 16: only when a failure shows the symptom it addresses, a level defaulted to 0 — no claim
          -- that existed before the tier depends on it)
          let msgs := r.message ++ ((lastTier.map (·.message)).getD "")
          let zeroDefault := (msgs.splitOn "(some 0)").length > 1 || (msgs.splitOn "argument is 0").length > 1
          if !r.accepted && !isStmt && genv.stmtMode && gone.isEmpty && zeroDefault &&
              (retry r.status || r.status == "INTERFACE_REJECTED" || r.status == "TRANSLATION_FAILED") then
            let sD ← saveState
            let dsc ← budgeted c.name "constant" <| processConstant genv results c (inferSort := c0.bodyState == "opaque_interface")
              (discover := true)
            sD.restore
            if dsc.status == "DISCOVERED" && !dsc.implicitLevels.isEmpty then
              let eoD := (eo ++ dsc.implicitLevels).toList.eraseDups.toArray
              for (it, cu, lo, p3) in [(false, false, false, false), (true, false, false, false), (false, true, true, false),
                                       (false, false, false, true)] do
                let r' ← budgeted c.name "constant" <| processConstant genv results c (inferSort := c0.bodyState == "opaque_interface")
                  (interp := it) (cumul := cu) (lower := lo) (hypExact := p3) (extraOwn := eoD)
                if r'.status != "UNSUPPORTED_FEATURE" then lastTier := some r'
                if r'.status == "RESOURCE_LIMIT" then break
                if r'.accepted then
                  r := r'
                  iface := none
                  break
          -- P3 (ITERATION_LOG entry 8): per-instance prerequisite hypotheses (no level unified across uses;
          -- duplicates collapsed after solving), when the attempts above failed
          if !r.accepted && genv.stmtMode && (retry r.status || r.status == "TRANSLATION_FAILED") then
            -- (speed, entry 14: without pending prerequisites or a fixpoint no hypothesis exists, and the first two
            -- variants are exactly earlier tiers)
            let (_, _, cPend) := blockedDeps results (c.typeDeps ++ c.bodyDeps)
            let noHyps := cPend.isEmpty && !((c.body.map termHasFix).getD false)
            for (fr, it, cu, lo) in [(false, false, false, false), (false, true, false, false), (false, false, false, true)] do
              if noHyps && !lo then continue
              let r' ← budgeted c.name "constant" <| processConstant genv results c (stmt := isStmt) (inferSort := c0.bodyState == "opaque_interface")
                (factReduce := fr) (interp := it) (cumul := cu) (extraOwn := eo) (lower := lo) (hypExact := true)
              if r'.status != "UNSUPPORTED_FEATURE" then lastTier := some r'
              if r'.accepted then
                r := r'
                iface := none
                break
          -- R2B-V last (docs/UNIVERSE_FAMILY_C.md §4): a type-valued definition declared at the sort
          -- of its value (only when every other tier failed: no accepted translation changes)
          if !r.accepted && !isStmt && genv.stmtMode && (retry r.status || r.status == "INTERFACE_REJECTED") then
            for (fr, it, cu, lo) in [(false, false, false, false), (false, true, false, false), (false, false, false, true),
                                     (false, true, false, true), (true, true, true, true)] do
              let r' ← processConstant genv results c (stmt := isStmt) (factReduce := fr) (interp := it) (cumul := cu)
                (extraOwn := eo) (lower := lo) (inheritSort := true)
              if r'.status != "UNSUPPORTED_FEATURE" then lastTier := some r'
              if r'.accepted then
                r := r'
                iface := none
                break
          -- generality first (docs/COHERENCE_READINGS.md §6): a definition accepted with an own *type*
          -- level solved by typing (R2S) under coherence by construction is retried with shared levels
          -- instantiated per occurrence; the retry is kept only when it is accepted with fewer solved type
          -- levels (the same checks: it is at least as general)
          if r.accepted && !isStmt && genv.stmtMode then
            let tyLv := globalsOf c.type
            let solvedTy (x : DeclResult) := (x.bodyLevels.filter fun (m, _) => tyLv.contains m).size
            let gDep := depGlobalLevels genv (c.typeDeps ++ c.bodyDeps)
            if solvedTy r > 0 && (r.bodyLevels.any fun (m, _) => gDep.contains m) then
              let sAcc ← saveState
              let mut better := false
              for it in [false, true] do
                sBefore.restore
                let r' ← processConstant genv results c (stmt := isStmt) (inferSort := c0.bodyState == "opaque_interface")
                  (interp := it) (extraOwn := eo) (unify := true)
                if r'.accepted && solvedTy r' < solvedTy r && r'.levelDefaults ≤ r.levelDefaults then
                  r := { r' with levelDiagnostics := r'.levelDiagnostics.push s!"generality: {solvedTy r} solved type level(s) reduced to {solvedTy r'} (shared levels per occurrence)" }
                  better := true
                  break
              unless better do sAcc.restore
          if r.accepted then break
        -- a declaration that no attempt accepts keeps the diagnosis of the plain attempt without
        -- implicit levels (the earlier behaviour)
        if !r.accepted then
          r := first.getD r
          -- the last tier's diagnosis (R2⁺ + R2F-c + cumulativity + R3↓ with the bounded solver) is
          -- appended, with its solver log
          if let some lt := lastTier then
            let slog := lt.levelDiagnostics.filter (·.startsWith "solver:")
            r := { r with message := s!"{r.message} [last tier: {lt.status}: {lt.message.take 600}{if slog.isEmpty then "" else s!" {slog}"}]" }
          -- the refusal is the reason when a tier was refused only for interface protection
          if let some i := iface then
            r := { i with message := s!"{i.message} [plain attempt: {r.status}: {r.message.take 400}]" }
        if isStmt then
          let st := if r.status == "TRANSLATED_AND_CHECKED" then "STATEMENT_KERNEL_CHECKED"
            else if r.status == "PENDING_KERNEL_CHECKED" then "STATEMENT_PENDING_KERNEL_CHECKED" else r.status
          r := { r with source := c0.name, status := st,
                        targetKind := if st != r.status then "statement" else r.targetKind }
        -- B: generated statements (termination obligations, unfolding equations) are proof tasks
        for x in r.synthetic do
          if let some n := x.target then
            if x.status == "STATEMENT_KERNEL_CHECKED" || x.status == "STATEMENT_PENDING_KERNEL_CHECKED" then
              genv := { genv with leafStmt := genv.leafStmt.insert x.source (n, x.pendingHyps),
                                  leafStmtTargets := genv.leafStmtTargets.insert n }
              unless x.levelParams.isEmpty do
                genv := { genv with constGlobals := genv.constGlobals.insert n x.paramLevels }
        -- statement mode: register proof tasks (statements) and pending artifacts for later references
        if r.status == "STATEMENT_KERNEL_CHECKED" || r.status == "STATEMENT_PENDING_KERNEL_CHECKED" || r.status == "PENDING_KERNEL_CHECKED" then
          if let some n := r.target then
            if r.status == "PENDING_KERNEL_CHECKED" then
              genv := { genv with pendingDefs := genv.pendingDefs.insert c0.name (n, r.pendingHyps) }
            else
              genv := { genv with leafStmt := genv.leafStmt.insert c0.name (n, r.pendingHyps),
                                  leafStmtTargets := genv.leafStmtTargets.insert n }
            unless r.levelParams.isEmpty do
              genv := { genv with constGlobals := genv.constGlobals.insert n r.paramLevels }
        if r.ok then if let some n := r.target then
          genv := { genv with consts := genv.consts.insert c.name n,
                              constLevels := genv.constLevels.insert c.name r.levelParams.length,
                              constGlobals := if r.levelParams.isEmpty then genv.constGlobals
                                else genv.constGlobals.insert n r.paramLevels }
          if r.polyParams > 0 then
            genv := { genv with constPoly := genv.constPoly.insert c.name r.polyParams,
                                polyByTarget := genv.polyByTarget.insert n r.polyParams }
          unless r.admittingLevels.isEmpty do
            genv := { genv with admitting := genv.admitting.insert n r.admittingLevels }
        pure r
      | .inductive i =>
        -- R3G for blocks: first with free reference levels as implicit parameters (more general); if
        -- the kernel rejects that (an implicit level in a field may exceed the block's sort), the
        -- R3″ translation (free reference levels at 0) as before
        -- M6: each attempt first with plain universe parameters (more general: the R2F interpretation
        -- also bakes in facts that only uses elsewhere impose, e.g. Ring_theory.ring_morph's
        -- C ≥ R from IDmorph), then with the R2F interpretation
        let ladder (i : IR.InductiveDecl) : MetaM (DeclResult × Option IndTarget) := do
          let run1 (eo : Array String) (lower : Bool) (rs : Array String := #[]) : MetaM (DeclResult × Option IndTarget) := do
            -- (per-occurrence attempts only when some level of the block is a referenced declaration's: its own
            -- levels against the dependencies' generalized levels, or implicit levels, which are such by definition)
            let depLv := depGlobalLevels genv i.typeDeps
            let shared := !eo.isEmpty || (globalsOfInd i).any depLv.contains
            -- (R3↓ tier: shared levels per occurrence first — lowered where typing lowers them, otherwise the
            -- own level — then fresh and defaulted, as before)
            if lower && shared then
              for pl in [true, false] do
                let (u, tu) ← processInductive genv results i src.rawDecls[i.name]! (extraOwn := eo) (lower := true) (plain := pl) (rsOwn := rs) (unify := true)
                if u.accepted then return (u, tu)
            let (a, ta) ← processInductive genv results i src.rawDecls[i.name]! (extraOwn := eo) (lower := lower) (plain := true) (rsOwn := rs)
            if a.accepted then return (a, ta)
            -- coherence by unification (docs/COHERENCE_READINGS.md §6) before the R2F interpretation, as plain
            -- parameters are (M6): the plain attempt with shared levels instantiated per occurrence
            if !lower && shared && (a.status == "KERNEL_REJECTED" || a.status == "UNIVERSE_REJECTED") then
              let (u, tu) ← processInductive genv results i src.rawDecls[i.name]! (extraOwn := eo) (plain := true) (rsOwn := rs) (unify := true)
              if u.accepted then return (u, tu)
            let (b, tb) ← processInductive genv results i src.rawDecls[i.name]! (extraOwn := eo) (lower := lower) (rsOwn := rs)
            if b.accepted || lower || !shared || !(b.status == "KERNEL_REJECTED" || b.status == "UNIVERSE_REJECTED") then return (b, tb)
            let (u, tu) ← processInductive genv results i src.rawDecls[i.name]! (extraOwn := eo) (rsOwn := rs) (unify := true)
            if u.accepted then return (u, tu)
            return (b, tb)
          -- (speed, entry 14: discovery only when a dependency has generalized levels — otherwise no reference
          -- level can be free; per-occurrence attempts only when the block shares a level with a reference)
          let depLv := depGlobalLevels genv i.typeDeps
          let shared := (globalsOfInd i).any depLv.contains
          let noDisc : DeclResult := { source := i.name, kind := "inductive", status := "DISCOVERED" }
          let (d0, _) ← if depLv.isEmpty then pure (noDisc, none) else processInductive genv results i src.rawDecls[i.name]! (discover := true)
          let attempt (d : DeclResult) : MetaM (DeclResult × Option IndTarget) := do
            let (r, t?) ← do
              if d.status == "DISCOVERED" && !d.implicitLevels.isEmpty then
                let (r1, t1) ← run1 d.implicitLevels false d.resultSortImplicit
                if r1.accepted then pure (r1, t1) else
                -- (R3G for fields refused by the kernel: the levels found in the arity and by R3G-F, as before)
                let (r1, t1) ← if d.fieldImplicit.isEmpty then pure (r1, t1) else
                  let ex := d.implicitLevels.filter (!d.fieldImplicit.contains ·)
                  if ex.isEmpty then run1 #[] false else run1 ex false d.resultSortImplicit
                if r1.accepted then pure (r1, t1) else
                -- (R3G-F levels refused by the kernel: the arity's implicit levels alone, as before)
                let old := d.implicitLevels.filter (!d.resultSortImplicit.contains ·)
                if !d.resultSortImplicit.isEmpty && !old.isEmpty then
                  let (r2, t2) ← run1 old false
                  if r2.accepted then pure (r2, t2) else run1 #[] false
                else run1 #[] false
              else run1 #[] false
            -- R3↓ last (reported): references in the block instantiated below its shared levels
            if r.accepted || !(r.status == "KERNEL_REJECTED" || r.status == "UNIVERSE_REJECTED") then return (r, t?)
            -- (with the discovered implicit levels first: per occurrence, a lowered field keeps them; entry 13)
            let (r2, t2) ← if d.status == "DISCOVERED" && !d.implicitLevels.isEmpty then do
                let (a, ta) ← run1 d.implicitLevels true d.resultSortImplicit
                if a.accepted then pure (a, ta) else run1 #[] true
              else run1 #[] true
            if r2.accepted then pure (r2, t2) else pure ({ r with message := s!"{r.message} [R3↓ attempt: {r2.status}: {r2.message}]" }, t?)
          let (r, t?) ← attempt d0
          -- per-occurrence discovery (entry 14), only when the plain attempts failed on a block that shares a
          -- level with a reference: classes that coherence by construction identifies with an own level (a
          -- lower carrier under `Equality.sort`) can then be named
          if r.accepted || !shared || d0.status != "DISCOVERED" ||
              !(r.status == "KERNEL_REJECTED" || r.status == "UNIVERSE_REJECTED") then return (r, t?)
          let (du, _) ← processInductive genv results i src.rawDecls[i.name]! (discover := true) (unify := true)
          let extra := du.implicitLevels.filter (!d0.implicitLevels.contains ·)
          if du.status != "DISCOVERED" || extra.isEmpty then return (r, t?)
          let d := { d0 with implicitLevels := (d0.implicitLevels ++ extra).qsort (· < ·),
                             fieldImplicit := (d0.fieldImplicit ++ extra.filter du.fieldImplicit.contains).qsort (· < ·) }
          let (r2, t2) ← attempt d
          if r2.accepted then return (r2, t2)
          return (r, t?)
        let (r, t?) ← ladder i
        -- δ-inlining of erasing polymorphic definitions (entry 14, last tier): the whole ladder on the
        -- block with those applications δβ-reduced (definitional; the audit re-derives both the names
        -- and the inlined source), when every attempt on the source block failed
        let (r, t?) ← if r.accepted || genv.erasingPoly.isEmpty ||
            !(r.status == "KERNEL_REJECTED" || r.status == "UNIVERSE_REJECTED") then pure (r, t?) else do
          let names : Std.HashSet String := genv.erasingPoly.fold (fun acc k _ => acc.insert k) {}
          let bodies := genv.erasingPoly
          let inl (t : IR.Term) (used : Std.HashSet String) : IR.Term × Std.HashSet String :=
            let (t', u) := inlineConsts bodies names t
            (t', used.insertMany u)
          let mut used : Std.HashSet String := {}
          let mut params := #[]
          for p in i.params do
            let (t, u) := inl p.type used
            used := u
            params := params.push { p with type := t }
          let mut bodies' := #[]
          for b in i.bodies do
            let (ty, u) := inl b.type used
            used := u
            let mut ctors := #[]
            for c in b.ctors do
              let (cty, u) := inl c.type used
              used := u
              let mut args := #[]
              for a in c.args do
                let (at', u) := inl a.type used
                used := u
                args := args.push { a with type := at' }
              ctors := ctors.push { c with type := cty, args }
            -- (primitive records: the projections' types, as the audit inlines them)
            let mut projs := #[]
            for (pn, pr, pt) in b.projs do
              let (pt', u) := inl pt used
              used := u
              projs := projs.push (pn, pr, pt')
            bodies' := bodies'.push { b with type := ty, ctors, projs }
          if used.isEmpty then pure (r, t?) else
          let (r2, t2) ← ladder { i with params, bodies := bodies' }
          let usedA := used.toArray.qsort (· < ·)
          if r2.accepted then pure ({ r2 with deltaInlined := usedA }, t2)
          else pure ({ r with message := s!"{r.message} [δ-inlined {usedA}: {r2.status}: {r2.message.take 400}]" }, t?)
        if let some t := t? then genv := { genv with inds := genv.inds.insert i.name t }
        -- Non-template inductives with generalized global levels: references obey R3 like
        -- generalized constants (the type and its constructors carry the same parameters).
        if (r.ok || r.status == "PENDING_KERNEL_CHECKED") && !r.levelParams.isEmpty then
          if let some tn := r.target then
            for n in #[tn] ++ r.targetCtors.map (·.1) do
              genv := { genv with constGlobals := genv.constGlobals.insert n r.paramLevels }
            -- R3G-F: the type's result-sort-only levels (source) and its own R3G-F levels
            if !r.isTemplate then
              let ro := Split.resultOnlyLevels i ++ r.resultSortImplicit
              unless ro.isEmpty do genv := { genv with resultOnly := genv.resultOnly.insert tn ro }

            for (l, _) in r.templateParams do
              genv := { genv with templateLevels := genv.templateLevels.insert l }
        pure r
    -- R-CARRIER P2: the copy positions of the declaration's universe parameters, for references to it
    unless r.levelCopies.isEmpty do
      let copies := r.levelCopies.foldl (· ++ ·.2) #[]
      let mask := (r.levelParams.drop r.polyParams).toArray.map fun p => copies.any (levelParamName · == p)
      for n in (r.target.toList ++ (r.targetCtors.map (·.1)).toList) do
        genv := { genv with copyPositions := genv.copyPositions.insert n mask }
    -- R3G-F: the declaration's closure of result-sort implicit levels (its dependencies' and its own)
    let deps := match d with
      | .constant c => c.typeDeps ++ c.bodyDeps
      | .inductive i => i.typeDeps
    -- rule P gate: the declaration reaches a lifted definition
    if r.propLift.isSome || deps.any genv.liftReach.contains then
      genv := { genv with liftReach := genv.liftReach.insert d.name,
                          liftTargets := (r.target.toList ++ (r.targetCtors.map (·.1)).toList).foldl (fun s n => s.insert n)
                            (genv.liftTargets.insert ``PULift) }
    let cl := r.resultSortImplicit.foldl (·.insert ·) (genv.rsOfDeps deps)
    unless cl.isEmpty do genv := { genv with rsClosure := genv.rsClosure.insert d.name cl }
    -- R3G-F applicability at references to this declaration (docs/RESULT_SORT_LEVELS.md §2): besides an
    -- inductive's source result-sort-only levels (registered above), the R3G-F levels of its dependency
    -- closure that are not levels of its own source (they reach it only through such blocks)
    if r.accepted || r.status == "STATEMENT_KERNEL_CHECKED" || r.status == "STATEMENT_PENDING_KERNEL_CHECKED" then
      let expl : Std.HashSet String := match d with
        | .constant c => globalsOf (c.body.getD (.sort .prop)) (globalsOf c.type)
        | .inductive i => (globalsOfInd i).foldl (·.insert ·) {}
      let inh := (genv.rsOfDeps deps).fold (fun acc l => if expl.contains l then acc else acc.push l) #[]
      unless inh.isEmpty do
        for n in (r.target.toList ++ (r.targetCtors.map (·.1)).toList) do
          let old := (genv.resultOnly[n]?).getD #[]
          genv := { genv with resultOnly := genv.resultOnly.insert n (old ++ inh.filter (!old.contains ·)) }
    return (r, genv)

end Rocq2Lean

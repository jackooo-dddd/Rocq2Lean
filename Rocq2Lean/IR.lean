import Lean.Data.Json

/-!
# Source IR (`rocq2lean-ir/0.2`)

A faithful in-memory copy of the NDJSON written by `rocq/exporter` (see `docs/IR_SPEC.md`).
Nothing is normalized here: the parser is strict and rejects unknown tags, so a schema
mismatch can never be silently dropped.
-/

namespace Rocq2Lean.IR

open Lean

inductive Level where
  | set
  | global (name : String)
  | var (idx : Nat)
  deriving Repr, BEq, Inhabited

/-- One summand `l + n` of an algebraic universe `max(l₁+n₁, …)`. -/
structure LevelExpr where
  level : Level
  offset : Nat
  deriving Repr, BEq, Inhabited

inductive SortIR where
  | prop
  | sprop
  | type (u : Array LevelExpr)
  deriving Repr, BEq, Inhabited

inductive Relevance where
  | relevant
  | irrelevant
  deriving Repr, BEq, Inhabited

structure AName where
  name : Option String
  rel : Relevance
  deriving Repr, BEq, Inhabited

structure IndRef where
  mind : String
  idx : Nat
  deriving Repr, BEq, Inhabited

inductive Term where
  | rel (i : Nat)
  | var (id : String)
  | evar (ev : Nat) (args : Array Term)
  | sort (s : SortIR)
  | cast (t : Term) (kind : String) (ty : Term)
  | prod (n : AName) (ty body : Term)
  | lam (n : AName) (ty body : Term)
  | letIn (n : AName) (val ty body : Term)
  | app (f : Term) (args : Array Term)
  | const (c : String) (u : Array Level)
  | ind (i : IndRef) (u : Array Level)
  | construct (i : IndRef) (ctor : Nat) (u : Array Level)
  /-- MetaRocq compact case: `pctx`/branch contexts carry names only. -/
  | case (ind : IndRef) (npar : Nat) (rel : Relevance) (puinst : Array Level)
      (pparams : Array Term) (pctx : Array AName) (pret : Term)
      (scrut : Term) (brs : Array (Array AName × Term))
  | proj (ind : IndRef) (npars arg : Nat) (t : Term)
  /-- `defs[k] = (name, type, body, rarg)`; bodies live under `defs.size` extra binders. -/
  | fix (defs : Array (AName × Term × Term × Nat)) (idx : Nat)
  | cofix (defs : Array (AName × Term × Term × Nat)) (idx : Nat)
  /-- Primitive literal (`int`, `float`, `string`, `array`), kept verbatim. -/
  | prim (kind : String) (raw : Json)
  deriving Inhabited

/-- A context declaration; contexts are stored innermost-first, as in MetaRocq. -/
structure CtxDecl where
  name : AName
  body : Option Term
  type : Term
  deriving Inhabited

inductive UDecl where
  | monomorphic
  | polymorphic (names : Array (Option String)) (constraints : Json)
  deriving Inhabited

structure ConstantDecl where
  name : String
  type : Term
  body : Option Term
  /-- `transparent`, `opaque_present`, `assumption`, `unavailable`, `unsupported_primitive`. -/
  bodyState : String
  universes : UDecl
  typeDeps : Array String
  bodyDeps : Array String
  native : Json
  deriving Inhabited

structure CtorBody where
  name : String
  args : Array CtxDecl
  indices : Array Term
  type : Term
  arity : Nat
  deriving Inhabited

structure OneInd where
  name : String
  indices : Array CtxDecl
  sort : SortIR
  type : Term
  kelim : String
  ctors : Array CtorBody
  projs : Array (String × Relevance × Term)
  rel : Relevance
  deriving Inhabited

structure InductiveDecl where
  name : String
  finite : String
  npars : Nat
  params : Array CtxDecl
  bodies : Array OneInd
  universes : UDecl
  variance : Option (Array String)
  typeDeps : Array String
  native : Json
  deriving Inhabited

inductive Decl where
  | constant (c : ConstantDecl)
  | inductive (i : InductiveDecl)
  deriving Inhabited

def Decl.name : Decl → String
  | .constant c => c.name
  | .inductive i => i.name

/-- A source universe constraint `l rel r` as quoted by MetaRocq: `kind = "le"` with an
offset (`l + offset ≤ r`; offset 1 means `l < r`) or `kind = "eq"`. -/
structure UConstraint where
  l : Level
  kind : String
  offset : Int
  r : Level
  deriving Inhabited, Repr

/-- Native universe facts: the exact relation (`lt`, `le`, or none) between every pair of levels
of the export (and `Set`), computed from Rocq's universe graph by the exporter. -/
structure UniverseFacts where
  levels : Array String
  relations : Array (String × String × String)
  /-- P0 resource accounting: `(a, b) ↦ relation`, and the strict successors of each level, built
  once per export (`UniverseFacts.indexed`). A query no longer scans the request-sized relation
  table, so a declaration's cost (its heartbeat budget) does not grow with the size of the request. -/
  index : Std.HashMap (String × String) String := {}
  ltSucc : Std.HashMap String (Array String) := {}
  deriving Inhabited

def UniverseFacts.indexed (levels : Array String) (relations : Array (String × String × String)) : UniverseFacts :=
  let index := relations.foldl (init := ({} : Std.HashMap (String × String) String)) fun m (a, r, b) => m.insert (a, b) r
  let ltSucc := relations.foldl (init := ({} : Std.HashMap String (Array String))) fun m (a, r, b) =>
    if r == "lt" then m.insert a ((m.getD a #[]).push b) else m
  { levels, relations, index, ltSucc }

/-- New levels with the given relations added to an indexed fact table (R-SPLIT copies). -/
def UniverseFacts.extend (f : UniverseFacts) (levels : Array String) (relations : Array (String × String × String)) : UniverseFacts :=
  let index := relations.foldl (init := f.index) fun m (a, r, b) => m.insert (a, b) r
  let ltSucc := relations.foldl (init := f.ltSucc) fun m (a, r, b) =>
    if r == "lt" then m.insert a ((m.getD a #[]).push b) else m
  { levels := f.levels ++ levels, relations := f.relations ++ relations, index, ltSucc }

def UniverseFacts.rel (f : UniverseFacts) (a b : String) : String :=
  if a == b then "eq" else
  if f.index.isEmpty then
    match f.relations.find? (fun (x, _, y) => x == a && y == b) with
    | some (_, r, _) => r
    | none => "none"
  else f.index.getD (a, b) "none"

structure Root where
  requested : String
  name : String
  deriving Inhabited

structure Source where
  header : Json
  roots : Array Root
  libraries : Array (String × Option String)
  decls : Array Decl
  universeLevels : Array Level
  universeConstraints : Array UConstraint
  facts : UniverseFacts
  /-- Raw JSON line of each declaration, by name (for provenance and re-checking). -/
  rawDecls : Std.HashMap String Json
  deriving Inhabited

/-! ## Parsing -/

abbrev P := Except String

private def field (j : Json) (k : String) : P Json :=
  match j.getObjVal? k with
  | .ok v => pure v
  | .error _ => throw s!"missing field '{k}' in {j.compress.take 200}"

private def str (j : Json) (k : String) : P String := do (← field j k).getStr?
private def nat (j : Json) (k : String) : P Nat := do (← field j k).getNat?
private def arr (j : Json) (k : String) : P (Array Json) := do (← field j k).getArr?

def parseLevel (j : Json) : P Level := do
  match ← str j "k" with
  | "set" => pure .set
  | "global" => return .global (← str j "n")
  | "var" => return .var (← nat j "i")
  | k => throw s!"unknown level tag '{k}'"

def parseSort (j : Json) : P SortIR := do
  match ← str j "k" with
  | "prop" => pure .prop
  | "sprop" => pure .sprop
  | "type" =>
    let es ← (← arr j "u").mapM fun e => do
      return { level := ← parseLevel (← field e "l"), offset := ← nat e "n" : LevelExpr }
    return .type es
  | k => throw s!"unknown sort tag '{k}'"

def parseRel (j : Json) : P Relevance := do
  match ← j.getStr? with
  | "R" => pure .relevant
  | "I" => pure .irrelevant
  | r => throw s!"unknown relevance '{r}'"

def parseAName (j : Json) : P AName := do
  let n ← field j "n"
  let name ← match n with
    | .null => pure none
    | v => some <$> v.getStr?
  return { name, rel := ← parseRel (← field j "r") }

def parseInd (j : Json) : P IndRef := return { mind := ← str j "mind", idx := ← nat j "i" }

def parseInstance (j : Json) : P (Array Level) := do (← j.getArr?).mapM parseLevel

partial def parseTerm (j : Json) : P Term := do
  match ← str j "k" with
  | "rel" => return .rel (← nat j "i")
  | "var" => return .var (← str j "id")
  | "evar" => return .evar (← nat j "ev") (← (← arr j "args").mapM parseTerm)
  | "sort" => return .sort (← parseSort (← field j "s"))
  | "cast" => return .cast (← parseTerm (← field j "t")) (← str j "kind") (← parseTerm (← field j "ty"))
  | "prod" =>
    return .prod (← parseAName (← field j "n")) (← parseTerm (← field j "ty")) (← parseTerm (← field j "b"))
  | "lam" =>
    return .lam (← parseAName (← field j "n")) (← parseTerm (← field j "ty")) (← parseTerm (← field j "b"))
  | "let" =>
    return .letIn (← parseAName (← field j "n")) (← parseTerm (← field j "v"))
      (← parseTerm (← field j "ty")) (← parseTerm (← field j "b"))
  | "app" => return .app (← parseTerm (← field j "f")) (← (← arr j "args").mapM parseTerm)
  | "const" => return .const (← str j "c") (← parseInstance (← field j "u"))
  | "ind" => return .ind (← parseInd (← field j "ind")) (← parseInstance (← field j "u"))
  | "construct" =>
    return .construct (← parseInd (← field j "ind")) (← nat j "c") (← parseInstance (← field j "u"))
  | "case" =>
    let ci ← field j "ci"
    let p ← field j "p"
    let brs ← (← arr j "brs").mapM fun b => do
      return ((← (← arr b "ctx").mapM parseAName), ← parseTerm (← field b "body"))
    return .case (← parseInd (← field ci "ind")) (← nat ci "npar") (← parseRel (← field ci "r"))
      (← parseInstance (← field p "u")) (← (← arr p "params").mapM parseTerm)
      (← (← arr p "ctx").mapM parseAName) (← parseTerm (← field p "ret"))
      (← parseTerm (← field j "c")) brs
  | "proj" =>
    let p ← field j "p"
    return .proj (← parseInd (← field p "ind")) (← nat p "npars") (← nat p "arg") (← parseTerm (← field j "t"))
  | "fix" => return .fix (← parseDefs j) (← nat j "idx")
  | "cofix" => return .cofix (← parseDefs j) (← nat j "idx")
  | "int" => return .prim "int" j
  | "float" => return .prim "float" j
  | "string" => return .prim "string" j
  | "array" => return .prim "array" j
  | k => throw s!"unknown term tag '{k}'"
where
  parseDefs (j : Json) : P (Array (AName × Term × Term × Nat)) := do
    (← arr j "defs").mapM fun d => do
      return ((← parseAName (← field d "n")), (← parseTerm (← field d "ty")),
        (← parseTerm (← field d "body")), (← nat d "rarg"))

def parseCtx (j : Json) : P (Array CtxDecl) := do
  (← j.getArr?).mapM fun d => do
    let body ← match ← field d "body" with
      | .null => pure none
      | b => some <$> parseTerm b
    return { name := ← parseAName (← field d "n"), body, type := ← parseTerm (← field d "ty") }

def parseUDecl (j : Json) : P UDecl := do
  match ← str j "k" with
  | "monomorphic" => pure .monomorphic
  | "polymorphic" =>
    let names ← (← arr j "names").mapM fun n => match n with
      | .null => pure none
      | v => some <$> v.getStr?
    return .polymorphic names (← field j "constraints")
  | k => throw s!"unknown universe declaration tag '{k}'"

private def strArr (j : Json) : P (Array String) := do (← j.getArr?).mapM (·.getStr?)

def parseDecl (j : Json) : P Decl := do
  match ← str j "kind" with
  | "constant" =>
    let body ← match ← field j "body" with
      | .null => pure none
      | b => some <$> parseTerm b
    let deps ← field j "deps"
    return .constant {
      name := ← str j "name", type := ← parseTerm (← field j "type"), body,
      bodyState := ← str j "body_state", universes := ← parseUDecl (← field j "universes"),
      typeDeps := ← strArr (← field deps "type"), bodyDeps := ← strArr (← field deps "body"),
      native := ← field j "native" }
  | "inductive" =>
    let bodies ← (← arr j "bodies").mapM fun b => do
      let ctors ← (← arr b "ctors").mapM fun c => do
        return { name := ← str c "name", args := ← parseCtx (← field c "args"),
                 indices := ← (← arr c "indices").mapM parseTerm, type := ← parseTerm (← field c "type"),
                 arity := ← nat c "arity" : CtorBody }
      let projs ← (← arr b "projs").mapM fun p => do
        return ((← str p "name"), (← parseRel (← field p "r")), (← parseTerm (← field p "type")))
      return { name := ← str b "name", indices := ← parseCtx (← field b "indices"),
               sort := ← parseSort (← field b "sort"), type := ← parseTerm (← field b "type"),
               kelim := ← str b "kelim", ctors, projs, rel := ← parseRel (← field b "r") : OneInd }
    let variance ← match ← field j "variance" with
      | .null => pure none
      | v => some <$> strArr v
    return .inductive {
      name := ← str j "name", finite := ← str j "finite", npars := ← nat j "npars",
      params := ← parseCtx (← field j "params"), bodies, universes := ← parseUDecl (← field j "universes"),
      variance, typeDeps := ← strArr (← field (← field j "deps") "type"), native := ← field j "native" }
  | k => throw s!"not a declaration line: kind '{k}'"

/-- Parse a whole NDJSON export. The line layout is fixed: header, roots, libraries, universes,
universe_facts, declarations…, footer (whose count must match). -/
def parseSource (contents : String) : P Source := do
  let lines := (contents.splitOn "\n").filter (· ≠ "") |>.toArray
  let js ← lines.mapM Json.parse
  unless js.size ≥ 6 do throw "truncated export: fewer than 6 lines"
  let header := js[0]!
  unless (← str header "kind") == "header" && (← str header "ir") == "rocq2lean-ir/0.2" do
    throw "first line is not a rocq2lean-ir/0.2 header"
  unless (← str js[1]! "kind") == "roots" do throw "second line is not the roots record"
  unless (← str js[2]! "kind") == "libraries" do throw "third line is not the libraries record"
  unless (← str js[3]! "kind") == "universes" do throw "fourth line is not the universes record"
  unless (← str js[4]! "kind") == "universe_facts" do throw "fifth line is not the universe facts record"
  let universeLevels ← (← arr js[3]! "levels").mapM parseLevel
  let universeConstraints ← (← arr js[3]! "constraints").mapM fun c => do
    let rel ← field c "rel"
    let kind ← str rel "k"
    let offset : Int ← if kind == "le" then (← field rel "offset").getInt? else pure 0
    unless kind == "le" || kind == "eq" do throw s!"unknown constraint kind {kind}"
    return { l := ← parseLevel (← field c "l"), kind, offset, r := ← parseLevel (← field c "r") : UConstraint }
  let fj := js[4]!
  let facts : UniverseFacts := UniverseFacts.indexed
    (← (← arr fj "levels").mapM (·.getStr?))
    (← (← arr fj "relations").mapM fun x => do
      let r ← str x "rel"
      unless r == "lt" || r == "le" do throw s!"unknown universe relation {r}"
      return ((← str x "l"), r, (← str x "r")))
  let footer := js[js.size - 1]!
  unless (← str footer "kind") == "footer" do throw "missing footer (export incomplete?)"
  let roots ← (← arr js[1]! "roots").mapM fun r => do
    return { requested := ← str r "requested", name := ← str r "name" : Root }
  let libraries ← (← arr js[2]! "libraries").mapM fun l => do
    let vo ← match ← field l "vo" with
      | .null => pure none
      | v => some <$> v.getStr?
    return ((← str l "dirpath"), vo)
  let declJs := js.extract 5 (js.size - 1)
  unless declJs.size == (← nat footer "declarations") do
    throw s!"footer announces {← nat footer "declarations"} declarations, found {declJs.size}"
  let decls ← declJs.mapM parseDecl
  let mut raw : Std.HashMap String Json := {}
  for d in decls, j in declJs do
    if raw.contains d.name then throw s!"duplicate declaration {d.name}"
    raw := raw.insert d.name j
  return { header, roots, libraries, decls, universeLevels, universeConstraints, facts, rawDecls := raw }

end Rocq2Lean.IR

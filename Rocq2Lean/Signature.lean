import Lean.Data.Json

/-!
# Canonical source signatures

A bootstrap mapping is keyed on the exact *shape* of the source inductive: its kind, name,
parameters, bodies (indices, sort, constructors with their argument contexts, indices and
types, projections, eliminations), universes, variance and template/polymorphic/private status.
Names of global universe levels are erased (`"*"`), since Rocq numbers them per library; the
typing flags are audited separately.
-/

namespace Rocq2Lean

open Lean

private def eraseGlobalLevelNames (s : String) : String := Id.run do
  let marker := "\"k\":\"global\",\"n\":\""
  let parts := s.splitOn marker
  let mut out := parts[0]!
  for p in parts.drop 1 do
    -- drop the level name up to its closing quote
    let rest := (p.dropWhile (· != '"')).toString
    out := out ++ marker ++ "*" ++ rest
  return out

/-- Canonical signature of a raw inductive declaration line. -/
def canonicalSignature (raw : Json) : String :=
  let pick (k : String) : Json := (raw.getObjVal? k).toOption.getD .null
  let native := pick "native"
  let nat (k : String) : Json := (native.getObjVal? k).toOption.getD .null
  let j := Json.mkObj [
    ("kind", pick "kind"), ("name", pick "name"), ("finite", pick "finite"), ("npars", pick "npars"),
    ("params", pick "params"), ("bodies", pick "bodies"), ("universes", pick "universes"),
    ("variance", pick "variance"), ("polymorphic", nat "polymorphic"), ("template", nat "template"),
    ("private", nat "private")]
  eraseGlobalLevelNames j.compress

end Rocq2Lean

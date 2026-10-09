# Source IR — `rocq2lean-ir/0.1`

NDJSON, one JSON object per line, written by `rocq/exporter` (`Rocq2Lean Export "file" roots…`).
It is a field-by-field serialization of MetaRocq Template quotations
(`Ast_quoter.quote_term_rec ~bypass:true`); **no normalization is applied**. Parsed strictly by
`Rocq2Lean/IR.lean` (unknown tags are errors).

## Line layout (fixed order)

| # | `kind` | Content |
|---|---|---|
| 1 | `header` | `ir`, `frontend` (name, MetaRocq commit, quoter, opaque access), `rocq_version`, `ocaml_version`, `global_typing_flags`, `conventions` |
| 2 | `roots` | `[{requested, name, term}]` — the qualid as written and its quoted head |
| 3 | `libraries` | `[{dirpath, vo}]` — compiled libraries the declarations come from |
| 4 | `universes` | union of the quoted environments' `levels` and `constraints` |
| 5… | `constant` / `inductive` | declarations, **dependencies before dependents** |
| last | `footer` | `declarations`: count (an incomplete export is rejected) |

## Conventions

* **Bound variables.** `{"k":"rel","i":n}` is MetaRocq `tRel n`: `0` = innermost binder.
  This equals Lean `Expr.bvar n`. (Raw kernel `Rel 1` = IR `rel 0`; the exporter never sees
  raw `Rel`.) Confirmed by the Phase 0 probe: `fun x y => x` ↦ `rel 1`.
* **Contexts** (`params`, `indices`, `args`) are arrays **innermost-first** (MetaRocq snoc order).
* **Constructor indices** are 0-based; **inductive bodies** `i` are 0-based within the block.
  In constructor types the block's inductives are bound as `rel`s: body `k` of `n` is
  `rel (n - 1 - k + depth)`.
* **Dirpaths** in `mp` are outer-first.
* **Keys.** A global name is the string `M.ident` where `M` is the file dirpath joined by `.`,
  followed by `/field` for each module field. Identifiers contain neither `.` nor `/`, so keys
  are unambiguous. Lean names are `Rocq.` + all components.
* **Case** is MetaRocq's compact form: `p.ctx` and branch `ctx` carry binder names only; types
  are recovered from the inductive declaration (as MetaRocq's `case_branch_context`).
* **Fix**: `defs[k] = {n, ty, body, rarg}`; bodies are under `defs.size` extra binders;
  `rarg` is the 0-based decreasing argument, taken from the source metadata.

## Terms

`rel i` · `var id` · `evar ev args` · `sort s` · `cast t kind ty` (`kind` ∈ vm/native/default) ·
`prod n ty b` · `lam n ty b` · `let n v ty b` · `app f args` · `const c u` · `ind ind u` ·
`construct ind c u` · `case ci p c brs` · `proj p t` · `fix defs idx` · `cofix defs idx` ·
`int v` · `float v` · `string v` · `array u elems default ty`.

Binder annotation `n = {n: name|null, r: "R"|"I"}`. Sorts: `prop`, `sprop`,
`type u` with `u = [{l, n}]` meaning `max(l₁+n₁, …)`; levels `set`, `global n`, `var i`.

## Declarations

`constant`: `name, mp, id, type, body|null, body_state, universes, relevance, deps{type,body},
native{body_kind, polymorphic, typing_flags}`.

`body_state` is one of — and these are never interchangeable:

| state | meaning |
|---|---|
| `transparent` | transparent definition, body present |
| `opaque_present` | opaque (`Qed`) constant, body read through `opaque_access` |
| `assumption` | genuine source assumption (`Axiom`/`Parameter`) |
| `unavailable` | body expected but absent |
| `unsupported_primitive` | primitive operation or symbol |

`inductive`: `name` (key of the block = first body), `finite`, `npars`, `params`, `bodies[{name,
indices, sort, type, kelim, ctors[{name, args, indices, type, arity}], projs, r}]`, `universes`,
`variance`, `deps{type}`, `native{polymorphic, template, private, typing_flags}`.

`deps` are computed from the quoted terms (constants, inductives, constructors, case and
projection metadata), self-references removed.

## Hashes

`source_snapshot.json` (written by `rocq2lean export`) records sha256 of the manifest, every
compiled source `.v`, every library `.vo`, the IR file, the exporter plugin and the toolchain
lock. Source hashes and the IR hash are kept separate; `verify` recomputes all of them.

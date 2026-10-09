# References (pinned)

Only what this project actually relies on. Every API name below was checked in the pinned source.

## Lean `v4.33.1` — commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`

Source: `~/.elan/toolchains/leanprover--lean4---v4.33.1/src/lean/Lean`.

| Symbol | File | Use |
|---|---|---|
| `Environment.addDeclCore (doCheck := true)` → `lean_add_decl` | `Environment.lean:701` | the only insertion path (`Rocq2Lean/Kernel.lean`) |
| `addDeclWithoutChecking`, `debug.skipKernelTC` | `Environment.lean:307`, `:76` | forbidden; `addChecked` refuses to run if the option is set |
| `Lean.addDecl` | `AddDecl.lean:229` | not used: under the module system it may export theorems as axioms |
| `Expr`, `Level`, `Declaration` | `Expr.lean`, `Level.lean`, `Declaration.lean` | target representation |

## Rocq `V9.3.0` — commit `c8e202eb0d6cc08b848ba27dcf2cc35804df7d96` (2026-09-18)

| Symbol | File | Use |
|---|---|---|
| `Constr.kind` (`Case of case_info * univs * params * pcase_return * pcase_invert * c * pcase_branch array`) | `kernel/constr.mli:273` | raw kernel shape the frontend quotes |
| `Global.lookup_constant`, `Global.body_of_constant`, `Global.force_proof` | `library/global.mli:128-157` | native metadata/opaque-body access |
| `Library.indirect_accessor` | `vernac/library.mli:82` | accessor for opaque proofs of loaded libraries |

Rocq 9.3 branched from master at `d77b754f` (2026-07-08).

## MetaRocq — candidate `c18395ad772a40d59b6d04a5fcd1a4e0e5073d81` (main, 2026-08-10)

There is no MetaRocq release for Rocq 9.3 (latest `1.5.1+9.2`; `main` declares `rocq-core = dev`).
The candidate is the parent of `8456c5b0` ("Adapt to rocq-prover/rocq#22271"). Of the Rocq PRs that
MetaRocq `main` adapted to since 2026-04, all those up to #22164 are in `V9.3.0`, and #22271 and
#22516 are not, so this is the last `main` commit that matches 9.3.0's API.

| Symbol | File | Use |
|---|---|---|
| `Ast.term` (`tRel` 0-based … `tArray`), `predicate`, `branch` | `template-rocq/theories/Ast.v` | quoted term AST (compact case contexts: names only) |
| `case_info`, `def`/`mfixpoint` (`rarg`) | `common/theories/BasicAst.v` | case/fix metadata |
| `ExtractedASTQuoter.quote_term_rec ~bypass ~opaque_access` | `template-rocq/src/ast_quoter.ml:515` | OCaml-level recursive quotation across opacity |
| `case_branch_context`, `case_predicate_context` | `template-rocq/theories/Ast.v` | how compact contexts are rebuilt |

Dependencies: Coq-Equations tag `v1.3.2-9.3` = `d56dfc2c38feb5054d75ef43540ee89a6beb1a7e`;
coq-ext-lib `0.13.2` = `dd32f1c56f41d699ed2ffd4193a876c87fc44926`.

## rocq-lean-import — `2d28bbe` (reverse direction; architecture reference only)

`src/lean.ml`: structural term translation, universe surrogates, `_instN` Prop-instance
duplication, recursor argument reordering (`_indl`/`_recl`). Not used as a tool in M1–M3.

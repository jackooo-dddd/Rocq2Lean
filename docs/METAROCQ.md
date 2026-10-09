# MetaRocq in this project

* **Revision**: `c18395ad772a40d59b6d04a5fcd1a4e0e5073d81` (MetaRocq `main`, 2026-08-10), unpatched.
  No MetaRocq release targets Rocq 9.3; this is the last `main` commit before MetaRocq adapted
  to Rocq PRs that are *not* in `V9.3.0` (#22271, #22516). Built packages: `utils`, `common`,
  `template` only (no PCUIC, SafeChecker or erasure). Status: **METAROCQ_TEMPLATE_RUNNING**.
* **Dependencies**: Coq-Equations `v1.3.2-9.3` (`d56dfc2c`, opam pin; opam labels it
  `1.3.2+9.2`), coq-ext-lib `0.13.2`.
* **Gate** (`rocq/probes/MetaRocqGate.v`, log `reports/phase0/metarocq_gate.log`): a
  transparent definition and a `Qed` theorem loaded from a separately compiled `.vo`
  (`tmQuoteRecTransp _ true` → body present; `false` → hidden), a fresh inductive, universe
  levels, and the index convention (`fun x y => x` ↦ `tRel 1`).
* **Use**: the exporter calls the OCaml quoter `Ast_quoter.quote_term_rec ~bypass:true
  ~opaque_access` from a vernacular command classified `STATE opaque_access`. Reading opaque
  bodies does not change their source opacity and does not disable any checking.
* **Not used**: the erasure pipeline (the subject is typed proof terms, not extracted code);
  PCUIC; SafeChecker. SafeChecker could give extra source-side evidence for its fragment;
  neither it nor PCUIC is a Rocq-to-Lean correctness theorem.

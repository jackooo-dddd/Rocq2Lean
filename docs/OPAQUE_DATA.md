# A′: opaque data translated with its body

Decision (2026-10-13, confirmed 2026-10-14): the data-producing bodies of opaque `Set`/`Type` constants
(`Qed` with a non-propositional type) are translated mechanically; their source opacity is kept; their
genuine proof subterms are extracted as obligations. No submitted value ever stands for a source body,
and uniqueness of an inhabitant is never assumed. Synthetic test proofs remain the only testing
exception (Rocq2Lean writes no corpus proof).

## 1. Export (`rocq/exporter/src/r2l_export.ml`, `statement_env`)

For an opaque data constant (`is_opaque_data`: not proof-valued, native `OpaqueDef`) the body is now
prepared like a transparent definition's: proof subterms extracted (`extract_proofs`, obligations
`<c>__rocq2lean_obligation_<k>`), and the rewritten declaration re-checked by Rocq's kernel. Then:

* **accepted** → body state `opaque_data`: the IR carries the prepared body; `native.body_kind` stays
  `opaque` (Rocq's own record); the body's dependencies join the closure;
* **refused by the kernel re-check**, or **accepted only with the guard check deferred** (a recursion on
  an extracted proof subterm, e.g. MathComp's `find_ex_minn`, which recurses on an accessibility proof)
  → the interface treatment as before A′ (`opaque_interface`: type only, a value task that accepts no
  submission), with the reason in `opaque_body_refused`; only the type's own obligations are kept.

Round trip (`tools/roundtrip.py` `check_statement`): `opaque_data` rows are re-derived in a fresh Rocq
process (state, prepared body, obligations) and must have native opaque bodies. The statement
re-derivation now prepares the environment once for all of an export's constants
(`Rocq2Lean CheckStatementsPrepared`, as the export does) and re-derives a deterministic sample alone
(`CheckStatementPrepared`); both must agree with the IR (request independence).

## 2. Translation (`Rocq2Lean/Emit.lean`)

An `opaque_data` constant is translated as a definition whose declaration is a Lean **`opaque`**
constant under its own name, `opaque Rocq.<c> : ⟦T⟧ := ⟦b′⟧` — Lean's kernel never unfolds it, as Rocq
never unfolds `Qed`. While obligations (or other proof prerequisites) are unproved it is the pending
artifact `RocqPending.<c>` with them as hypotheses. Dependents reference the constant (they are no
longer pending on an opaque-value hypothesis). Not δ-inlined (only transparent bodies are).

## 3. Validation

* consumer (`Rocq2Lean/Verify.lean`): an `opaque` constant is allowed for definition rows (never for a
  statement row, never of a proposition);
* audit (`tools/audit.py`): an `opaque_data` row is audited as a definition (type and body term by
  term against the source), must be emitted as `opaque` (a `def` would expose an unfolding the source
  hides), and its native body must be opaque;
* tasks: no opaque-value task for a translated body; its obligations are ordinary proof tasks;
* assembly: the opaque constant is assembled like any pending definition (`Rocq.<c>`, kind opaque).

Tests (`scripts/test-opaque`, fixture `fixtures/stmt/opq/Opq.v`): bodies exported and round-tripped;
`pick` accepted as an opaque constant, `bounded` pending on its obligation, `nat_eqP` (reflect-valued,
by induction; 5 obligations under binders); opacity kept (`pick = 3` holds neither by `rfl` nor by
kernel reduction); negative controls (a different opaque value; the opaque data emitted as a `def`)
kernel-accepted and audit-rejected; assembly with a synthetic obligation proof yields the opaque
`Rocq.SF.Opq.bounded`. The assembly fixture keeps an interface case (`pick_wf`, body recursing on an
accessibility proof) for the value-task policy (`OPAQUE_BINDING_PENDING`).

## 4. Limits

* bodies with deferred termination keep the interface (no translation rule for recursion on an
  extracted proof subterm);
* universe-polymorphic and template behaviour of bodies follows the definition rules unchanged;
* computation through an opaque constant is not available in Lean (as in Rocq's kernel).

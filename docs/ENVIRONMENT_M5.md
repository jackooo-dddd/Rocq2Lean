# Architectural decision: MathComp environment (M5/M6)

**Decision.** M5 and M6 run in a dedicated opam switch, `rocq930-mc`. It is built with
`scripts/setup-switch-mc` from the **same pinned toolchain** as `rocq930`:

* Rocq 9.3.0, with `rocq-core`/`rocq-runtime` pinned;
* rocq-stdlib 9.2.0 and coq-ext-lib 0.13.2;
* Equations `d56dfc2c`;
* MetaRocq `c18395ad` (utils, common, template; unpatched).

It differs from `rocq930` in two ways: **dune is pinned to 3.23.1**, and it adds **MathComp 2.6.0**
(installed through opam together with Hierarchy Builder and rocq-elpi). No Lean, Rocq, MetaRocq or
stdlib version changes. The translator's lock and doctor validate the switch exactly as before.

## Why

MathComp 2.x is built with Hierarchy Builder, which needs `rocq-elpi`.

* `rocq-elpi` 3.5.1 (the newest release for Rocq 9.3) uses dune's `(using coq 0.8)` extension.
  dune 3.24 removed that extension (build error: "Extension coq was deleted in the 3.24 version of
  the dune language"), and the package's opam constraint is `dune < 3.24`.
* `rocq930` has dune 3.24.2. An `opam install` of MathComp into it plans to downgrade dune, rebuild
  Rocq, and **remove the pinned MetaRocq and Equations** (opam's metadata for those dev pins
  cannot be satisfied with `rocq-core` pinned at 9.3.0; they were installed with
  `--ignore-constraints-on`). That would break the frozen frontend, so it was not done.
* Ignoring only the dune cap gave an install-only plan, but rocq-elpi then fails to build.
* Building rocq-elpi with a dune 3.23.1 binary inside `rocq930` fails too: that switch's OCaml
  libraries were installed by dune 3.24.2, and dune 3.23.1 cannot read their `dune-package` files.

Investigation commands and outputs: `reports/m5/environment_investigation.md`.

A clean switch with dune 3.23.1 avoids all of these. Every package, the frontend included, is
built by one dune version, and the whole environment is opam-managed and reproducible.

## Consequences

* **Fingerprint.** The frontend and Rocq are *rebuilt* from the same pinned sources, so their
  binaries differ from those in `rocq930`. The toolchain fingerprint (content digests of `lean`,
  `libleanshared`, `rocq`, the MetaRocq plugins and theories) records the new binaries. Runs exported
  in one switch do not verify in the other: verify reports a toolchain change. This is the intended
  behaviour.
* **Regression.** The complete M1–M4 suite is re-run on `rocq930-mc` before any M5 result is claimed.
* **Original switch kept.** `rocq930` is kept unchanged, so the M1–M4 evidence recorded on it stays
  reproducible. Its only change is opam *additions* from the aborted MathComp install (27 OCaml
  build packages, `elpi` 3.7.3). Its translator fingerprint was checked to be unchanged
  (`reports/m5/toolchain_before_mathcomp.json`).

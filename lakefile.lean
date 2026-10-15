import Lake
open Lake DSL

package rocq2lean_pilot where
  leanOptions := #[⟨`autoImplicit, false⟩]

/-- Translator library: IR reader, translation, kernel insertion, audits. -/
@[default_target]
lean_lib Rocq2Lean where
  -- speed (entry 14): the translator runs as native code (`--load-dynlib`), not in the IR interpreter;
  -- the same program, still checked by the kernel and the independent audit
  precompileModules := true

/-- Phase 0 smoke tests of the checked kernel path. -/
lean_lib Smoke where
  srcDir := "tests/smoke"
  roots := #[`KernelPath, `Sha256Vectors, `UniverseRules]

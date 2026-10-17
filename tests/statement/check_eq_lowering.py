"""Rule E (docs/EQ_LOWERING.md, approved 2026-10-17): the conclusion `@eq T a b` of an unprotected statement, its
operands convertible, is stated at the operands' own type (Rocq types them at the larger `T` by cumulativity).
Fixture fixtures/stmt/eqlow (synthetic, CoqEAL's `refinesE` shape), through the real exporter and translator.

1. Pipeline: export, translate, validate (consumer, audit).
2. Positive: `refinesE` (`refines A B R = R` at `A → B → Type@{c}`, `R` at `Type@{b}`) claimed with
   `eq_lowered` = 1.
3. Negative: `neq` (an equality of distinct relations at the larger universe) never lowered; forged rows — rule E
   on a definition, on a statement whose conclusion is an equality at a non-sort type, a lowering count other
   than 1 — audit-rejected; unit controls on the consumer's E1 check (convertible accepted, distinct rejected).

Writes reports/statement_only/test_eq_lowering.json.
"""
import copy
import json
import os
import shutil
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from lib import ROOT, audit_report, check, cli, finish, forge_run, results  # noqa: E402

OUT = {}
RUN = ROOT / "runs" / "st-eqlow"
F = "SF.Eqlow."
ROOTS = [F + x for x in ("refines", "refinesE", "neq", "other")]
CLAIMED = ("TRANSLATED_AND_CHECKED", "STATEMENT_KERNEL_CHECKED", "PENDING_KERNEL_CHECKED", "STATEMENT_PENDING_KERNEL_CHECKED")

shutil.rmtree(RUN, ignore_errors=True)
rcs = [cli("export", "--mode", "statement", "--manifest", ROOT / "fixtures/stmt/eqlow/manifest.json",
           "--roots", ",".join(ROOTS), "--out", RUN)[0]]
rcs.append(cli("translate", "--input", RUN / "source.ndjson", "--out", RUN)[0])
rcs.append(cli("validate", "--run", RUN)[0])
v = json.loads((RUN / "validate.json").read_text())
R, rep = results(RUN)
OUT["pipeline"] = {"exit_codes": rcs, "validation": v.get("status"), "by_validation": v.get("by_validation")}
OUT["rows"] = {n: {k: r.get(k) for k in ("status", "eq_lowered", "message")} for n, r in R.items() if n.startswith(F)}
check(rcs[0] == 0 and rcs[2] == 0 and v.get("status") == "STATEMENT_VALIDATED", "fixture: validated (consumer E1 and audit)")
check(R[F + "refinesE"]["status"] in CLAIMED and R[F + "refinesE"].get("eq_lowered") == 1,
      "refinesE (convertible operands, larger universe): stated at the operands' universe, reported")
check(R[F + "neq"]["status"] not in CLAIMED and not R[F + "neq"].get("eq_lowered"),
      "neq (distinct relations at the larger universe): never lowered, refused")
check(R[F + "other"]["status"] in CLAIMED and not R[F + "other"].get("eq_lowered"), "an ordinary equality statement: unchanged")


def forge(label, row, edit):
    rep2 = copy.deepcopy(rep)
    rows = {x["source"]: x for x in rep2["results"]}
    edit(rows[row])
    d, _, rc, cons, aud = forge_run(RUN, label, rep2, check_cmd="validate")
    aprobs = aud.get("problems") if aud else audit_report(d, rep2, "forged")[1]
    probs = [p_["message"][:300] for p_ in aprobs if p_["message"].startswith(row + ":")]
    OUT.setdefault("negative", {})[label] = {"validate_exit": rc, "audit_problems": probs[:4]}
    return rc, probs


rc, probs = forge("on-definition", F + "refines", lambda r: r.update(eq_lowered=1))
check(rc == 2 and any("not a statement" in p for p in probs), "rule E reported on a definition: audit-rejected")
rc, probs = forge("conclusion-not-sort-ended", F + "other", lambda r: r.update(eq_lowered=1))
check(rc == 2 and any("sort-ended" in p for p in probs), "rule E on an equality at a non-sort type: audit-rejected")
rc, probs = forge("count-not-one", F + "refinesE", lambda r: r.update(eq_lowered=2))
check(rc == 2 and any("exactly the conclusion" in p for p in probs), "a lowering count other than 1: audit-rejected")

# unit controls on the consumer's E1 (independent Lean re-check of convertibility)
lean = RUN / "lean"
(lean / "E1Unit.lean").write_text("""import Rocq2Lean
open Lean Meta
#eval show MetaM Unit from do
  let rel ← mkArrow (mkConst ``Nat) (mkSort levelZero)
  let distinct ← withLocalDeclD `R rel fun r => withLocalDeclD `S rel fun s => do mkForallFVars #[r, s] (← mkEq r s)
  let same ← withLocalDeclD `R rel fun r => do mkForallFVars #[r] (← mkEq r r)
  IO.println s!"E1 distinct={← Rocq2Lean.checkEqLowered distinct} same={← Rocq2Lean.checkEqLowered same}"
""")
env = dict(os.environ, PATH=f"{Path.home()}/.elan/bin:" + os.environ["PATH"])
q = subprocess.run(["lake", "-d", str(ROOT), "env", "lean", "E1Unit.lean"], cwd=lean, capture_output=True, text=True, env=env)
out = q.stdout + q.stderr
OUT["unit"] = out[:500]
check(q.returncode == 0 and "E1 distinct=false same=true" in out, f"consumer E1: distinct operands rejected, convertible accepted ({out.strip()[:80]})")

(ROOT / "reports" / "statement_only" / "test_eq_lowering.json").write_text(json.dumps(OUT, indent=1) + "\n")
finish("test-eq-lowering")

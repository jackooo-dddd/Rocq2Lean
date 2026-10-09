"""M1: complete source export and dependency validation (plus translation of the M1 constants)."""
import shutil
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from lib import ROOT, check, cli, decls, results, finish  # noqa: E402

MAN = ROOT / "fixtures" / "m1" / "manifest.json"
POS = ["M1.M1Chain.chain_qed", "M1.M1Chain.chain_sec", "M1.M1Chain.chain_opaque_data",
       "M1.M1Chain.chain_chain", "M1.M1Base.two_eq", "M1.M1Base.two_refl_defined", "M1.M1Base.let_test"]
NEG = ["M1.M1Chain.uses_color", "M1.M1Neg.uses_ax", "M1.M1Neg.uses_relaxed"]

# ---- positive run: export, translate, verify
run = ROOT / "runs" / "m1"
shutil.rmtree(run, ignore_errors=True)
rc, out = cli("export", "--manifest", MAN, "--roots", ",".join(POS), "--out", run)
check(rc == 0, "M1 export of positive roots succeeds (with independent round trip)")
D = decls(run / "source.ndjson")
st = {n: d.get("body_state") for n, d in D.items()}
check(st["M1.M1Base.two"] == "transparent", "transparent data definition")
check(st["M1.M1Base.two_eq"] == "transparent", "transparent proof-valued definition stays transparent")
check(st["M1.M1Base.two_eq_qed"] == "opaque_present", "Qed proof body exported (opacity bypass)")
check(st["M1.M1Base.three_opaque"] == "opaque_present", "opaque data-valued constant body exported")
check(st["M1.M1Base.two_refl_defined"] == "transparent", "Defined is transparent")
at = D["M1.M1Base.add_two"]["type"]
check(at["k"] == "prod" and at["b"]["k"] == "ind", "Section variable discharged into a leading binder")
check(D["M1.M1Chain.chain_chain"]["deps"]["body"] == ["M1.M1Chain.chain_qed"]
      and "M1.M1Base.two_eq_qed" in D["M1.M1Chain.chain_qed"]["deps"]["body"],
      "opaque dependency chain collected through proof bodies (body deps, not type deps)")
check("M1.M1Base.two_eq_qed" not in D["M1.M1Chain.chain_qed"]["deps"]["type"], "type and body deps distinguished")
check("M1.M1Base.Color" not in D, "inductive outside the closure is not exported (explicit roots, not whole library)")
rc, out = cli("translate", "--input", run / "source.ndjson", "--out", run)
check(rc == 0, "M1 positive roots translate")
R, rep = results(run)
kinds = {n: R[n]["target_kind"] for n in R if R[n]["status"] == "TRANSLATED_AND_CHECKED"}
check(kinds.get("M1.M1Base.two_eq") == "def", "transparent proof-valued definition emitted as def (not theorem)")
check(kinds.get("M1.M1Base.two_eq_qed") == "theorem", "opaque proof emitted as theorem")
check(kinds.get("M1.M1Base.three_opaque") == "opaque", "opaque data-valued constant emitted as opaque")
check(rep["summary"]["bootstrap_resolved"] == 2, "bootstrap-resolved references counted separately")
rc, out = cli("verify", "--run", run)
check(rc == 0, "M1 positive run VERIFIED (snapshot, consumer, audit)")

# ---- negative run: every root must be rejected with the right status
neg = ROOT / "runs" / "m1-neg"
shutil.rmtree(neg, ignore_errors=True)
rc, out = cli("export", "--manifest", MAN, "--roots", ",".join(NEG), "--out", neg)
check(rc == 0, "M1 negative roots still export faithfully")
rc, out = cli("translate", "--input", neg / "source.ndjson", "--out", neg)
check(rc != 0, "translation of negative roots exits non-zero")
R, rep = results(neg)
check(R["M1.M1Neg.ax"]["status"] == "BLOCKED_SOURCE_BODY", "genuine assumption detected (no axiom created)")
check(R["M1.M1Neg.uses_ax"]["status"] == "BLOCKED_DEPENDENCY"
      and R["M1.M1Neg.uses_ax"]["blocked_by"] == ["M1.M1Neg.ax"], "dependency on an assumption blocks the proof")
check(R["M1.M1Neg.relaxed"]["status"] == "AUDIT_REJECTED", "relaxed source checking rejected")
check(R["M1.M1Neg.uses_relaxed"]["status"] == "BLOCKED_DEPENDENCY", "dependent of relaxed input blocked")
check(R["M1.M1Base.Color"]["status"] == "TRANSLATED_AND_CHECKED"
      and R["M1.M1Chain.uses_color"]["status"] == "TRANSLATED_AND_CHECKED",
      "simple inductive and its use translate (M3a); unsupported inductives are covered by test-m3")
rc, out = cli("verify", "--run", neg)
check(rc != 0, "verify refuses a run whose roots were rejected")
finish("test-m1")

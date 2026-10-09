"""Historical holdout fixtures (regression role).

These nine roots were unseen when the implementation was frozen at tag `pilot-freeze-1`. The
hardening work (2026-10) necessarily changed the implementation, so they are no longer unseen
holdouts: this runner keeps them as regression tests and *records* (does not assert away) the
implementation change since the historical freeze. Fresh holdouts for the hardened freeze live
in tests/holdout2/.
"""
import shutil
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from lib import ROOT, check, cli, results, finish  # noqa: E402

IMPL = ["Rocq2Lean", "Rocq2Lean.lean", "tools", "rocq/exporter", "rocq/roundtrip", "lakefile.lean", "toolchains.lock.json"]
p = subprocess.run(["git", "-C", str(ROOT), "diff", "--stat", "pilot-freeze-1", "--", *IMPL], capture_output=True, text=True)
changed = p.stdout.strip().splitlines()
check(subprocess.run(["git", "-C", str(ROOT), "rev-parse", "pilot-freeze-1^{commit}"], capture_output=True).returncode == 0,
      "historical freeze tag pilot-freeze-1 still present (not moved)")
print(f"NOTE implementation changed since pilot-freeze-1 ({changed[-1] if changed else 'no change'}): "
      "historical holdouts now run as regression tests")
ROOTS = ["H.Holdout." + n for n in ("incr_not_BZ", "omap_id", "swap_swap", "le_0", "length_app", "addR_comm",
                                     "addR_assoc", "size_mirror", "vapp_nil")]
run = ROOT / "runs" / "holdout"
shutil.rmtree(run, ignore_errors=True)
man = ROOT / "fixtures" / "holdout" / "manifest.json"
check(cli("export", "--manifest", man, "--roots", ",".join(ROOTS), "--out", run)[0] == 0, "holdout export + round trip")
check(cli("translate", "--input", run / "source.ndjson", "--out", run)[0] == 0, "all 9 holdout roots TRANSLATED_AND_CHECKED")
check(cli("verify", "--run", run)[0] == 0, "holdout run VERIFIED")
R, rep = results(run)
check(R["Corelib.Init.Logic.False"]["status"] == "TRANSLATED_AND_CHECKED"
      and R["Corelib.Init.Nat.add"]["status"] == "TRANSLATED_AND_CHECKED",
      "holdout pulled new Corelib content (False/True/not/Nat.add) through the generic rules")
finish("test-holdout")

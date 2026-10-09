"""CLI status semantics: 0 = success/candidate, 2 = rejection/known blocker, 3 = invalid input or
tool failure; wrappers propagate; reasons are checked, not just non-zero exits."""
import json
import shutil
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from lib import ROOT, check, finish  # noqa: E402

W = str(ROOT / "scripts" / "rocq2lean")
PY = [sys.executable, "-I", str(ROOT / "tools" / "rocq2lean.py")]
PF = [sys.executable, "-I", str(ROOT / "tools" / "preflight.py")]
M3 = str(ROOT / "fixtures" / "m3" / "manifest.json")


def run(cmd):
    p = subprocess.run(cmd, capture_output=True, text=True)
    return p.returncode, p.stdout + p.stderr


for entry, base in (("python", PY), ("wrapper", [W])):
    rc, out = run(base + ["doctor"])
    check(rc == 0 and "doctor: OK" in out, f"[{entry}] doctor exits 0 on the fixed toolchains")
    rc, out = run(base + ["inspect", "--manifest", M3, "--roots", "M3.M3Fix.addR_RS"])
    check(rc == 0 and '"CANDIDATE_SUPPORTED"' in out, f"[{entry}] inspect of a supported root exits 0")
    rc, out = run(base + ["inspect", "--manifest", M3, "--roots", "M3.M3Neg.sprop_id"])
    check(rc == 2 and "UNSUPPORTED_FEATURE" in out, f"[{entry}] inspect of a known blocker exits 2 with its reason")
    rc, out = run(base + ["export", "--manifest", "/nonexistent/manifest.json", "--roots", "X.y", "--out", str(ROOT / "runs" / "cli-bad")])
    check(rc == 3 and "TOOL_FAILURE" in out, f"[{entry}] missing manifest is a tool failure (exit 3), not a rejection")
    rc, out = run(base + ["export", "--manifest", M3, "--roots", "", "--out", str(ROOT / "runs" / "cli-empty")])
    check(rc == 2 and "ROOT_CONTRACT_REJECTED" in out, f"[{entry}] empty request is a rejection (exit 2)")
    rc, out = run(base + ["verify", "--run", str(ROOT / "runs" / "cli-nothing")])
    check(rc == 2 and "missing source snapshot" in out, f"[{entry}] verify of an empty run directory is rejected (exit 2)")
    rc, out = run(base + ["bogus-subcommand"])
    check(rc != 0, f"[{entry}] unknown subcommand fails")

# Standalone preflight on IR files.
good = ROOT / "runs" / "h-m3d" / "source.ndjson"
rc, out = run(PF + [str(good)])
check(rc == 0 and "CANDIDATE_SUPPORTED" in out, "preflight: all-candidate IR exits 0")
neg = ROOT / "runs" / "cli-neg"
shutil.rmtree(neg, ignore_errors=True)
assert run(PY + ["export", "--manifest", M3, "--roots", "M3.M3Neg.sprop_id,M3.M3Fix.addR_RS", "--out", str(neg)])[0] == 0
rc, out = run(PF + [str(neg / "source.ndjson")])
check(rc == 2 and "UNSUPPORTED_FEATURE" in out and "SProp" in out, "preflight: known blocker exits 2 and names the reason")
rc, out = run(PF + ["/nonexistent.ndjson"])
check(rc == 3 and "TOOL_FAILURE" in out, "preflight: invalid input exits 3")
# A shell pipeline must not hide the failure.
p = subprocess.run(["bash", "-c", f"set -o pipefail; {W} inspect --manifest {M3} --roots M3.M3Neg.sprop_id | cat"],
                   capture_output=True, text=True)
check(p.returncode == 2, "pipefail: a failing inspect through a pipeline still reports exit 2")
finish("test-cli-status")

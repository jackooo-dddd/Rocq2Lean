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
# The suite builds its own inputs (no dependence on runs left by other suites or earlier sessions).
gooddir = ROOT / "runs" / "cli-good"
shutil.rmtree(gooddir, ignore_errors=True)
assert run(PY + ["export", "--manifest", M3, "--roots", "M3.M3Proofs.mirror_mirror,M3.M3Proofs.vmap_id", "--out", str(gooddir)])[0] == 0
good = gooddir / "source.ndjson"
rc, out = run(PF + [str(good)])
check(rc == 0 and "CANDIDATE_SUPPORTED" in out, "preflight: all-candidate IR exits 0")
neg = ROOT / "runs" / "cli-neg"
shutil.rmtree(neg, ignore_errors=True)
assert run(PY + ["export", "--manifest", M3, "--roots", "M3.M3Neg.sprop_id,M3.M3Fix.addR_RS", "--out", str(neg)])[0] == 0
rc, out = run(PF + [str(neg / "source.ndjson")])
check(rc == 2 and "UNSUPPORTED_FEATURE" in out and "SProp" in out, "preflight: known blocker exits 2 and names the reason")
rc, out = run(PF + ["/nonexistent.ndjson"])
check(rc == 3 and "TOOL_FAILURE" in out, "preflight: invalid input exits 3")
# Every known blocker of the M3 negative fixtures is reported by inspect (one export, all roots),
# with structured diagnostics: status, blocked declaration, dependency path, reasons and node paths.
NEG = {"M3.M3Neg.Stream": "coinductive type", "M3.M3Neg.sprop_id": "SProp"}
rc, out = run(PY + ["inspect", "--manifest", M3, "--roots", ",".join(NEG)])
rep = json.loads(out[:out.rindex("}") + 1])
check(rc == 2 and "UNSUPPORTED_FEATURE" in out, "inspect of the M3 negative roots exits 2")
for r, reason in NEG.items():
    v = rep["roots"][r]
    check(v["status"] == "UNSUPPORTED_FEATURE" and reason in v["reasons"] and v["blocked_declaration"] == r
          and reason in v["locations"] and v["dependency_path"] == [r],
          f"inspect: {r} blocked by '{reason}' at {v.get('locations', {}).get(reason)}")
# Mutual fixpoints (joint recursor) and calls on non-direct subterms (course-of-values) are translated
# since M6 completion: evenR and half are no longer blockers.
for r_, what in (("M3.M3Neg.evenR", "mutual fixpoint"), ("M3.M3Neg.half", "call on a field of a field"),
                 ("M3.M3Neg.rose_size", "match on a nested inductive")):
    rc, out = run(PY + ["inspect", "--manifest", M3, "--roots", r_])
    rep = json.loads(out[:out.rindex("}") + 1])
    check(rc == 0 and rep["roots"][r_]["status"] == "CANDIDATE_SUPPORTED",
          f"inspect: {r_.split('.')[-1]} ({what}) is a candidate since M6 completion, not a blocker")
# Universe-polymorphic constants are translated since M6 (rule R6): pid is no longer a blocker.
rc, out = run(PY + ["inspect", "--manifest", M3, "--roots", "M3.M3Neg.pid"])
rep = json.loads(out[:out.rindex("}") + 1])
check(rc == 0 and rep["roots"]["M3.M3Neg.pid"]["status"] == "CANDIDATE_SUPPORTED",
      "inspect: universe-polymorphic pid is a candidate since M6 (R6)")
# A blocker reached through a dependency names the dependency path; relaxed checking is a blocker.
M1 = str(ROOT / "fixtures" / "m1" / "manifest.json")
rc, out = run(PY + ["inspect", "--manifest", M1, "--roots", "M1.M1Neg.uses_ax,M1.M1Neg.uses_relaxed,M1.M1Chain.uses_color"])
rep = json.loads(out[:out.rindex("}") + 1])
check(rc == 2 and rep["roots"]["M1.M1Neg.uses_ax"]["dependency_path"] == ["M1.M1Neg.uses_ax", "M1.M1Neg.ax"]
      and "genuine source assumption" in rep["roots"]["M1.M1Neg.uses_ax"]["reasons"],
      "inspect: a blocker in a dependency is reported with its dependency path (uses_ax -> ax)")
check(any(x.startswith("relaxed source checking") for x in rep["roots"]["M1.M1Neg.uses_relaxed"]["reasons"]),
      "inspect: relaxed source checking is a known blocker")
check(rep["roots"]["M1.M1Chain.uses_color"]["status"] == "CANDIDATE_SUPPORTED", "inspect: supported root in the same request stays a candidate")
# Agreement with the translator: every positive M3 root is a candidate.
rc, out = run(PF + [str(ROOT / "runs" / "cli-good" / "source.ndjson")])
check(rc == 0, "preflight agrees with the translator on supported roots (exit 0)")
# A shell pipeline must not hide the failure.
p = subprocess.run(["bash", "-c", f"set -o pipefail; {W} inspect --manifest {M3} --roots M3.M3Neg.sprop_id | cat"],
                   capture_output=True, text=True)
check(p.returncode == 2, "pipefail: a failing inspect through a pipeline still reports exit 2")
finish("test-cli-status")

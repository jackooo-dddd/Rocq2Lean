"""Fresh holdouts for the hardened implementation (role: unseen inputs).

The fixtures in fixtures/holdout2/ were written *after* the implementation was frozen at the
annotated tag `hardening-freeze-1`, whose commit is recorded in tests/holdout2/FREEZE. This runner
first checks that the tag still names that commit and that no implementation file differs from it
(committed or not); then it runs every holdout root through the public CLI (inspect, export,
translate, verify, status) and records each root's outcome in reports/hardening/holdout2.json.
Outcomes are recorded as observed: a failing holdout is a finding, never relabelled.

Role. While the implementation equals the freeze, these are unseen holdouts (record:
reports/hardening/holdout2.json, committed at 6e85e3c). Once a later milestone changes the
implementation, the same roots run as *regression tests* (record: reports/hardening/
holdout2_regression.json): the freeze tag must still be intact, the implementation change is
recorded, and every root must still verify.
"""
import json
import shutil
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from lib import ROOT, check, cli, finish, results  # noqa: E402

IMPL = ["Rocq2Lean", "Rocq2Lean.lean", "tools", "rocq/exporter", "rocq/roundtrip", "lakefile.lean", "lake-manifest.json",
        "lean-toolchain", "toolchains.lock.json", "scripts/rocq2lean"]
git = lambda *a: subprocess.run(["git", "-C", str(ROOT), *a], capture_output=True, text=True)
want = (Path(__file__).parent / "FREEZE").read_text().split()[0]
tag = git("rev-parse", "hardening-freeze-1^{commit}").stdout.strip()
check(tag == want, f"freeze tag hardening-freeze-1 names the recorded commit {want[:12]} (found {tag[:12] or 'none'})")
check(git("cat-file", "-t", "hardening-freeze-1").stdout.strip() == "tag", "hardening-freeze-1 is an annotated tag")
check(git("rev-parse", "pilot-freeze-1^{commit}").returncode == 0, "historical freeze pilot-freeze-1 still present")
diff = git("diff", "--stat", want, "--", *IMPL).stdout.strip()
untracked = git("ls-files", "--others", "--exclude-standard", "--", *IMPL).stdout.split()
ROLE = "fresh-holdout" if diff == "" and not untracked else "regression"
if ROLE == "fresh-holdout":
    check(True, "implementation identical to the freeze (committed and working tree): fresh-holdout role")
else:
    print(f"NOTE implementation changed since hardening-freeze-1 ({diff.splitlines()[-1] if diff else 'untracked files'}): "
          "holdout2 roots now run as regression tests")
first = git("log", "--diff-filter=A", "--format=%H", "--", "fixtures/holdout2").stdout.split()
check(bool(first) and git("merge-base", "--is-ancestor", want, first[-1]).returncode == 0 and first[-1] != want,
      "holdout fixtures were first committed after the freeze commit")

MAN = ROOT / "fixtures" / "holdout2" / "manifest.json"
ROOTS = json.loads((ROOT / "fixtures" / "holdout2" / "roots.json").read_text())
out = {"schema": "rocq2lean-holdout2/1", "freeze": want, "role": ROLE, "roots": {}}
run = ROOT / "runs" / "holdout2"
shutil.rmtree(run, ignore_errors=True)
rc_i, txt = cli("inspect", "--manifest", MAN, "--roots", ",".join(ROOTS))
pre = json.loads(txt[:txt.rindex("}") + 1]) if "}" in txt else {"roots": {}}
rcs = {"export": cli("export", "--manifest", MAN, "--roots", ",".join(ROOTS), "--out", run)[0]}
rcs["translate"] = cli("translate", "--input", run / "source.ndjson", "--out", run)[0] if rcs["export"] == 0 else None
rcs["verify"] = cli("verify", "--run", run)[0] if rcs["translate"] == 0 else None
rcs["status"] = cli("status", "--run", run)[0] if rcs["verify"] == 0 else None
R = results(run)[0] if (run / "translation_report.json").exists() else {}
for r in ROOTS:
    out["roots"][r] = {"preflight": pre["roots"].get(r, {}).get("status"),
                       "translation": R.get(r, {}).get("status"), "message": R.get(r, {}).get("message", "")[:300]}
out["pipeline_exit_codes"] = rcs
out["verified"] = rcs["verify"] == 0 and rcs["status"] == 0
if (run / "verify.json").exists():
    v = json.loads((run / "verify.json").read_text())
    out["verify_status"] = v["status"]
    out["required_closure_size"] = v.get("required_closure_size")
(ROOT / "reports" / "hardening").mkdir(parents=True, exist_ok=True)
rec = "holdout2.json" if ROLE == "fresh-holdout" else "holdout2_regression.json"
(ROOT / "reports" / "hardening" / rec).write_text(json.dumps(out, indent=2) + "\n")
for r, v in out["roots"].items():
    check(v["preflight"] == "CANDIDATE_SUPPORTED" and v["translation"] == "TRANSLATED_AND_CHECKED",
          f"holdout root {r}: preflight {v['preflight']}, translation {v['translation']} {v['message'][:120]}")
check(rcs == {"export": 0, "translate": 0, "verify": 0, "status": 0},
      f"holdout run: export/translate/verify/status exit codes {rcs}; VERIFIED_CURRENT")
finish("test-holdout2")

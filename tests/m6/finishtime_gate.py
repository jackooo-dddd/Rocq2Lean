"""M6 completion gate (strict): ONE fresh run of the five FinishTime roots
(fixtures/m6/regression/finishtime5.json) through export, translate, verify and the artifact-currency
check (status). Exit 0 only if every root is TRANSLATED_AND_CHECKED, verify reports VERIFIED and
status reports VERIFIED_CURRENT. Writes reports/m6/finishtime_gate.json, bound to the implementation
tree, the git revision (dirty or not), the source IR digest and the toolchain fingerprint. No expected
rejection is ever counted as a pass here; exploratory runs live elsewhere.
"""
import hashlib
import json
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tests"))
from lib import cli  # noqa: E402

# the patched Prosa build the manifest requires (as scripts/test-m6-prosa does)
if not (ROOT / ".work" / "prosa-0.6-rocq93" / "analysis" / "facts" / "behavior" / "all.vo").exists():
    subprocess.run([str(ROOT / "scripts" / "setup-prosa"), "--full"], check=True)
REQ = json.loads((ROOT / "fixtures" / "m6" / "regression" / "finishtime5.json").read_text())
RUN = ROOT / "runs" / "m6-gate-finishtime5"


def git(*a):
    return subprocess.run(["git", "-C", str(ROOT), *a], capture_output=True, text=True).stdout.strip()


def main():
    shutil.rmtree(RUN, ignore_errors=True)
    steps = {}
    rc, out = cli("export", "--manifest", ROOT / REQ["manifest"], "--roots", ",".join(REQ["roots"]), "--out", RUN)
    steps["export"] = rc
    if rc == 0:
        steps["translate"], _ = cli("translate", "--input", RUN / "source.ndjson", "--out", RUN)
        steps["verify"], _ = cli("verify", "--run", RUN)
        steps["status"], sout = cli("status", "--run", RUN)
    rep = json.loads((RUN / "translation_report.json").read_text()) if (RUN / "translation_report.json").exists() else {}
    st = {x["source"]: x for x in rep.get("results", [])}
    roots = {r: st.get(r, {}).get("status") for r in REQ["roots"]}
    ver = json.loads((RUN / "verify.json").read_text()) if (RUN / "verify.json").exists() else {}
    not_ok = {s: {"status": x["status"], "message": x["message"][:300]} for s, x in st.items()
              if x["status"] not in ("TRANSLATED_AND_CHECKED", "BOOTSTRAP_RESOLVED", "BLOCKED_DEPENDENCY")}
    blocked = sum(1 for x in st.values() if x["status"] == "BLOCKED_DEPENDENCY")
    passed = (steps.get("export") == 0 and steps.get("translate") == 0 and steps.get("verify") == 0
              and steps.get("status") == 0 and all(v == "TRANSLATED_AND_CHECKED" for v in roots.values())
              and ver.get("status") == "VERIFIED")
    ir = RUN / "source.ndjson"
    out = {"gate": "M6_FINISHTIME_COMPLETE", "verdict": "PASS" if passed else "FAIL", "steps": steps, "roots": roots,
           "required_closure": ver.get("required_closure_size"), "verify_status": ver.get("status"),
           "root_failures_in_closure": not_ok, "blocked_dependents": blocked,
           "binding": {"git_head": git("rev-parse", "HEAD"), "git_dirty": bool(git("status", "--porcelain")),
                       "impl_tree_sha256": ver.get("impl_tree_sha256") or (ver.get("bound_sha256") or {}).get("impl_tree"),
                       "toolchain_fingerprint": ver.get("toolchain_fingerprint"),
                       "source_ir_sha256": hashlib.sha256(ir.read_bytes()).hexdigest() if ir.exists() else None}}
    (ROOT / "reports" / "m6").mkdir(parents=True, exist_ok=True)
    (ROOT / "reports" / "m6" / "finishtime_gate.json").write_text(json.dumps(out, indent=2) + "\n")
    print(f"M6_FINISHTIME_COMPLETE gate: {out['verdict']}  roots={roots}  closure={out['required_closure']}")
    return 0 if passed else 1


if __name__ == "__main__":
    sys.exit(main())

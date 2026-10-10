"""Acceptance gate for HARDENED_M1_M3_ACCEPTED, computed from recorded evidence (never asserted).

    scripts/acceptance   ->  reports/acceptance.json; exit 0 iff every gate passes

Gates
  clean_rebuild      a fresh clone, built and tested in fresh processes (reports/clean_rebuild/):
                     every required suite PASS; its commit equals HEAD outside reports/ and docs
  in_place_suite     reports/test_all.json: every required suite PASS on a commit equal to HEAD
                     outside reports/ and docs
  fixtures_preserved M1–M3, bootstrap and historical holdout fixtures byte-identical to the last
                     reviewed commit 7adb40b (original statements and proofs)
  freezes            pilot-freeze-1 unchanged; hardening-freeze-1 annotated; implementation at HEAD
                     identical to hardening-freeze-1
  fresh_holdouts     reports/hardening/holdout2.json: every fresh holdout root translated, the run
                     VERIFIED and current, on the frozen implementation
  evidence_package   reports/evidence/*.tar.gz matches its .sha256; built from a commit equal to
                     HEAD outside reports/ and docs
"""
import hashlib
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
REVIEWED = "7adb40bef74b653e97821807374462d660512737"
PILOT_FREEZE = "6a4054d"
REQUIRED = ["doctor", "test-smoke", "test-m1", "test-m2", "test-m3", "test-negative", "test-holdout", "test-root-contract",
            "test-artifact-integrity", "test-universe-audit", "test-lowering-audit", "test-source-metadata",
            "test-cli-status", "test-assumptions", "test-holdout2"]
IMPL = ["Rocq2Lean", "Rocq2Lean.lean", "tools", "rocq/exporter", "rocq/roundtrip", "lakefile.lean", "lake-manifest.json",
        "lean-toolchain", "toolchains.lock.json", "scripts/rocq2lean"]
NON_EVIDENCE = [":(exclude)reports", ":(exclude)docs", ":(exclude)STATUS.md", ":(exclude)README.md"]


def git(*a):
    return subprocess.run(["git", "-C", str(ROOT), *a], capture_output=True, text=True)


def same_outside_reports(commit):
    return bool(commit) and git("diff", "--quiet", commit, "HEAD", "--", ".", *NON_EVIDENCE).returncode == 0


def suites(path):
    if not path.exists():
        return False, f"{path.relative_to(ROOT)} missing", None
    t = json.loads(path.read_text())
    res = {r["suite"]: r for r in t["results"]}
    bad = [s for s in REQUIRED if res.get(s, {}).get("result") != "PASS" or res[s].get("checks_failed", 0)]
    checks = sum(r.get("checks_passed", 0) for r in t["results"])
    ok = not bad and same_outside_reports(t["commit"])
    why = (f"{len(REQUIRED)} suites PASS, {checks} checks, commit {t['commit'][:12]}" if ok else
           f"failing/missing suites {bad}; commit {t['commit'][:12]} equal to HEAD outside reports: {same_outside_reports(t['commit'])}")
    return ok, why, t


gates = {}
ok, why, t = suites(ROOT / "reports" / "clean_rebuild" / "test_all.json")
cr = ROOT / "reports" / "clean_rebuild" / "clean_rebuild.json"
crj = json.loads(cr.read_text()) if cr.exists() else {}
if ok and not (crj.get("fresh_clone") and crj.get("lake_build_exit") == 0 and crj.get("test_all_exit") == 0):
    ok, why = False, f"clean rebuild record incomplete: {crj}"
gates["clean_rebuild"] = {"ok": ok, "detail": why, "toolchain_rebuilt": crj.get("toolchain_rebuilt", False)}
ok, why, _ = suites(ROOT / "reports" / "test_all.json")
gates["in_place_suite"] = {"ok": ok, "detail": why}
fx = ["fixtures/m1", "fixtures/m2", "fixtures/m3", "fixtures/bootstrap", "fixtures/holdout"]
d = git("diff", "--stat", REVIEWED, "HEAD", "--", *fx).stdout.strip()
gates["fixtures_preserved"] = {"ok": d == "" and git("diff", "--quiet", "HEAD", "--", *fx).returncode == 0,
                               "detail": "identical to 7adb40b" if d == "" else d.splitlines()[-1]}
pf = git("rev-parse", "pilot-freeze-1^{commit}").stdout.strip()
hf = git("rev-parse", "hardening-freeze-1^{commit}").stdout.strip()
impl_same = bool(hf) and git("diff", "--quiet", hf, "HEAD", "--", *IMPL).returncode == 0 and \
    git("diff", "--quiet", "HEAD", "--", *IMPL).returncode == 0
gates["freezes"] = {"ok": pf.startswith(PILOT_FREEZE) and git("cat-file", "-t", "hardening-freeze-1").stdout.strip() == "tag" and impl_same,
                    "detail": f"pilot-freeze-1={pf[:12]}, hardening-freeze-1={hf[:12]}, implementation unchanged since: {impl_same}"}
h2 = ROOT / "reports" / "hardening" / "holdout2.json"
h = json.loads(h2.read_text()) if h2.exists() else {}
roots = h.get("roots", {})
gates["fresh_holdouts"] = {"ok": bool(roots) and h.get("verified") is True and h.get("freeze") == hf
                           and all(v["translation"] == "TRANSLATED_AND_CHECKED" for v in roots.values()),
                           "detail": f"{sum(v['translation'] == 'TRANSLATED_AND_CHECKED' for v in roots.values())}/{len(roots)} roots "
                                     f"translated; verified={h.get('verified')}; freeze={str(h.get('freeze'))[:12]}"}
pk = sorted((ROOT / "reports" / "evidence").glob("rocq2lean-evidence-*.tar.gz"))
if pk:
    p = pk[-1]
    want = (p.parent / (p.name + ".sha256")).read_text().split()[0] if (p.parent / (p.name + ".sha256")).exists() else ""
    got = hashlib.sha256(p.read_bytes()).hexdigest()
    meta = json.loads((ROOT / "reports" / "evidence" / "package.json").read_text()) \
        if (ROOT / "reports" / "evidence" / "package.json").exists() else {}
    gates["evidence_package"] = {"ok": want == got and same_outside_reports(meta.get("commit")) and meta.get("verify_status") == "VERIFIED",
                                 "detail": f"{p.name} sha256 {got[:16]} (recorded {want[:16]}); run {meta.get('run')} "
                                           f"{meta.get('verify_status')}; commit {str(meta.get('commit'))[:12]}"}
else:
    gates["evidence_package"] = {"ok": False, "detail": "no evidence package"}
verdict = "HARDENED_M1_M3_ACCEPTED" if all(g["ok"] for g in gates.values()) else "PARTIAL"
out = {"schema": "rocq2lean-acceptance/1", "verdict": verdict, "head": git("rev-parse", "HEAD").stdout.strip(), "gates": gates,
       "failing": [k for k, g in gates.items() if not g["ok"]]}
(ROOT / "reports" / "acceptance.json").write_text(json.dumps(out, indent=2) + "\n")
for k, g in gates.items():
    print(("PASS " if g["ok"] else "FAIL ") + f"{k}: {g['detail']}")
print(verdict)
sys.exit(0 if verdict == "HARDENED_M1_M3_ACCEPTED" else 2)

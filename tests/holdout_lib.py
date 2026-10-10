"""Shared fresh-holdout runner (milestone freezes after hardening-freeze-1).

run_holdouts(tag, fixture, record): the fixture's roots were chosen and committed *after* the
annotated freeze tag `tag` (commit recorded in tests/<fixture>/FREEZE). While the implementation
equals the freeze they are unseen holdouts (record reports/<record>.json); once a later milestone
changes the implementation they run as regression tests (record reports/<record>_regression.json).
Every root runs alone through the public CLI (inspect, export, translate, verify, status), so each
outcome is recorded independently and as observed, never relabelled.
"""
import json
import shutil
import subprocess
from pathlib import Path

from lib import ROOT, check, cli, results

IMPL = ["Rocq2Lean", "Rocq2Lean.lean", "tools", "rocq/exporter", "rocq/roundtrip", "lakefile.lean", "lake-manifest.json",
        "lean-toolchain", "toolchains.lock.json", "scripts/rocq2lean"]


def git(*a):
    return subprocess.run(["git", "-C", str(ROOT), *a], capture_output=True, text=True)


def run_holdouts(tag, fixture, record, tests_dir):
    want = (Path(tests_dir) / "FREEZE").read_text().split()[0]
    got = git("rev-parse", f"{tag}^{{commit}}").stdout.strip()
    check(got == want, f"freeze tag {tag} names the recorded commit {want[:12]} (found {got[:12] or 'none'})")
    check(git("cat-file", "-t", tag).stdout.strip() == "tag", f"{tag} is an annotated tag")
    diff = git("diff", "--stat", want, "--", *IMPL).stdout.strip()
    untracked = git("ls-files", "--others", "--exclude-standard", "--", *IMPL).stdout.split()
    role = "fresh-holdout" if diff == "" and not untracked else "regression"
    if role == "fresh-holdout":
        check(True, f"implementation identical to {tag} (committed and working tree): fresh-holdout role")
    else:
        print(f"NOTE implementation changed since {tag}: roots run as regression tests")
    first = git("log", "--diff-filter=A", "--format=%H", "--", f"fixtures/{fixture}").stdout.split()
    check(bool(first) and git("merge-base", "--is-ancestor", want, first[-1]).returncode == 0 and first[-1] != want,
          f"fixtures/{fixture} first committed after the freeze commit")
    man = ROOT / "fixtures" / fixture / "manifest.json"
    roots = json.loads((ROOT / "fixtures" / fixture / "roots.json").read_text())
    out = {"schema": "rocq2lean-holdout/2", "tag": tag, "freeze": want, "role": role, "roots": {}}
    for r in roots:
        run = ROOT / "runs" / f"{fixture}-{r.split('.')[-1]}"
        shutil.rmtree(run, ignore_errors=True)
        rc_i, txt = cli("inspect", "--manifest", man, "--roots", r)
        pre = json.loads(txt[:txt.rindex("}") + 1]) if "}" in txt else {"roots": {}}
        pv = pre["roots"].get(r, {})
        rcs = {"export": cli("export", "--manifest", man, "--roots", r, "--out", run)[0]}
        rcs["translate"] = cli("translate", "--input", run / "source.ndjson", "--out", run)[0] if rcs["export"] == 0 else None
        rcs["verify"] = cli("verify", "--run", run)[0] if rcs["translate"] == 0 else None
        rcs["status"] = cli("status", "--run", run)[0] if rcs["verify"] == 0 else None
        R = results(run)[0] if (run / "translation_report.json").exists() else {}
        v = json.loads((run / "verify.json").read_text()) if (run / "verify.json").exists() else {}
        out["roots"][r] = {"preflight": pv.get("status"), "preflight_reasons": pv.get("reasons"),
                           "preflight_path": pv.get("dependency_path"), "translation": R.get(r, {}).get("status"),
                           "message": R.get(r, {}).get("message", "")[:300], "exit_codes": rcs,
                           "verified": rcs["verify"] == 0 and rcs["status"] == 0,
                           "closure": v.get("required_closure_size")}
    rec = record if role == "fresh-holdout" else record + "_regression"
    (ROOT / "reports" / (rec + ".json")).parent.mkdir(parents=True, exist_ok=True)
    (ROOT / "reports" / (rec + ".json")).write_text(json.dumps(out, indent=2) + "\n")
    for r, v in out["roots"].items():
        check(v["verified"], f"holdout {r}: preflight {v['preflight']}, translation {v['translation']}, "
                             f"verified={v['verified']} (closure {v['closure']}) {v['message'][:100]}")
    return out

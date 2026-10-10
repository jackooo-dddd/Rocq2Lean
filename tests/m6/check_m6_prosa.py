"""M6 Prosa regression (long-running; not part of test-all). Fixed requests from
fixtures/m6/regression/*.json, each in its own fresh run, against the current implementation:

* behavior61          the 61 M6.1/M6.2 lemmas                                   must VERIFY
* finishtime4         the four FinishTime roots verified at 43baae6              must VERIFY
* holdout13_prosa     the 13 translated roots of the original Prosa holdout      must VERIFY
* holdout14_mathcomp  the MathComp holdouts                                      must VERIFY
* holdout20_prosa     the original 20-root Prosa holdout request: its complete outcome (failures
                      included) is recorded; it must NOT be reported VERIFIED while any root is blocked
The completion gate for all five FinishTime roots is scripts/m6-finishtime-gate (separate, strict).
Results: reports/m6/m6_prosa_results.json (per run: roots, closure, statuses, verify, binding).
"""
import hashlib
import json
import shutil
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from lib import ROOT, check, cli, finish  # noqa: E402

if not (ROOT / ".work" / "prosa-0.6-rocq93" / "analysis" / "facts" / "behavior" / "all.vo").exists():
    subprocess.run([str(ROOT / "scripts" / "setup-prosa"), "--full"], check=True)
REG = ROOT / "fixtures" / "m6" / "regression"
OUT = {"git_head": subprocess.run(["git", "-C", str(ROOT), "rev-parse", "HEAD"], capture_output=True, text=True).stdout.strip(),
       "git_dirty": bool(subprocess.run(["git", "-C", str(ROOT), "status", "--porcelain"], capture_output=True, text=True).stdout.strip()),
       "runs": {}}


def run(name):
    req = json.loads((REG / f"{name}.json").read_text())
    d = ROOT / "runs" / f"m6p-{name}"
    shutil.rmtree(d, ignore_errors=True)
    rcs = {"export": cli("export", "--manifest", ROOT / req["manifest"], "--roots", ",".join(req["roots"]), "--out", d)[0]}
    if rcs["export"] == 0:
        rcs["translate"] = cli("translate", "--input", d / "source.ndjson", "--out", d)[0]
        rcs["verify"] = cli("verify", "--run", d)[0]
        rcs["status"] = cli("status", "--run", d)[0]
    rep = json.loads((d / "translation_report.json").read_text()) if (d / "translation_report.json").exists() else {}
    st = {x["source"]: x for x in rep.get("results", [])}
    ver = json.loads((d / "verify.json").read_text()) if (d / "verify.json").exists() else {}
    kinds = {}
    src = d / "source.ndjson"
    if src.exists():
        for l in open(src):
            x = json.loads(l)
            if x.get("kind") == "constant":
                kinds[x["name"]] = "definition" if x["body_state"] in ("transparent", "sealed_implementation") else "theorem/opaque"
            elif x.get("kind") == "inductive":
                kinds[x["name"]] = "inductive"
    accepted = [s for s, x in st.items() if x["status"] == "TRANSLATED_AND_CHECKED"]
    res = {"request": name, "roots": {r: st.get(r, {}).get("status") for r in req["roots"]}, "exit_codes": rcs,
           "verify": ver.get("status"), "required_closure": ver.get("required_closure_size"),
           "accepted_by_kind": {k: sum(1 for s in accepted if kinds.get(s) == k) for k in ("definition", "theorem/opaque", "inductive")},
           "blocked_root_causes": {s: {"status": x["status"], "message": x["message"][:200]} for s, x in st.items()
                                   if x["status"] not in ("TRANSLATED_AND_CHECKED", "BOOTSTRAP_RESOLVED", "BLOCKED_DEPENDENCY")},
           "source_ir_sha256": hashlib.sha256(src.read_bytes()).hexdigest() if src.exists() else None}
    OUT["runs"][name] = res
    return res


for name in ("behavior61", "finishtime4", "holdout13_prosa", "holdout14_mathcomp"):
    r = run(name)
    ok = r["verify"] == "VERIFIED" and r["exit_codes"].get("status") == 0 and all(v == "TRANSLATED_AND_CHECKED" for v in r["roots"].values())
    check(ok, f"{name}: {len(r['roots'])} roots VERIFIED_CURRENT (closure {r['required_closure']}) {r['exit_codes']}")
r = run("holdout20_prosa")
n_ok = sum(1 for v in r["roots"].values() if v == "TRANSLATED_AND_CHECKED")
check(r["verify"] != "VERIFIED" if n_ok < len(r["roots"]) else r["verify"] == "VERIFIED",
      f"holdout20_prosa (original request): {n_ok}/{len(r['roots'])} roots translated; reported as "
      f"{r['verify']} (never VERIFIED while a root is blocked); complete outcome recorded")
(ROOT / "reports" / "m6" / "m6_prosa_results.json").write_text(json.dumps(OUT, indent=2) + "\n")
finish("test-m6-prosa")

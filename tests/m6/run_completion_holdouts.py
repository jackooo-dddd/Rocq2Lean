"""Run the M6-completion holdouts (reports/m6/holdout_completion_selection.json) ONCE on the frozen
implementation. Each request runs in its own fresh run; its complete outcome is recorded
(reports/m6/holdout_completion_results.json): per-root status, blocked causes, verify, closure, the
binding. A request is VERIFIED only if every root is translated; then the translated subset is not
re-run here (a failing request's outcome is the result).
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

REG = ROOT / "fixtures" / "m6" / "regression"
git = lambda *a: subprocess.run(["git", "-C", str(ROOT), *a], capture_output=True, text=True).stdout.strip()
OUT = {"git_head": git("rev-parse", "HEAD"), "freeze": json.loads((ROOT / "reports" / "m6" / "holdout_completion_selection.json")
                                                                    .read_text())["freeze"], "runs": {}}
for name in ("holdout_completion_prosa", "holdout_completion_mathcomp"):
    req = json.loads((REG / f"{name}.json").read_text())
    d = ROOT / "runs" / f"m6h-{name}"
    shutil.rmtree(d, ignore_errors=True)
    rcs = {"export": cli("export", "--manifest", ROOT / req["manifest"], "--roots", ",".join(req["roots"]), "--out", d)[0]}
    if rcs["export"] == 0:
        rcs["translate"] = cli("translate", "--input", d / "source.ndjson", "--out", d)[0]
        rcs["verify"] = cli("verify", "--run", d)[0]
        rcs["status"] = cli("status", "--run", d)[0]
    rep = json.loads((d / "translation_report.json").read_text()) if (d / "translation_report.json").exists() else {}
    st = {x["source"]: x for x in rep.get("results", [])}
    ver = json.loads((d / "verify.json").read_text()) if (d / "verify.json").exists() else {}
    # (report names of module-nested declarations use '/' where the request uses '.')
    by_dotted = {s.replace("/", "."): x for s, x in st.items()}
    roots = {r: by_dotted.get(r, {}).get("status") for r in req["roots"]}
    src = d / "source.ndjson"
    OUT["runs"][name] = {
        "roots": roots, "translated": sum(1 for v in roots.values() if v == "TRANSLATED_AND_CHECKED"),
        "requested": len(roots), "exit_codes": rcs, "verify": ver.get("status"), "reason": (ver.get("reason") or "")[:300],
        "required_closure": ver.get("required_closure_size"),
        "blocked_causes": {s: {"status": x["status"], "message": x["message"][:200]} for s, x in st.items()
                           if x["status"] not in ("TRANSLATED_AND_CHECKED", "BOOTSTRAP_RESOLVED", "BLOCKED_DEPENDENCY")},
        "source_ir_sha256": hashlib.sha256(src.read_bytes()).hexdigest() if src.exists() else None}
    r = OUT["runs"][name]
    print(f"{name}: {r['translated']}/{r['requested']} roots translated; verify {r['verify']} (closure {r['required_closure']})")
    for s, c in r["blocked_causes"].items():
        print(f"  {c['status']} {s}: {c['message'][:150]}")
(ROOT / "reports" / "m6" / "holdout_completion_results.json").write_text(json.dumps(OUT, indent=2) + "\n")

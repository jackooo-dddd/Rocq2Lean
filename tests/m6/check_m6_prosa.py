"""M6 Prosa v0.6 (original release + compat/prosa-0.6 patches, built by scripts/setup-prosa under the
fixed toolchain): genuine Prosa theorems with their full closures, original proofs kernel-checked.

* M6.1/M6.2: the 61 behavior lemmas of prosa.analysis.facts.behavior.{arrivals,service,completion}
  that the current rules support (reports/m6/behavior61.json lists them), VERIFIED.
* M6.3: prosa.analysis.definitions.finish_time: finish_time, finished_at_finish_time,
  earliest_finish_time, response_time (through MathComp ex_minn / find_ex_minn, accessibility
  lowering), VERIFIED; completes_at_finish_time is reported with its blocker (lia's micromega closure).
Long-running (exports of large closures): not part of test-all.
"""
import json
import shutil
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from lib import ROOT, check, cli, finish, results  # noqa: E402

MAN = ROOT / "fixtures" / "m6" / "manifest.json"
if not (ROOT / ".work" / "prosa-0.6-rocq93" / "analysis" / "facts" / "behavior" / "completion.vo").exists():
    subprocess.run([str(ROOT / "scripts" / "setup-prosa"), "--full"], check=True)
OUT = {}


def pipeline(name, roots):
    run = ROOT / "runs" / name
    shutil.rmtree(run, ignore_errors=True)
    rcs = [cli("export", "--manifest", MAN, "--roots", ",".join(roots), "--out", run)[0]]
    rcs.append(cli("translate", "--input", run / "source.ndjson", "--out", run)[0] if rcs[0] == 0 else None)
    rcs.append(cli("verify", "--run", run)[0] if rcs[1] == 0 else None)
    v = json.loads((run / "verify.json").read_text()) if (run / "verify.json").exists() else {}
    R = results(run)[0] if (run / "translation_report.json").exists() else {}
    OUT[name] = {"roots": {r: R.get(r, {}).get("status") for r in roots}, "exit_codes": rcs,
                 "required_closure": v.get("required_closure_size")}
    return rcs, R, v


B = json.loads((ROOT / "reports" / "m6" / "behavior61.json").read_text())["roots"]
rcs, R, v = pipeline("m6p-behavior", B)
check(rcs == [0, 0, 0], f"M6.1/M6.2: {len(B)} Prosa behavior lemmas VERIFIED (closure {v.get('required_closure_size')}) {rcs}")
F = "prosa.analysis.definitions.finish_time"
FT = [f"{F}.{n}" for n in ("finish_time", "finished_at_finish_time", "earliest_finish_time", "response_time")]
rcs, R, v = pipeline("m6p-finishtime", FT)
check(rcs == [0, 0, 0], f"M6.3: Prosa finish_time, finished_at_finish_time, earliest_finish_time, response_time VERIFIED "
                        f"(closure {v.get('required_closure_size')}) {rcs}")
rc, out = cli("inspect", "--manifest", MAN, "--roots", f"{F}.completes_at_finish_time")
rep = json.loads(out[out.index("{"):out.rindex("}") + 1]) if "{" in out else {"roots": {}}
blk = rep["roots"].get(f"{F}.completes_at_finish_time", {})
OUT["completes_at_finish_time"] = blk
print(f"NOTE completes_at_finish_time: {blk.get('status')} {blk.get('reasons')} via "
      f"{' -> '.join(x.split('.')[-1] for x in blk.get('dependency_path', []))}")
(ROOT / "reports" / "m6" / "m6_prosa_results.json").write_text(json.dumps(OUT, indent=2) + "\n")
finish("test-m6-prosa")

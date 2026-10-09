"""Assumption auditing, isolated: the forged target module and the report are *synchronized*
(the module is built by replaying the mutated report), so the only fault is an axiom in the
transitive dependencies of an accepted declaration. The consumer's `axioms` detector must fire."""
import copy
import hashlib
import json
import os
import shutil
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from lib import ROOT, check, cli, finish  # noqa: E402

MAN = ROOT / "fixtures" / "m3" / "manifest.json"
BASE = ROOT / "runs" / "as-base"
shutil.rmtree(BASE, ignore_errors=True)
assert cli("export", "--manifest", MAN, "--roots", "M3.M3Fix.addR_RS", "--out", BASE)[0] == 0
assert cli("translate", "--input", BASE / "source.ndjson", "--out", BASE)[0] == 0
rc, _ = cli("verify", "--run", BASE)
check(rc == 0, "positive control VERIFIED; consumer axioms detector OK on the genuine module")
ROOT_DECL = "M3.M3Fix.addR_RS"
lenv = dict(os.environ, PATH=f"{Path.home()}/.elan/bin:" + os.environ["PATH"])


def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def forge(name, prelude, value_of):
    d = ROOT / "runs" / f"as-{name}"
    shutil.rmtree(d, ignore_errors=True)
    shutil.copytree(BASE, d, ignore=shutil.ignore_patterns(".rocq2lean.lock", "verify.json", "audit.json", "consumer_result.json"))
    rep = json.loads((d / "translation_report.json").read_text())
    r = next(x for x in rep["results"] if x["source"] == ROOT_DECL)
    r["target_value"] = value_of(r["target_type"])
    (d / "translation_report.json").write_text(json.dumps(rep))
    lean = d / "lean"
    for f in lean.glob("Rocq2LeanOut.*"):
        f.unlink()
    (lean / "Rocq2LeanOut.lean").write_text(
        f'import Rocq2Lean\n{prelude}\n#rocq2lean_replay "{d / "translation_report.json"}" "{lean / "replay.json"}"\n')
    p = subprocess.run(["lake", "-d", str(ROOT), "env", "lean", "Rocq2LeanOut.lean", "-o", "Rocq2LeanOut.olean",
                        "-i", "Rocq2LeanOut.ilean"], cwd=lean, capture_output=True, text=True, env=lenv)
    replayed = json.loads((lean / "replay.json").read_text())["results"]
    kernel_ok = all(x["kernel"] == "ACCEPTED" for x in replayed)
    tm = json.loads((d / "translation_manifest.json").read_text())
    tm.update(report_sha256=sha(d / "translation_report.json"), module_lean_sha256=sha(lean / "Rocq2LeanOut.lean"),
              module_olean_sha256=sha(lean / "Rocq2LeanOut.olean"), module_ilean_sha256=sha(lean / "Rocq2LeanOut.ilean"))
    (d / "translation_manifest.json").write_text(json.dumps(tm))
    rc, out = cli("verify", "--run", d)
    c = json.loads((d / "consumer_result.json").read_text())
    return p.returncode, kernel_ok, rc, c


def app(f, a):
    return {"k": "app", "f": f, "a": a}


def const(n, u=()):
    return {"k": "const", "n": n, "u": list(u)}


Z = {"k": "zero"}
for name, prelude, value_of, needle in (
        ("custom-axiom", "axiom r2l_injected : False",
         lambda T: app(app(const("False.elim", [Z]), T), const("r2l_injected")), "r2l_injected"),
        ("sorryAx", "", lambda T: app(app(const("sorryAx", [Z]), T), const("Bool.false")), "sorryAx")):
    lean_rc, kernel_ok, rc, c = forge(name, prelude, value_of)
    det = c["detectors"]
    msgs = [p["message"] for p in c["problems"] if p["detector"] == "axioms"]
    check(lean_rc == 0 and kernel_ok, f"[{name}] forged module builds; every declaration kernel-accepted (synchronized forgery)")
    check(det.get("value") == "OK" and det.get("type") == "OK" and det.get("coverage") == "OK" and det.get("presence") == "OK",
          f"[{name}] report and module agree (value/type/coverage/presence detectors OK)")
    check(rc != 0 and det.get("axioms") == "FAIL" and any(needle in m for m in msgs),
          f"[{name}] the axioms detector rejects it: {msgs[:1]}")
finish("test-assumptions")

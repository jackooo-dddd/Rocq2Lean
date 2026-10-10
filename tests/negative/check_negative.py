"""Negative suite (prompt §9): every mutation must be rejected, some of them outside the kernel."""
import json
import os
import shutil
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from lib import ROOT, check, cli, results, finish, SWITCH  # noqa: E402

BASE = ROOT / "runs" / "neg-base"
MAN = ROOT / "fixtures" / "m3" / "manifest.json"
ROOTS = ["M3.M3Proofs.mirror_mirror", "M3.M3Fix.addR_RS"]
shutil.rmtree(BASE, ignore_errors=True)
assert cli("export", "--manifest", MAN, "--roots", ",".join(ROOTS), "--out", BASE)[0] == 0
assert cli("translate", "--input", BASE / "source.ndjson", "--out", BASE)[0] == 0
assert cli("verify", "--run", BASE)[0] == 0
LINES = [json.loads(l) for l in open(BASE / "source.ndjson")]


def mutated(name, mutate):
    """Translate a mutated copy of the IR; returns (exit code, results)."""
    run = ROOT / "runs" / f"neg-{name}"
    shutil.rmtree(run, ignore_errors=True)
    run.mkdir(parents=True)
    lines = mutate(json.loads(json.dumps(LINES)))
    (run / "source.ndjson").write_text("".join(json.dumps(d) + "\n" for d in lines))
    rc, out = cli("translate", "--input", run / "source.ndjson", "--out", run)
    try:
        R, _ = results(run)
    except FileNotFoundError:
        R = {}
    return rc, R, out, run


def decl(lines, name):
    return next(d for d in lines if d.get("name") == name)


# 1. Missing opaque body in a *dependency* (the root's own body is present).
def drop_dep_body(lines):
    d = decl(lines, "M3.M3Fix.mirrorR")
    d["body"], d["body_state"] = None, "unavailable"
    return lines
rc, R, _, _ = mutated("dep-body", drop_dep_body)
check(rc != 0 and R["M3.M3Fix.mirrorR"]["status"] == "BLOCKED_SOURCE_BODY"
      and R["M3.M3Proofs.mirror_mirror"]["status"] == "BLOCKED_DEPENDENCY",
      "missing body in a required dependency blocks the root (no axiom)")


# 2. Missing dependency declaration.
def drop_dep(lines):
    lines = [d for d in lines if d.get("name") != "M3.M3Types.Tree_ind"]
    lines[-1]["declarations"] -= 1
    return lines
rc, R, _, _ = mutated("missing-dep", drop_dep)
check(rc != 0 and R["M3.M3Proofs.mirror_mirror"]["status"] == "EXPORT_VALIDATION_FAILED",
      "dependency absent from the export is reported, not skipped")


# 3. Malformed de Bruijn index.
def bad_index(lines):
    d = decl(lines, "M3.M3Fix.addR_RS")
    d["body"]["b"]["b"]["args"][1] = {"k": "rel", "i": 7}
    return lines
rc, R, _, _ = mutated("bad-index", bad_index)
check(rc != 0 and R["M3.M3Fix.addR_RS"]["status"] == "EXPORT_VALIDATION_FAILED"
      and "out of scope" in R["M3.M3Fix.addR_RS"]["message"], "malformed (out-of-scope) index rejected with node path")


# 4. Reordered constructors in the source declaration: the kernel accepts the reordered type, but
#    the round trip against the original environment must reject the IR.
def reorder(lines):
    b = decl(lines, "M3.M3Types.Tree")["bodies"][0]
    b["ctors"].reverse()
    return lines
rc, R, _, run = mutated("reorder", reorder)
env = dict(os.environ, PATH=f"{Path.home()}/.local/bin:" + os.environ["PATH"])
p = subprocess.run(["opam", "exec", "--switch=" + SWITCH, "--", sys.executable, "-I", str(ROOT / "tools" / "roundtrip.py"),
                    str(run / "source.ndjson"), str(run / "rt"), "-Q", str(ROOT / "fixtures" / "m3"), "M3", "--",
                    "M3.M3Proofs", "M3.M3Fix"], capture_output=True, text=True, env=env)
check(p.returncode != 0 and "M3.M3Types.Tree: RT_MISMATCH" in p.stdout, "reordered constructors detected by the round trip")
check(rc != 0, "reordered constructors also break the dependent translation")


# 5. Incompatible universe: Prop inductive turned into a large sort mismatch (kernel must reject).
def bad_universe(lines):
    d = decl(lines, "M3.M3Fix.addR_RS")
    d["type"]["ty"] = {"k": "sort", "s": {"k": "prop"}}      # forall (n : Prop) ...
    return lines
rc, R, _, _ = mutated("universe", bad_universe)
check(rc != 0 and R["M3.M3Fix.addR_RS"]["status"] in ("KERNEL_REJECTED", "TRANSLATION_FAILED"),
      f"ill-typed universe change rejected ({R['M3.M3Fix.addR_RS']['status']})")


# 6. Type-incorrect proof (kernel rejection path).
def wrong_proof(lines):
    d = decl(lines, "M3.M3Fix.addR_RS")
    d["body"]["b"]["b"]["args"][1] = {"k": "rel", "i": 0}    # eq_refl m instead of eq_refl (addR (RS n) m)
    return lines
rc, R, _, _ = mutated("wrong-proof", wrong_proof)
check(rc != 0 and R["M3.M3Fix.addR_RS"]["status"] == "KERNEL_REJECTED", "wrong proof term rejected by the Lean kernel")


# 7. Injected custom axiom / forged module: consumer must reject.
forge = ROOT / "runs" / "neg-forge"
shutil.rmtree(forge, ignore_errors=True)
shutil.copytree(BASE, forge)
snap = json.loads((forge / "source_snapshot.json").read_text())
(forge / "source_snapshot.json").write_text(json.dumps(snap))
rep = json.loads((forge / "translation_report.json").read_text())
lean_dir = forge / "lean"
(lean_dir / "Rocq2LeanOut.lean").write_text(
    "import Rocq2Lean\n" + open(BASE / "lean" / "Rocq2LeanOut.lean").read().split("\n", 1)[1].replace(
        str(BASE / "translation_report.json"), str(forge / "report_unused.json")) +
    "axiom r2l_injected : False\n"
    "theorem r2l_uses_injected : True := r2l_injected.elim\n")
lenv = dict(os.environ, PATH=f"{Path.home()}/.elan/bin:" + os.environ["PATH"])
subprocess.run(["lake", "-d", str(ROOT), "env", "lean", "Rocq2LeanOut.lean", "-o", "Rocq2LeanOut.olean"],
               cwd=lean_dir, env=lenv, capture_output=True)
rep["results"].append({"source": "M3.M3Fix.addR_RS", "kind": "constant", "status": "TRANSLATED_AND_CHECKED",
                       "rule": "forged", "target": "r2l_uses_injected", "target_kind": "theorem", "message": "",
                       "path": [], "blocked_by": [], "level_params": [], "target_ctors": [],
                       "target_type": {"k": "const", "n": "True", "u": []},
                       "target_value": {"k": "const", "n": "True.intro", "u": []}})
(forge / "translation_report.json").write_text(json.dumps(rep))
rc, out = cli("verify", "--run", forge)
check(rc != 0, "forged report with an injected custom axiom is rejected by verify")

# 8. Stale artifacts: a failing translation in a directory holding a previous successful .olean.
stale = ROOT / "runs" / "neg-stale"
shutil.rmtree(stale, ignore_errors=True)
shutil.copytree(BASE, stale)
lines = wrong_proof(json.loads(json.dumps(LINES)))
(stale / "source.ndjson").write_text("".join(json.dumps(d) + "\n" for d in lines))
rc, _ = cli("translate", "--input", stale / "source.ndjson", "--out", stale)
check(rc != 0 and not (stale / "lean" / "Rocq2LeanOut.olean").exists(), "stale .olean removed; failing input stays failed")
rc, _ = cli("verify", "--run", stale)
check(rc != 0, "verify refuses a run whose IR no longer matches its anchored snapshot")

# 9. Skipped requested root: export of a root that does not exist must fail, not be dropped.
rc, out = cli("export", "--manifest", MAN, "--roots", "M3.M3Fix.addR_RS,M3.M3Fix.no_such_lemma",
              "--out", ROOT / "runs" / "neg-skip")
check(rc != 0, "a requested root that does not exist fails the export (never silently skipped)")

# 10. Genuine source assumption and relaxed checking are covered in test-m1; unsupported recursion in test-m3.
finish("test-negative")

"""M2: structural expression translation, with target- and source-side mutation tests."""
import json
import shutil
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from lib import ROOT, audit_report, check, cli, decls, results, finish, structurally_rejected, SWITCH  # noqa: E402

MAN = ROOT / "fixtures" / "m2" / "manifest.json"
ROOTS = ["M2.M2A.prop_id", "M2.M2A.twice_succ", "M2.M2A.first_second", "M2.M2A.vm_proof",
         "M2.M2A.change_proof", "M2.M2A.nested_let", "M2.M2A.let_in_type", "M2.M2A.dep_pair",
         "M2.M2A.dep_use", "M2.M2A.shadow_inner", "M2.M2B.f_values", "M2.M2B.f_values_b"]
run = ROOT / "runs" / "m2"
shutil.rmtree(run, ignore_errors=True)
rc, _ = cli("export", "--manifest", MAN, "--roots", ",".join(ROOTS), "--out", run)
check(rc == 0, "M2 export + round trip")
rc, _ = cli("translate", "--input", run / "source.ndjson", "--out", run)
check(rc == 0, "all M2 roots TRANSLATED_AND_CHECKED")
rc, _ = cli("verify", "--run", run)
check(rc == 0, "M2 run VERIFIED (consumer + independent audit)")
D = decls(run / "source.ndjson")
R, rep = results(run)


def count(e, k):
    if isinstance(e, dict):
        return (e.get("k") == k) + sum(count(v, k) for v in e.values())
    if isinstance(e, list):
        return sum(count(v, k) for v in e)
    return 0


check(count(D["M2.M2A.nested_let"]["body"], "let") == 3 == count(R["M2.M2A.nested_let"]["target_value"], "let"),
      "all three (shadowing) lets preserved")
check(count(D["M2.M2A.vm_proof"]["body"], "cast") >= 1 and count(R["M2.M2A.vm_proof"]["target_value"], "mdata") == 0,
      "kernel vm cast present in source, validated and erased in target")
check(R["M2.M2A.f"]["target"] == "Rocq.M2.M2A.f" and R["M2.M2B.f"]["target"] == "Rocq.M2.M2B.f",
      "identical short names in different modules get distinct targets")
sp = R["M2.M2A.shadow_params"]["target_value"]
check(sp["k"] == "lam" and sp["b"]["k"] == "lam" and sp["b"]["b"] == {"k": "bvar", "i": 0},
      "identical binder names: inner binder referenced (bvar 0)")
check(R["M2.M2A.pick_first"]["target_value"]["b"]["b"] == {"k": "bvar", "i": 1}
      and R["M2.M2A.pick_second"]["target_value"]["b"]["b"] == {"k": "bvar", "i": 0},
      "same-typed functions keep their distinct bodies")


def audit_with(mutate, name, decl):
    """The auditor must reject the mutated report through its structural detector on `decl`."""
    rep2 = json.loads((run / "translation_report.json").read_text())
    by = {r["source"]: r for r in rep2["results"]}
    mutate(by)
    return structurally_rejected(run, rep2, name, decl)


rc, probs = audit_report(run, json.loads((run / "translation_report.json").read_text()), "unmutated")
check(rc == 0 and not probs, "audit positive control: unmutated M2 report accepted")


def swap_picks(by):
    a, b = by["M2.M2A.pick_first"], by["M2.M2A.pick_second"]
    a["target_value"], b["target_value"] = b["target_value"], a["target_value"]


check(audit_with(swap_picks, "swap", "M2.M2A.pick_first"), "audit rejects swapped same-typed bodies (type-correct mutation)")


def unrelated_true(by):
    by["M2.M2A.dep_use"]["target_value"] = {"k": "const", "n": "True.intro", "u": []}


check(audit_with(unrelated_true, "true", "M2.M2A.dep_use"), "audit rejects an unrelated True proof substituted for a declaration")


def swap_args(by):
    v = by["M2.M2A.compose"]["target_value"]          # fun f g x => f (g x)
    v["b"]["b"]["b"]["f"] = {"k": "bvar", "i": 1}    # -> g (g x)
check(audit_with(swap_args, "args", "M2.M2A.compose"), "audit rejects a swapped variable inside a body")

# Source-IR mutation against the anchored snapshot: same-typed swap in pick_first.
mut = ROOT / "runs" / "m2-srcmut"
shutil.rmtree(mut, ignore_errors=True)
shutil.copytree(run, mut)
snap = json.loads((mut / "source_snapshot.json").read_text())
snap["ir"] = str(mut / "source.ndjson")
(mut / "source_snapshot.json").write_text(json.dumps(snap))
lines = [json.loads(l) for l in open(mut / "source.ndjson")]
for d in lines:
    if d.get("name") == "M2.M2A.pick_first":
        d["body"]["b"]["b"] = {"k": "rel", "i": 0}
(mut / "source.ndjson").write_text("".join(json.dumps(d) + "\n" for d in lines))
rc, out = cli("verify", "--run", mut)
check(rc != 0 and "source IR changed" in out, "verify rejects a source IR that differs from the anchored snapshot")
oenv_cmd = ["opam", "exec", "--switch=" + SWITCH, "--", sys.executable, "-I", str(ROOT / "tools" / "roundtrip.py"),
            str(mut / "source.ndjson"), str(mut / "rt"), "-Q", str(ROOT / "fixtures" / "m2"), "M2", "--",
            "M2.M2A", "M2.M2B"]
p = subprocess.run(oenv_cmd, capture_output=True, text=True,
                   env={**__import__("os").environ, "PATH": f"{Path.home()}/.local/bin:" + __import__("os").environ["PATH"]})
check(p.returncode != 0 and "M2.M2A.pick_first" in p.stdout, "independent round trip flags the mutated declaration")
finish("test-m2")

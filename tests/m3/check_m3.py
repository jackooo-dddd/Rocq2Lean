"""M3: inductives (a), case lowering (b), fix lowering (c), original induction proofs (d)."""
import copy
import json
import shutil
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from lib import ROOT, audit_report, check, cli, decls, results, finish, structurally_rejected  # noqa: E402

MAN = ROOT / "fixtures" / "m3" / "manifest.json"
STAGES = {
    "m3a": ["M3.M3Types." + n for n in ("RNat", "RList", "Tree", "Vec")],
    "m3b": ["M3.M3Case." + n for n in ("pred_r_RS", "pred_nat_S", "head_or_cons", "vid_cons", "vtail_cons",
                                        "eq_sym_nat", "tree_root_or")],
    "m3c": ["M3.M3Fix." + n for n in ("addR_RZ", "addR_RS", "lengthR_nil", "lengthR_cons", "mirrorR_node",
                                       "addAcc_RS", "vmap_cons", "double_nat_S", "addR_2_1", "mirror_small", "mapR")],
    "m3d": ["M3.M3Proofs." + n for n in ("addR_n_RZ", "length_map", "mirror_mirror", "vmap_id", "vid_id")],
}


def pipeline(name, roots):
    run = ROOT / "runs" / name
    shutil.rmtree(run, ignore_errors=True)
    rcs = [cli("export", "--manifest", MAN, "--roots", ",".join(roots), "--out", run)[0],
           cli("translate", "--input", run / "source.ndjson", "--out", run)[0],
           cli("verify", "--run", run)[0]]
    return run, rcs


runs = {}
for stage, roots in STAGES.items():
    run, rcs = pipeline(stage, roots)
    runs[stage] = run
    check(rcs == [0, 0, 0], f"{stage}: export + translate + VERIFIED ({len(roots)} roots)")

R, _ = results(runs["m3a"])
check(all(R[n]["target_kind"] == "inductive" for n in STAGES["m3a"]), "M3a: fresh Lean inductives generated (not aliases)")
check([c["name"].split(".")[-1] for c in R["M3.M3Types.Tree"]["target_ctors"]] == ["Leaf", "Node"],
      "M3a: constructor order preserved")


def mentions(e, name):
    return json.dumps(e).find(f'"n": "{name}"') >= 0 or json.dumps(e).find(f'"n":"{name}"') >= 0


R, _ = results(runs["m3c"])
check(mentions(R["M3.M3Fix.mirrorR"]["target_value"], "Rocq.M3.M3Types.Tree.rec"),
      "M3c: mirrorR lowered to the kernel-generated Tree.rec (no self reference)")
check(mentions(R["M3.M3Fix.double_nat"]["target_value"], "Nat.rec"), "M3c: recursion through bootstrap Nat.rec")


# Mutation: swap the two recursive results in mirrorR's Node minor. Type-correct; audit must reject.
def swap_tree_results(e):
    if isinstance(e, dict):
        if e.get("k") == "bvar" and e["i"] in (2, 3) and e.get("_m") is None:
            pass
        for v in e.values():
            swap_tree_results(v)
    return e


run = runs["m3c"]
rep = json.loads((run / "translation_report.json").read_text())
mr = next(r for r in rep["results"] if r["source"] == "M3.M3Fix.mirrorR")
s = json.dumps(mr["target_value"])
# In the Node minor (fields l x r, results ihl ihr, no Q), the body is Node (ihr) x (ihl): bvar 0 and bvar 1.
swapped = s.replace('{"k": "bvar", "i": 0}', "@@").replace('{"k": "bvar", "i": 1}', '{"k": "bvar", "i": 0}').replace("@@", '{"k": "bvar", "i": 1}')
check(swapped != s, "M3c mutation constructed (swap mirrorR recursive results)")
mr["target_value"] = json.loads(swapped)
rc, probs = audit_report(run, json.loads((run / "translation_report.json").read_text()), "unmutated")
check(rc == 0 and not probs, "audit positive control: unmutated M3c report accepted")
check(structurally_rejected(run, rep, "swapped", "M3.M3Fix.mirrorR"),
      "audit rejects mirrorR with its two recursive results swapped (structure detector on mirrorR)")

# Definitional vs propositional laws.
laws = []
for stage, kind in (("m3b", None), ("m3c", None), ("m3d", None)):
    D = decls(runs[stage] / "source.ndjson")
    for n in STAGES[stage]:
        d = D[n]
        if d["kind"] != "constant" or not d["type"] or d["type"].get("k") not in ("prod", "app"):
            continue
        b = d["body"]
        while b["k"] == "lam":
            b = b["b"]
        f = b.get("f", {})
        refl = (b["k"] == "app" and f.get("k") == "construct" and f.get("c") == 0
                and f.get("ind") == {"mind": "Corelib.Init.Logic.eq", "i": 0})
        if "eq" in json.dumps(d["type"]):
            laws.append({"law": n, "kind": "definitional (original eq_refl proof accepted by the Lean kernel)"
                         if refl else "propositional (original proof translated)"})
(ROOT / "reports").mkdir(exist_ok=True)
(ROOT / "reports" / "m3_laws.json").write_text(json.dumps(laws, indent=2) + "\n")
defin = {l["law"] for l in laws if l["kind"].startswith("definitional")}
check({"M3.M3Fix.addR_RZ", "M3.M3Fix.addR_RS", "M3.M3Fix.lengthR_nil", "M3.M3Fix.lengthR_cons"} <= defin,
      "open-variable equations addR RZ m, addR (RS n) m, lengthR nil, lengthR (cons a xs) are definitional in Lean")
check("M3.M3Proofs.addR_n_RZ" not in defin, "addR n RZ = n recorded as propositional (proved by induction)")

# Computation on generated inputs.
p = subprocess.run([sys.executable, "-I", str(ROOT / "tests" / "m3" / "compute.py")], capture_output=True, text=True)
print(p.stdout.strip().splitlines()[-1] if p.stdout.strip() else p.stderr[-500:])
check(p.returncode == 0, "source and target computations agree on generated inputs (constructor encodings)")

# Unsupported patterns are rejected explicitly.
neg = ROOT / "runs" / "m3-neg"
shutil.rmtree(neg, ignore_errors=True)
roots = ["M3.M3Neg." + n for n in ("evenR", "half", "addPre", "Stream", "sprop_id", "pid", "rose_size")]
rc, _ = cli("export", "--manifest", MAN, "--roots", ",".join(roots), "--out", neg)
check(rc == 0, "negative M3 inputs export and round-trip faithfully")
rc, _ = cli("translate", "--input", neg / "source.ndjson", "--out", neg)
R, _ = results(neg)
want = {"Stream": "coinductive", "sprop_id": "SProp"}
for n, msg in want.items():
    r = R["M3.M3Neg." + n]
    check(rc != 0 and r["status"] == "UNSUPPORTED_FEATURE" and msg in r["message"], f"rejected explicitly: {n} ({msg})")
# rose_size (a match on a nested inductive, no recursion through the nesting) was rejected until M6
# completion; trivial auxiliary motives translate it. It must now translate, verify and pass the audit.
rv = ROOT / "runs" / "m3-rose"
shutil.rmtree(rv, ignore_errors=True)
rcs = [cli("export", "--manifest", MAN, "--roots", "M3.M3Neg.rose_size", "--out", rv)[0],
       cli("translate", "--input", rv / "source.ndjson", "--out", rv)[0], cli("verify", "--run", rv)[0]]
check(rcs == [0, 0, 0], f"rose_size (match on a nested inductive, trivial auxiliary motives since M6 completion) VERIFIED {rcs}")
# half (recursion on a field of a field) was rejected until M6 completion; course-of-values recursion
# (docs/SUPPORT_PROFILE.md) translates it. It must now translate, verify and pass the audit on its own.
hv = ROOT / "runs" / "m3-half"
shutil.rmtree(hv, ignore_errors=True)
rcs = [cli("export", "--manifest", MAN, "--roots", "M3.M3Neg.half", "--out", hv)[0],
       cli("translate", "--input", hv / "source.ndjson", "--out", hv)[0], cli("verify", "--run", hv)[0]]
check(rcs == [0, 0, 0], f"half (recursion on a non-direct subterm, course-of-values since M6 completion) VERIFIED {rcs}")
# evenR/oddR (a mutual fixpoint) was rejected until M6 completion; the joint recursor into PProd
# (docs/SUPPORT_PROFILE.md) translates it. It must now translate, verify and pass the audit on its own.
ev = ROOT / "runs" / "m3-evenr"
shutil.rmtree(ev, ignore_errors=True)
rcs = [cli("export", "--manifest", MAN, "--roots", "M3.M3Neg.evenR", "--out", ev)[0],
       cli("translate", "--input", ev / "source.ndjson", "--out", ev)[0], cli("verify", "--run", ev)[0]]
check(rcs == [0, 0, 0], f"evenR (mutual fixpoint, joint recursor since M6 completion) VERIFIED {rcs}")
# addPre (recursion changes the argument k before the decreasing n) was a blocker of the pilot; since M4
# the changed argument is generalized in the motive (docs/SUPPORT_PROFILE.md). It must now translate,
# verify and pass the audit on its own.
ap = ROOT / "runs" / "m3-addpre"
shutil.rmtree(ap, ignore_errors=True)
rcs = [cli("export", "--manifest", MAN, "--roots", "M3.M3Neg.addPre", "--out", ap)[0],
       cli("translate", "--input", ap / "source.ndjson", "--out", ap)[0], cli("verify", "--run", ap)[0]]
check(rcs == [0, 0, 0], f"addPre (changed earlier argument, generalized in the motive since M4) VERIFIED {rcs}")
# pid (universe-polymorphic) was rejected by the pilot; since M6 rule R6 translates universe-polymorphic
# constants (their universe variables become the first Lean universe parameters v_i). It must now be
# accepted in the negative run and verify on its own.
check(R["M3.M3Neg.pid"]["status"] == "TRANSLATED_AND_CHECKED" and R["M3.M3Neg.pid"]["level_params"] == ["v_0"],
      "pid (universe-polymorphic) translated by R6 since M6 (level parameter v_0)")
pp = ROOT / "runs" / "m3-pid"
shutil.rmtree(pp, ignore_errors=True)
rcs = [cli("export", "--manifest", MAN, "--roots", "M3.M3Neg.pid", "--out", pp)[0],
       cli("translate", "--input", pp / "source.ndjson", "--out", pp)[0], cli("verify", "--run", pp)[0]]
check(rcs == [0, 0, 0], f"pid (universe-polymorphic, R6) VERIFIED {rcs}")
finish("test-m3")

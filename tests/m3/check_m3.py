"""M3: inductives (a), case lowering (b), fix lowering (c), original induction proofs (d)."""
import copy
import json
import shutil
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from lib import ROOT, check, cli, decls, results, finish  # noqa: E402

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
(run / "report_swapped.json").write_text(json.dumps(rep))
p = subprocess.run([sys.executable, "-I", str(ROOT / "tools" / "audit.py"), str(run / "source.ndjson"),
                    str(run / "report_swapped.json"), str(run / "audit_swapped.json")], capture_output=True, text=True)
check(p.returncode != 0, "audit rejects mirrorR with its two recursive results swapped (left/right kept distinct)")

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
want = {"evenR": "mutual fixpoint", "half": "not a direct recursive constructor field",
        "addPre": "changes parameter", "Stream": "coinductive", "sprop_id": "SProp", "pid": "universe-polymorphic",
        "rose_size": "mutual or nested"}
for n, msg in want.items():
    r = R["M3.M3Neg." + n]
    check(rc != 0 and r["status"] == "UNSUPPORTED_FEATURE" and msg in r["message"], f"rejected explicitly: {n} ({msg})")
finish("test-m3")

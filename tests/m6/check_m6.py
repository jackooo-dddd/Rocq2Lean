"""M6: translation rules needed by the Prosa closures, on focused fixtures (genuine Rocq/MathComp).

* R6 universe-polymorphic constants (fixtures/poly): VERIFIED; a cumulativity-dependent polymorphic
  definition (plift) is rejected by the kernel; a forged instance argument is rejected by the audit.
* Non-uniform parameters (fixtures/nonuniform): Lean indices + convoy lowering of matches, VERIFIED
  with reflexivity computations; a type-correct branch mutation is kernel-accepted and audit-rejected.
* Accessibility lowering (fixtures/accfix, MathComp ssrnat.find_ex_minn / ex_minn): structural
  recursion on a proof of a two-constructor Prop inductive into data, VERIFIED, with computation
  through the lowering (search P2 0 h0 = 2 by eq_refl); a type-correct result mutation is
  kernel-accepted and audit-rejected.
The long Prosa runs are in scripts/test-m6-prosa.
"""
import json
import shutil
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from lib import ROOT, audit_report, check, cli, finish, forge_run, results  # noqa: E402

RESULTS = {}


def pipeline(name, man, roots):
    run = ROOT / "runs" / name
    shutil.rmtree(run, ignore_errors=True)
    rcs = [cli("export", "--manifest", man, "--roots", ",".join(roots), "--out", run)[0]]
    rcs.append(cli("translate", "--input", run / "source.ndjson", "--out", run)[0] if rcs[0] == 0 else None)
    rcs.append(cli("verify", "--run", run)[0] if rcs[1] == 0 else None)
    R = results(run)[0] if (run / "translation_report.json").exists() else {}
    RESULTS[name] = {"roots": {r: R.get(r, {}).get("status") for r in roots}, "exit_codes": rcs}
    return run, rcs, R


def find(e, pred, path=()):
    """First (path, node) in a Lean expression JSON satisfying pred."""
    if isinstance(e, dict):
        if pred(e):
            return path, e
        for k, v in e.items():
            r = find(v, pred, path + (k,))
            if r:
                return r
    elif isinstance(e, list):
        for i, v in enumerate(e):
            r = find(v, pred, path + (i,))
            if r:
                return r
    return None


def at(e, path):
    for p in path:
        e = e[p]
    return e


def mutation(run, decl, mutate, label):
    """Forge the report of `run` (mutate decl's target value), replay it in the kernel, verify."""
    rep = json.loads((run / "translation_report.json").read_text())
    row = next(x for x in rep["results"] if x["source"] == decl)
    mutate(row["target_value"])
    _, kernel_ok, rc, _, aud = forge_run(run, label, rep)
    struct = [p for p in aud.get("problems", []) if p["message"].startswith(f"{decl}:")]
    RESULTS.setdefault("mutations", []).append({"mutation": label, "declaration": decl,
                                                "kernel": "ACCEPTED" if kernel_ok else "REJECTED",
                                                "verify_exit": rc, "detectors": sorted({p["detector"] for p in struct})})
    return kernel_ok, rc, struct


# --- R6: universe-polymorphic constants
P = "PolyFx.Poly"
run, rcs, R = pipeline("m6-poly", ROOT / "fixtures" / "poly" / "manifest.json",
                       [f"{P}.{n}" for n in ("use_set", "use_lemma", "use_twice_2", "use_glob")])
check(rcs == [0, 0, 0] and R[f"{P}.pid"]["level_params"] == ["v_0"] and R[f"{P}.pcomp"]["level_params"] == ["v_0", "v_1", "v_2"]
      and R[f"{P}.ptwice"]["universe_poly_params"] == 1,
      f"R6: universe-polymorphic pid/pcomp/ptwice/pid_eq and their uses VERIFIED {rcs}")


def raise_instance(v):
    hit = find(v, lambda n: n.get("k") == "const" and n.get("n") == "Rocq.PolyFx.Poly.pid")
    at(v, hit[0])["u"] = [{"k": "succ", "l": {"k": "zero"}}]          # pid.{0} -> pid.{1}


rep = json.loads((run / "translation_report.json").read_text())
raise_instance(next(x for x in rep["results"] if x["source"] == f"{P}.use_set")["target_value"])
rc, probs = audit_report(run, rep, "r6-instance")
check(rc == 1 and any(p["detector"] == "structure" and p["message"].startswith(f"{P}.use_set:") and "source instance" in p["message"]
                      for p in probs),
      "R6: a forged universe argument (not the image of the source instance) is rejected by the audit's structure detector")
neg = ROOT / "runs" / "m6-poly-neg"
shutil.rmtree(neg, ignore_errors=True)
cli("export", "--manifest", ROOT / "fixtures" / "poly" / "manifest.json", "--roots", f"{P}.plift", "--out", neg)
rc, _ = cli("translate", "--input", neg / "source.ndjson", "--out", neg)
check(rc != 0 and results(neg)[0][f"{P}.plift"]["status"] == "KERNEL_REJECTED",
      "R6: plift (needs cumulativity under u < v) rejected by the kernel, not patched")

# --- non-uniform parameters
N = "NU.NonUniform"
run, rcs, R = pipeline("m6-nonuniform", ROOT / "fixtures" / "nonuniform" / "manifest.json",
                       [f"{N}.{n}" for n in ("cd_is_stop_ex", "cd_tail_ex", "accb_inv", "accb_start")])
check(rcs == [0, 0, 0] and R[f"{N}.countdown"]["num_params"] == 0 and R[f"{N}.accb"]["num_params"] == 1,
      f"non-uniform parameters as Lean indices; convoy-lowered matches; reflexivity computations VERIFIED {rcs}")
run1, rcs1, _ = pipeline("m6-nonuniform-fn", ROOT / "fixtures" / "nonuniform" / "manifest.json", [f"{N}.cd_is_stop"])


def swap_branch(v):
    hit = find(v, lambda n: n.get("k") == "const" and n.get("n") == "Rocq.Corelib.Init.Datatypes.bool.true")
    at(v, hit[0])["n"] = "Rocq.Corelib.Init.Datatypes.bool.false"     # cd_stop branch: true -> false


kernel_ok, rc, struct = mutation(run1, f"{N}.cd_is_stop", swap_branch, "convoy-branch")
check(rcs1 == [0, 0, 0] and kernel_ok and rc == 2 and any(p["detector"] == "structure" for p in struct),
      "convoy lowering: a type-correct branch mutation is kernel-accepted and rejected by the structural audit")

# --- accessibility lowering
A = "AF.AccFix"
run, rcs, R = pipeline("m6-accfix", ROOT / "fixtures" / "accfix" / "manifest.json", [f"{A}.search_ex", f"{A}.search_ex1"])
check(rcs == [0, 0, 0], f"accessibility lowering: search (recursion on an accb proof) VERIFIED; search P2 0 h0 = 2 and "
                        f"search P2 1 _ = 2 by eq_refl, i.e. computed by Lean's kernel through Acc.rec {rcs}")
run1, rcs1, _ = pipeline("m6-accfix-fn", ROOT / "fixtures" / "accfix" / "manifest.json", [f"{A}.search"])


def bump_result(v):
    hit = find(v, lambda n: n.get("k") == "lam" and n["b"].get("k") == "proj" and n["b"].get("i") == 0
               and n["b"].get("s") == "PSigma")
    lam = at(v, hit[0])
    lam["b"] = {"k": "app", "f": {"k": "const", "n": "Nat.succ", "u": []}, "a": lam["b"]}    # m -> S m


kernel_ok, rc, struct = mutation(run1, f"{A}.search", bump_result, "acc-result")
check(rcs1 == [0, 0, 0] and kernel_ok and rc == 2 and any(p["detector"] == "structure" for p in struct),
      "accessibility lowering: a type-correct result mutation (m -> S m) is kernel-accepted and rejected by the structural audit")
M = "mathcomp.boot.ssrnat"
run, rcs, R = pipeline("m6-find-ex-minn", ROOT / "fixtures" / "m6" / "mathcomp_manifest.json", [f"{M}.find_ex_minn", f"{M}.ex_minn"])
check(rcs == [0, 0, 0] and R[f"{M}.acc_nat"]["num_params"] == 1,
      f"MathComp ssrnat.find_ex_minn / ex_minn (structural recursion on acc_nat, a non-uniform Prop inductive) VERIFIED {rcs}")

(ROOT / "reports" / "m6").mkdir(parents=True, exist_ok=True)
(ROOT / "reports" / "m6" / "m6_results.json").write_text(json.dumps(RESULTS, indent=2) + "\n")
finish("test-m6")

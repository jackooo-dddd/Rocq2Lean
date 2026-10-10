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
import subprocess
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
run, rcs, R = pipeline("m6-accfix", ROOT / "fixtures" / "accfix" / "manifest.json",
                       [f"{A}.search_ex", f"{A}.search_ex1", f"{A}.search_step0"])
check(rcs == [0, 0, 0], f"accessibility lowering: search (recursion on an accb proof) VERIFIED; search P2 0 h0 = 2 and "
                        f"search P2 1 _ = 2 by eq_refl (closed computation through Acc.rec) and search_step0 by "
                        f"reflexivity for an arbitrary proof a (open-variable unfolding) {rcs}")
p = subprocess.run([sys.executable, "-I", str(ROOT / "tests" / "m6" / "compute_m6.py")], capture_output=True, text=True)
print(p.stdout.strip().splitlines()[-1] if p.stdout.strip() else p.stderr[-400:])
check(p.returncode == 0, "accessibility lowering: Rocq (cbv) and Lean (normalization) values of search agree on 4 inputs")
run1, rcs1, _ = pipeline("m6-accfix-fn", ROOT / "fixtures" / "accfix" / "manifest.json", [f"{A}.search"])


def bump_result(v):
    hit = find(v, lambda n: n.get("k") == "lam" and n["b"].get("k") == "proj" and n["b"].get("i") == 0
               and n["b"].get("s") == "PSigma")
    lam = at(v, hit[0])
    lam["b"] = {"k": "app", "f": {"k": "const", "n": "Nat.succ", "u": []}, "a": lam["b"]}    # m -> S m


kernel_ok, rc, struct = mutation(run1, f"{A}.search", bump_result, "acc-result")
check(rcs1 == [0, 0, 0] and kernel_ok and rc == 2 and any(p["detector"] == "structure" for p in struct),
      "accessibility lowering: a type-correct result mutation (m -> S m) is kernel-accepted and rejected by the structural audit")


def empty_relation(v):
    # Acc.rec C R motive intro major wf: the node two applications above the constant is (Acc.rec C) R
    hit = find(v, lambda n: n.get("k") == "const" and n.get("n") == "Acc.rec")
    rel_app = at(v, hit[0][:-2])
    R = rel_app["a"]
    rel_app["a"] = {"k": "lam", "n": "y", "t": R["t"],
                    "b": {"k": "lam", "n": "s", "t": R["b"]["t"], "b": {"k": "const", "n": "False", "u": []}}}


kernel_ok, rc, struct = mutation(run1, f"{A}.search", empty_relation, "acc-empty-relation")
check(not kernel_ok and rc != 0,
      "accessibility lowering: replacing the call-graph relation by an empty one is rejected by the kernel "
      "(the generated proofs only check for a relation containing the source call graph)")
# --- ι-generalized fix lowering (fixtures/iotafix): the decreasing match is not outermost
I = "IF.IotaFix"
IROOTS = [f"{I}.{n}" for n in ("eqb_ex", "eqb_ex2", "cmp_ex", "cmp_ex2", "nth_ex", "nth_ex2", "dep_ex", "dep_ex2", "size_ex",
                              "eqb_step", "eqb_mixed", "cmp_step", "nth_step", "size_step", "sumto_ex", "sumto_step", "walk_ex",
                              "walk_step", "padd_ex", "padd_step", "count_ex", "count_step", "norm_ex", "norm_ex2",
                              "norm_step", "norm_step3")]
run, rcs, R = pipeline("m6-iotafix", ROOT / "fixtures" / "iotafix" / "manifest.json", IROOTS)
check(rcs == [0, 0, 0], f"ι-generalized fix lowering: eqb/compare_cont/nth (Pos.eqb, Pos.compare_cont, ListDef.nth shapes), a "
                        f"dependent return clause (dep) and the decreasing argument outside a match (size_if); ζ of a let-bound "
                        f"partial recursive application (sumto, the Pos.peano_rect shape); a functional recursive field (walk, "
                        f"the Acc shape); δβ of a constant the fixpoint passes itself to (padd/addI, count/both: the "
                        f"Ring_polynom Padd/PaddI and Tauto xcnf/mk_and shapes); course-of-values recursion on fields of matched "
                        f"fields (norm, the Ring_polynom norm_aux shape) VERIFIED; closed computations and open-variable computation rules (eqb_step, cmp_step, "
                        f"nth_step, sumto_step, walk_step, ...) by reflexivity {rcs}")
check(p.returncode == 0, "ι-generalized fix lowering and mutual fixpoints: Rocq and Lean values of eqb/compare_cont/nth/"
                        "dep/size_if and add/add_carry/sub_mask/evens_s/alt_eq agree (compute_m6)")
run1, rcs1, _ = pipeline("m6-iotafix-fn", ROOT / "fixtures" / "iotafix" / "manifest.json", [f"{I}.eqb"])


def swap_minors(v):
    # eqb := λ p q, pos.rec motive m_xI m_xO m_xH q p: swap m_xI and m_xO (same binder types)
    hit = find(v, lambda n: n.get("k") == "const" and n.get("n", "").endswith("IotaFix.pos.rec"))
    a0, a1 = at(v, hit[0][:-2]), at(v, hit[0][:-3])
    a0["a"], a1["a"] = a1["a"], a0["a"]


kernel_ok, rc, struct = mutation(run1, f"{I}.eqb", swap_minors, "iota-swapped-minors")
check(rcs1 == [0, 0, 0] and kernel_ok and rc == 2 and any(p["detector"] == "structure" for p in struct),
      "ι-generalized fix lowering: a type-correct mutation (minors for xI and xO swapped: eqb (xI a) (xI b) would be "
      "false) is kernel-accepted and rejected by the structural audit")


def drop_succ(v):
    # the first Nat.succ x in the target becomes x
    hit = find(v, lambda n: n.get("k") == "app" and n["f"] == {"k": "const", "n": "Nat.succ", "u": []})
    node, arg = at(v, hit[0]), hit[1]["a"]
    node.clear()
    node.update(arg)


def drop_negb(v):
    # the first negb x in the target becomes x
    hit = find(v, lambda n: n.get("k") == "app" and n["f"].get("k") == "const" and n["f"]["n"].endswith("Datatypes.negb"))
    node, arg = at(v, hit[0]), hit[1]["a"]
    node.clear()
    node.update(arg)


def cov_wrong_subterm(v):
    # a deep call's result path proj0 (proj1 (proj1 h)) (field m = 1) becomes proj0 (proj1 h) (field 0)
    hit = find(v, lambda n: n.get("k") == "proj" and n.get("s") == "PProd" and n.get("i") == 1
               and n["e"].get("k") == "proj" and n["e"].get("s") == "PProd" and n["e"].get("i") == 1)
    node, inner = at(v, hit[0]), hit[1]["e"]
    node.clear()
    node.update(inner)


for fn, mut, label, what in (("norm", cov_wrong_subterm, "cov-wrong-subterm", "norm's call on b, the second field of "
                                                                               "a matched field, reads the first field's result"),
                             ("sumto", drop_succ, "zeta-generalized-argument", "sumto's inlined call sumto (S k) m becomes sumto k m"),
                             ("walk", drop_succ, "functional-field-argument", "walk's call on f (S k) becomes a call on f k"),
                             ("count", drop_negb, "delta-beta-inlined-call", "count's call through both, count k (negb b) r, "
                                                                               "becomes count k b r")):
    run1, rcs1, _ = pipeline(f"m6-iotafix-{fn}", ROOT / "fixtures" / "iotafix" / "manifest.json", [f"{I}.{fn}"])
    kernel_ok, rc, struct = mutation(run1, f"{I}.{fn}", mut, label)
    check(rcs1 == [0, 0, 0] and kernel_ok and rc == 2 and any(p["detector"] == "structure" for p in struct),
          f"{label}: a type-correct mutation ({what}) is kernel-accepted and rejected by the structural audit")

# --- the real Stdlib/Corelib functions behind lia's certificates (fixtures/stdfix)
SFX = "SF.StdFix"
SROOTS = [f"{SFX}.{n}" for n in ("add_ex", "add_carry_ex", "sub_mask_ex", "sub_mask_ex2", "compare_ex", "compare_cont_ex", "eqb_ex",
                                "pos_sub_ex", "peano_ex", "nth_ex", "add_step", "sub_mask_step", "compare_cont_step", "eqb_step",
                                "pos_sub_step", "peano_step", "nth_step", "acc_rect_step", "acc_inv_step")]
run, rcs, R = pipeline("m6-stdfix", ROOT / "fixtures" / "stdfix" / "manifest.json", SROOTS)
check(rcs == [0, 0, 0], f"Stdlib/Corelib (not copies): Pos.add/add_carry, Pos.sub_mask/sub_mask_carry (mutual), Pos.compare_cont, "
                        f"Pos.eqb, Z.pos_sub, ListDef.nth (non-outermost), Pos.peano_rect (ζ), Acc_rect, Acc_inv (functional "
                        f"field, non-uniform parameter) VERIFIED with closed computations and open-variable computation rules {rcs}")
# --- cast repair: a proof whose cast needs a fixpoint's unfolding at open arguments (Stdlib)
NAP = "Stdlib.setoid_ring.Ring_polynom.norm_aux_PEadd"
run, rcs, R = pipeline("m6-cast-repair", ROOT / "fixtures" / "stdfix" / "micromega_manifest.json", [NAP])
check(rcs == [0, 0, 0], f"cast repair: Ring_polynom.norm_aux_PEadd (its cast needs norm_aux, a course-of-values function, to "
                        f"unfold at open arguments) VERIFIED with the source proof transported along case analysis {rcs}")
if rcs == [0, 0, 0]:
    rep3 = json.loads((run / "translation_report.json").read_text())
    row = next(x for x in rep3["results"] if x["source"] == NAP)

    # the repair is the whole proof under the lemma's binders: R.rec motive minors v c; in its first
    # minor, the leaf (the transported proof, bvar 0) becomes another bound variable
    e_ = row["target_value"]
    while e_.get("k") == "lam":
        e_ = e_["b"]
    sp_, h_ = [], e_["f"]
    while h_.get("k") == "app":
        sp_.append(h_)
        h_ = h_["f"]
    nodes = sp_[::-1]                                     # app nodes, the first argument first
    mi = next(i_ for i_, n_ in enumerate(nodes) if n_["a"].get("k") == "lam" and n_["a"]["b"].get("k") == "forall")
    for n_ in nodes[mi + 1:]:                             # the minors: the first one ending directly in h
        m_ = n_["a"]
        if m_.get("k") != "lam":
            break
        while m_["b"].get("k") == "lam":
            m_ = m_["b"]
        if m_["b"] == {"k": "bvar", "i": 0}:
            m_["b"] = {"k": "bvar", "i": 1}
            break
    rc, probs = audit_report(run, rep3, "cast-repair-leaf")
    check(rc == 1 and any(p["message"].startswith(f"{NAP}:") for p in probs),
          "cast repair (detector check): a repair leaf other than the transported source proof is audit-rejected")
# --- nested inductive with trivial auxiliary eliminations; micromega universe rules (Stdlib)
ZM = "Stdlib.micromega.ZMicromega"
run, rcs, R = pipeline("m6-nested", ROOT / "fixtures" / "stdfix" / "micromega_manifest.json",
                       [f"{ZM}.ZArithProof_ind", f"{ZM}.ZChecker", "Stdlib.micromega.RingMicromega.SORaddon",
                        "Stdlib.setoid_ring.Ring_theory.IDmorph"])
check(rcs == [0, 0, 0] and R[f"{ZM}.ZArithProof"].get("universe_lowered") and R["Stdlib.setoid_ring.Ring_theory.ring_morph"].get("plain_levels"),
      f"Stdlib micromega: ZArithProof (nested, R3-down: PolC at Z's level), ZArithProof_ind and ZChecker (matches and a "
      f"fixpoint on the nested inductive, trivial auxiliary motives), SORaddon and IDmorph (ring_morph with plain "
      f"levels) VERIFIED {rcs}")
# --- delta-inlining of a Set-motive constant used at a Prop family (Stdlib strong induction)
SR = "Stdlib.Arith.PeanoNat/Nat.strong_right_induction"
run, rcs, R = pipeline("m6-delta-inline", ROOT / "fixtures" / "stdfix" / "arith_manifest.json",
                       ["Stdlib.Arith.PeanoNat.Nat.strong_right_induction", "Stdlib.ZArith.BinInt.Z.strong_left_induction"])
check(rcs == [0, 0, 0] and R[SR].get("delta_inlined") == ["Corelib.Init.Wf.well_founded_induction"],
      f"delta-inlining: Nat.strong_right_induction / Z.strong_left_induction (well_founded_induction's P : A -> Set "
      f"used at a Prop family; its body uses the R8-generic well_founded_induction_type) VERIFIED, reported {rcs}")
if rcs == [0, 0, 0]:
    rep4 = json.loads((run / "translation_report.json").read_text())
    next(x for x in rep4["results"] if x["source"] == SR)["delta_inlined"] = []
    rc, probs = audit_report(run, rep4, "delta-unreported")
    check(rc == 1 and any(p["message"].startswith(f"{SR}:") for p in probs),
          "delta-inlining (detector check): an inlining not reported in the row is audit-rejected")
run, rcs, R = pipeline("m6-nested-neg", ROOT / "fixtures" / "iotafix" / "manifest.json", ["IF.IotaFix.rsize"])
check(rcs[1] != 0 and R["IF.IotaFix.rsize"]["status"] == "UNSUPPORTED_FEATURE",
      "nested inductive negative control: rsize (recursion through the nesting) rejected as unsupported")
# --- mutual structural fixpoints (fixtures/mutfix): Pos.add/add_carry, Pos.sub_mask/sub_mask_carry shapes
MF = "MF.MutFix"
MROOTS = [f"{MF}.{n}" for n in ("add_ex", "add_carry_ex", "sub_ex", "sub_ex2", "sub_ex3", "evens_s_ex", "odds_s_ex", "alt_ex",
                               "alt_ex2", "add_step", "add_carry_step", "sub_step", "odds_s_step", "alt_step")]
run, rcs, R = pipeline("m6-mutfix", ROOT / "fixtures" / "mutfix" / "manifest.json", MROOTS)
check(rcs == [0, 0, 0], f"mutual fixpoints (joint recursor into PProd): add/add_carry, sub_mask/sub_mask_carry (x generalized), "
                        f"a Set-parametric pair, a pair with non-outermost matches VERIFIED; closed computations and open-variable "
                        f"computation rules with cross-function calls (add_step, sub_step, ...) by reflexivity {rcs}")
run, rcs, R = pipeline("m6-mutfix-neg", ROOT / "fixtures" / "mutfix" / "manifest.json", [f"{MF}.evens"])
check(rcs[1] != 0 and R[f"{MF}.evens"]["status"] == "UNSUPPORTED_FEATURE" and "different type for argument" in R[f"{MF}.evens"]["message"],
      "mutual fixpoints: evens/odds (A : Type, a different global universe in each function) rejected as unsupported, "
      "not unified")
run1, rcs1, _ = pipeline("m6-mutfix-fn", ROOT / "fixtures" / "mutfix" / "manifest.json", [f"{MF}.add"])


def wrong_projection(v):
    # add := λ x y, (pos.rec … x).1 y  ->  (pos.rec … x).2 y  (add_carry; the same type)
    hit = find(v, lambda n: n.get("k") == "proj" and n.get("s") == "PProd")
    at(v, hit[0])["i"] = 1


def wrong_cross_call(v):
    # a recursive call (ih).1 / (ih).2: call the other function of the block (the same type)
    hit = find(v, lambda n: n.get("k") == "proj" and n.get("s") == "PProd" and n["e"].get("k") == "bvar")
    at(v, hit[0])["i"] = 1 - at(v, hit[0])["i"]


for mut, label, what in ((wrong_projection, "mutual-wrong-projection", "add defined as the add_carry component"),
                         (wrong_cross_call, "mutual-wrong-cross-call", "a recursive call redirected to the other function")):
    kernel_ok, rc, struct = mutation(run1, f"{MF}.add", mut, label)
    check(rcs1 == [0, 0, 0] and kernel_ok and rc == 2 and any(p["detector"] == "structure" for p in struct),
          f"mutual fixpoints: a type-correct mutation ({what}) is kernel-accepted and rejected by the structural audit")
# --- R3-down: a reference instantiated at its argument's level below a shared level (fixtures/cumul)
U2 = "Cu.Cumul"
run, rcs, R = pipeline("m6-r3down", ROOT / "fixtures" / "cumul" / "manifest.json", [f"{U2}.box_len", f"{U2}.steps_ex"])
check(rcs == [0, 0, 0] and R[f"{U2}.proof"].get("universe_lowered") and R[f"{U2}.proof"].get("level_params"),
      f"R3-down positive: proof : Type@{{l}} with a field Box nat (Box@{{l}}, nat : Set <= l; the shape of ZMicromega.ZArithProof) "
      f"keeps its level parameter and instantiates Box at nat's level; reported; VERIFIED {rcs}")
rep2 = json.loads((run / "translation_report.json").read_text())
row = next(x for x in rep2["results"] if x["source"] == f"{U2}.proof")
hit = find(row["target_ctors"], lambda n: n.get("k") == "const" and n.get("n") == "Rocq.Cu.Cumul.Box")
at(row["target_ctors"], hit[0])["u"] = [{"k": "param", "n": "u_Cu_Cumul_unrelated"}]
rc, probs = audit_report(run, rep2, "r3down-forged")
check(rc == 1 and any(p["detector"] in ("universe", "structure") and p["message"].startswith(f"{U2}.proof") for p in probs),
      "R3-down negative: a forged argument that is not a level of the block (nor Set + c <= l) is audit-rejected")
# --- cumulativity-tier controls (fixtures/cumul)
U = "Cu.Cumul"
run, rcs, R = pipeline("m6-cumul-pos", ROOT / "fixtures" / "cumul" / "manifest.json", [f"{U}.uses_n", f"{U}.up"])
si = json.loads((run / "source_instances.json").read_text()) if (run / "source_instances.json").exists() else {}
check(rcs == [0, 0, 0] and R[f"{U}.uses_n"].get("r2bp_levels") and si.get("checked", {}).get(f"{U}.uses_n") == "INSTANCE_OK",
      f"R2B-P positive: uses_n's level solved below an outside fact; Rocq's kernel accepts the source at that instance; VERIFIED {rcs}")
run, rcs, R = pipeline("m6-cumul-neg", ROOT / "fixtures" / "cumul" / "manifest.json", [f"{U}.prop_in_m"])
v = json.loads((run / "verify.json").read_text()) if (run / "verify.json").exists() else {}
check(rcs[:2] == [0, 0] and rcs[2] != 0 and "R2B-P source instance rejected" in v.get("reason", ""),
      "R2B-P negative control: prop_in_m (its own typing needs Set < m) translates under the relaxation, "
      "but its Rocq instance m := Set is rejected by Rocq's kernel, so verify fails")
run, rcs, R = pipeline("m6-cumul-sort", ROOT / "fixtures" / "cumul" / "manifest.json", [f"{U}.up_nat"])
row = R[f"{U}.up_nat"]
check(rcs == [0, 0, 0] and [x["level"] for x in row.get("sort_lowered_levels") or []] and not row.get("r2bp_levels"),
      f"R2B-S positive: up_nat : Type@{{c}} := up nat (Set < c from c's declaration, c only in the result sort) is a "
      f"type at its value's level; reported as a result-sort level, not R2B-P; VERIFIED {rcs}")
run, rcs, R = pipeline("m6-cumul-sortneg", ROOT / "fixtures" / "cumul" / "manifest.json", [f"{U}.up_binder"])
v = json.loads((run / "verify.json").read_text()) if (run / "verify.json").exists() else {}
check(rcs[2] != 0 and not R[f"{U}.up_binder"].get("sort_lowered_levels") and "R2B-P" in v.get("reason", ""),
      "R2B-S negative control: up_binder (c also in a binder type) is not a result-sort lowering; as a statement "
      "specialization it is refused (a requested root; its Rocq instance is also ill-typed)")
# Statement specializations (R2B-P on a type level, e.g. Morphisms obligations whose A : Type@{77} meets
# respectful's shared level at Prop): Rocq's kernel accepts each at the instance, and never on a root
LR = "Stdlib.Lists.List"
run, rcs, R = pipeline("m6-specialized", ROOT / "fixtures" / "m4" / "manifest.json", [f"{LR}.length_rev", f"{LR}.in_rev"])
si = json.loads((run / "source_instances.json").read_text()) if (run / "source_instances.json").exists() else {}
spec = [s_ for s_, r_ in R.items() if any(x.get("in_type") for x in r_.get("r2bp_levels") or [])]
check(rcs == [0, 0, 0] and spec and all(si.get("checked", {}).get(s_) == "INSTANCE_OK" for s_ in spec),
      f"statement specializations: {len(spec)} Morphisms rows (length_rev, in_rev closure) each accepted by Rocq's kernel "
      f"at the instance (INSTANCE_OK); the run VERIFIED {rcs}")
MO = "Corelib.Classes.Morphisms.trans_co_impl_morphism_obligation_1"
run, rcs, R = pipeline("m6-specialized-root", ROOT / "fixtures" / "stdfix" / "morph_manifest.json", [MO])
v = json.loads((run / "verify.json").read_text()) if (run / "verify.json").exists() else {}
check(rcs[:2] == [0, 0] and rcs[2] != 0 and "specialized" in v.get("reason", ""),
      "statement specialization refused on a requested root (its statement would be weakened)")
MC5 = ROOT / "fixtures" / "m5" / "manifest.json"
PH = ["mathcomp.boot.bigop.Monoid.isLaw.phant_axioms", "mathcomp.boot.bigop.Monoid.isComLaw.phant_axioms"]
run, rcs, R = pipeline("m6-r3up", MC5, PH)
rows = [R[n.replace("bigop.Monoid.", "bigop/Monoid/")] for n in PH]   # report names: module path with /
check(rcs == [0, 0, 0] and all(r.get("universe_cumulativity") and not r.get("r2bp_levels") for r in rows),
      f"R3-up positive: MathComp Monoid.isLaw/isComLaw.phant_axioms (a reference's result level lifted to the referrer's "
      f"level by a native fact, no R2B-P) VERIFIED {rcs}")
run = ROOT / "runs" / "m6-cumul-pos"
rep2 = json.loads((run / "translation_report.json").read_text())
row = next(x for x in rep2["results"] if x["source"] == f"{U}.up")
hit = find(row["target_value"], lambda n: n.get("k") == "const" and n.get("n") == "Rocq.Cu.Cumul.wrap")
lv = at(row["target_value"], hit[0])["u"]
lv[-1] = {"k": "param", "n": "u_Cu_Cumul_a"} if lv[-1] != {"k": "param", "n": "u_Cu_Cumul_a"} else lv[-1]
rc, probs = audit_report(run, rep2, "r3up-unrelated")
check(rc == 1 and any(p["detector"] in ("universe", "structure") and p["message"].startswith(f"{U}.up") for p in probs),
      "R3 negative: a forged universe argument of a reference that is not the image of the source level is audit-rejected")

M = "mathcomp.boot.ssrnat"
run, rcs, R = pipeline("m6-find-ex-minn", ROOT / "fixtures" / "m6" / "mathcomp_manifest.json", [f"{M}.find_ex_minn", f"{M}.ex_minn"])
check(rcs == [0, 0, 0] and R[f"{M}.acc_nat"]["num_params"] == 1,
      f"MathComp ssrnat.find_ex_minn / ex_minn (structural recursion on acc_nat, a non-uniform Prop inductive) VERIFIED {rcs}")

(ROOT / "reports" / "m6").mkdir(parents=True, exist_ok=True)
(ROOT / "reports" / "m6" / "m6_results.json").write_text(json.dumps(RESULTS, indent=2) + "\n")
finish("test-m6")

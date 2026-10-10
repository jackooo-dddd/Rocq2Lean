"""M4: genuine Rocq 9.3.0 standard-library datatypes, functions and theorems (original proof terms).

Positive: the real parameterized datatypes (template list, option, prod; bool), 29 real functions,
16 real theorems, each run through the public CLI (export with round trip, translate, verify:
kernel, consumer, independent audit); computation of functions and generated recursors compared
with Rocq (tests/m4/compute_m4.py). Negative: a Prop instance of the template prod, mutated native
template metadata, forged reports (template binding, level parameters, template level, proof-local
level solution) and type-correct mutations of the generalized fixpoint lowering, each rejected for
the intended reason; known blockers reported by inspect with their dependency paths.
"""
import copy
import json
import os
import shutil
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "tools"))
from lib import ROOT, audit_report, check, cli, finish, forge_run, results, SWITCH  # noqa: E402
import replay  # noqa: E402

MAN = ROOT / "fixtures" / "m4" / "manifest.json"
D, L, C = "Corelib.Init.Datatypes", "Stdlib.Lists.List", "Corelib.Lists.ListDef"
DATATYPES = {f"{D}.list": (1, True, ["nil", "cons"]), f"{D}.option": (1, True, ["Some", "None"]),
             f"{D}.prod": (2, True, ["pair"]), f"{D}.bool": (0, False, ["true", "false"])}
THEOREMS = [f"{L}.{n}" for n in ("app_nil_r", "app_assoc", "length_app", "map_app", "length_map", "rev_app_distr",
                                 "rev_involutive", "map_map", "map_id", "in_map", "fold_left_app", "combine_split",
                                 "length_fst_split", "app_inv_head", "in_app_or", "map_ext")]
FUNCTIONS = ([f"{L}.{n}" for n in ("rev", "fold_left", "fold_right", "combine", "split", "hd_error", "existsb", "forallb",
                                    "filter", "concat", "last", "removelast", "nth_error", "rev_append", "flat_map",
                                    "partition", "list_prod")]
             + [f"{C}.{n}" for n in ("firstn", "skipn", "repeat", "seq", "map")]
             + [f"{D}.{n}" for n in ("option_map", "negb", "andb", "orb", "xorb", "fst", "snd")])
RESULTS = {}


def pipeline(name, roots):
    run = ROOT / "runs" / name
    shutil.rmtree(run, ignore_errors=True)
    rcs = [cli("export", "--manifest", MAN, "--roots", ",".join(roots), "--out", run)[0],
           cli("translate", "--input", run / "source.ndjson", "--out", run)[0], cli("verify", "--run", run)[0],
           cli("status", "--run", run)[0]]
    R, rep = results(run) if (run / "translation_report.json").exists() else ({}, {})
    RESULTS[name] = {"roots": {r: R.get(r, {}).get("status") for r in roots}, "exit_codes": rcs,
                     "closure": json.loads((run / "verify.json").read_text()).get("required_closure_size")
                     if (run / "verify.json").exists() else None}
    return run, rcs, R


# 1. Real datatypes.
run, rcs, R = pipeline("m4-datatypes", list(DATATYPES))
check(rcs == [0, 0, 0, 0], f"real datatypes list/option/prod/bool: export, translate, verify, status {rcs}")
for src, (nlev, templ, ctors) in DATATYPES.items():
    r = R[src]
    t = r["target"]
    check(r["status"] == "TRANSLATED_AND_CHECKED" and t == "Rocq." + src and len(r["level_params"]) == nlev
          and r["template"] == templ and [c["name"] for c in r["target_ctors"]] == [t + "." + c for c in ctors],
          f"{src}: fresh Lean inductive {t}, {nlev} universe parameter(s), template={templ}, constructors {ctors} in order")
    if templ:
        tps = sorted(x["param"] for x in r["template_params"])
        check(tps == list(range(nlev)), f"{src}: template levels bound by parameters {tps} (kernel template record)")

# 2. Real theorems (original proof terms) and 3. real functions.
run_t, rcs, R = pipeline("m4-theorems", THEOREMS)
check(rcs == [0, 0, 0, 0] and all(R[t]["status"] == "TRANSLATED_AND_CHECKED" for t in THEOREMS),
      f"{len(THEOREMS)} genuine Stdlib theorems VERIFIED with their dependency closure ({RESULTS['m4-theorems']['closure']})")
aud = json.loads((run_t / "audit.json").read_text())
check(aud["status"] == "OK" and aud["instance_levels"]["deferred_to_consumer"] == 0 and aud["instance_levels"]["checked"] > 0,
      f"independent audit: {aud['instance_levels']} typing-determined levels, {aud['universe_arguments_checked']} R3 arguments")
pl = [x for x in R.values() if x.get("solved_levels")]
check(len(pl) >= 2 and all(x["universe_level_defaults"] == 0 for x in R.values()),
      f"proof-local levels (R2B) solved in {len(pl)} declarations ({', '.join(x['source'].split('.')[-1] for x in pl)}); no defaults")
run_f, rcs, R = pipeline("m4-functions", FUNCTIONS)
check(rcs == [0, 0, 0, 0] and all(R[f]["status"] == "TRANSLATED_AND_CHECKED" for f in FUNCTIONS),
      f"{len(FUNCTIONS)} genuine Stdlib/Corelib functions VERIFIED (closure {RESULTS['m4-functions']['closure']})")

# 4. Computation: functions and generated recursors, Rocq vs Lean.
p = subprocess.run([sys.executable, "-I", str(ROOT / "tests" / "m4" / "compute_m4.py")], capture_output=True, text=True)
comp = json.loads((ROOT / "runs" / "m4-compute" / "computation.json").read_text()) \
    if (ROOT / "runs" / "m4-compute" / "computation.json").exists() else {"cases": 0, "disagreements": -1}
check(p.returncode == 0 and comp["disagreements"] == 0 and comp["cases"] >= 30,
      f"computation: {comp['cases'] - max(comp['disagreements'], 0)}/{comp['cases']} cases agree (functions, list/option/prod/bool_rect)")
RESULTS["computation"] = comp
# Kernel-generated recursors of the real datatypes, as used by accepted declarations (consumer metadata).
recs = {}
for rn in ("m4-theorems", "m4-functions", "m4-compute"):
    cp = ROOT / "runs" / rn / "consumer_result.json"
    if cp.exists():
        recs.update({r["name"]: r for r in json.loads(cp.read_text())["recursors"]})
lr = recs.get(f"Rocq.{D}.list.rec", {})
check(all(f"Rocq.{s}.rec" in recs for s in DATATYPES) and lr.get("level_params") == ["u", "u_Corelib_Init_Datatypes_190"]
      and lr.get("num_motives") == 1 and lr.get("num_params") == 1 and lr.get("rule_nfields") == [0, 2],
      f"kernel recursors used: list.rec.{{u, u_list}} (large elimination, nfields [0, 2]), option/prod/bool.rec "
      f"({sorted(n for n in recs if n.startswith('Rocq.Corelib.Init.Datatypes'))})")

# 5. Negative: Prop instance of the template prod.
neg = ROOT / "runs" / "m4-neg-prop"
shutil.rmtree(neg, ignore_errors=True)
assert cli("export", "--manifest", MAN, "--roots", "M4.M4Neg.pp", "--out", neg)[0] == 0
rc, _ = cli("translate", "--input", neg / "source.ndjson", "--out", neg)
Rn, _ = results(neg)
check(rc == 2 and Rn["M4.M4Neg.pp"]["status"] == "UNSUPPORTED_FEATURE" and "quality Prop" in Rn["M4.M4Neg.pp"]["message"],
      f"prod instantiated at Prop rejected explicitly ({Rn['M4.M4Neg.pp']['status']}: {Rn['M4.M4Neg.pp']['message'][:70]})")

# 5b. Template parameter of arity type (sigT's P : A -> Type): genuine Corelib sigT with projT1/projT2
#     verifies; a Prop-valued family (Rocq: Prop <= Type cumulativity) is rejected explicitly.
st, rcs, Rs = pipeline("m4-sigt", ["Corelib.Init.Specif.sigT", "Corelib.Init.Specif.projT1", "Corelib.Init.Specif.projT2"])
sg = Rs.get("Corelib.Init.Specif.sigT", {})
check(rcs == [0, 0, 0, 0] and sg.get("template") is True and sorted(x["param"] for x in sg.get("template_params", [])) == [0, 1],
      f"Corelib sigT (template levels bound by A : Type and the arity P : A -> Type), projT1, projT2 VERIFIED {rcs}")
neg2 = ROOT / "runs" / "m4-neg-sigprop"
shutil.rmtree(neg2, ignore_errors=True)
assert cli("export", "--manifest", MAN, "--roots", "M4.M4Neg.sig_prop", "--out", neg2)[0] == 0
rc, _ = cli("translate", "--input", neg2 / "source.ndjson", "--out", neg2)
r2 = results(neg2)[0]["M4.M4Neg.sig_prop"]
check(rc == 2 and r2["status"] == "UNSUPPORTED_FEATURE" and "cumulativity" in r2["message"],
      f"Prop-valued family for sigT rejected explicitly ({r2['status']})")

# 6. Negative: mutated native template metadata is caught by the fresh-process round trip.
lines = [json.loads(l) for l in open(run / "source.ndjson")]
lst = next(x for x in lines if x.get("name") == f"{D}.list")
lst["native"]["template_info"]["param_arguments"] = [None]
d = ROOT / "runs" / "m4-neg-template-meta"
shutil.rmtree(d, ignore_errors=True)
(d / "logs").mkdir(parents=True)
(d / "source.ndjson").write_text("".join(json.dumps(x) + "\n" for x in lines))
env = dict(os.environ, PATH=f"{Path.home()}/.local/bin:" + os.environ["PATH"])
p = subprocess.run(["opam", "exec", "--switch=" + SWITCH, "--", sys.executable, "-I", str(ROOT / "tools" / "roundtrip.py"),
                    str(d / "source.ndjson"), str(d), "-Q", str(MAN.parent), "M4", "--", "M4.M4Std"],
                   capture_output=True, text=True, env=env)
rt = json.loads((d / "roundtrip.json").read_text()) if (d / "roundtrip.json").exists() else {}
check(p.returncode != 0 and "template_info" in json.dumps(rt),
      "mutated template_info (list's template parameter erased) rejected by the native round trip")


# 7. Negative: forged reports, classified by kernel replay and rejected by the intended detector.
def forged(run, name, decl, mutate, detector, needle):
    rep = json.loads((run / "translation_report.json").read_text())
    mutate(next(x for x in rep["results"] if x["source"] == decl), rep)
    dd = run / f"mut-{name}"
    shutil.rmtree(dd, ignore_errors=True)
    dd.mkdir()
    (dd / "report.json").write_text(json.dumps(rep))
    kern = next((x["kernel"] for x in replay.replay(dd / "report.json", dd) if x["source"] == decl), "NOT_REPLAYED")
    rc, probs = audit_report(run, rep, f"mut-{name}")
    hit = [x["message"] for x in probs if x["detector"] == detector and needle in x["message"]]
    check(rc == 1 and hit, f"{name}: rejected by the '{detector}' detector (kernel replay: {kern})"
          + ("" if hit else f" — got {[(x['detector'], x['message'][:80]) for x in probs][:3]}"))
    RESULTS.setdefault("mutations", []).append({"mutation": name, "declaration": decl, "kernel": kern, "detector": detector})


forged(run, "template-binding", f"{D}.prod", lambda r, rep: r.update(template_params=list(reversed(
    [{"level": x["level"], "param": 1 - x["param"]} for x in r["template_params"]]))), "structure", "template status/binding")
forged(run, "inductive-level-params", f"{D}.list", lambda r, rep: r.update(level_params=["u_other"]), "structure",
       "universe parameters")


def raise_list_level(r, rep):
    def go(e):
        if isinstance(e, dict):
            if e.get("k") == "const" and e["n"] == f"Rocq.{D}.list" and e["u"]:
                e["u"] = [{"k": "succ", "l": e["u"][0]}]
            for v in e.values():
                go(v)
        elif isinstance(e, list):
            for v in e:
                go(v)
    go(r["target_type"])
forged(run_t, "template-level-raised", f"{L}.app_nil_r", raise_list_level, "instance_levels", "template level")
forged(run_t, "proof-local-solution", f"{L}.app_nil_r",
       lambda r, rep: [b.update(sigma={"k": "zero"}) for b in r["solved_levels"]], "universe", "violates the native fact")
forged(run_t, "proof-local-set", f"{L}.app_nil_r", lambda r, rep: r.update(solved_levels=r["solved_levels"][1:]), "universe",
       "do not partition the own levels")


# 8. Negative: type-correct mutations of the generalized fixpoint lowering (seq), kernel-accepted, through verify.
def seq_rows(rep):
    return next(x for x in rep["results"] if x["source"] == f"{C}.seq")


def spine(e):
    sp = []
    while e["k"] == "app":
        sp.append(e)
        e = e["f"]
    return e, list(reversed(sp))


def mut_top_g(rep):            # λ start len. Nat.rec … len start  ->  … len (S start)
    v = seq_rows(rep)["target_value"]["b"]["b"]
    h, sp = spine(v)
    sp[-1]["a"] = {"k": "app", "f": {"k": "const", "n": "Nat.succ", "u": []}, "a": sp[-1]["a"]}


def mut_rec_g(rep):            # minor for S: ih (S start') -> ih start'
    v = seq_rows(rep)["target_value"]["b"]["b"]
    h, sp = spine(v)
    minor = sp[2]["a"]
    m = minor
    while m["k"] == "lam":
        m = m["b"]
    def go(e):
        if isinstance(e, dict):
            if e.get("k") == "app" and e["f"].get("k") == "bvar" and e["a"].get("k") == "app" and \
                    e["a"]["f"] == {"k": "const", "n": "Nat.succ", "u": []}:
                e["a"] = e["a"]["a"]
                return True
            return any(go(v) for v in e.values() if isinstance(v, (dict, list)))
        if isinstance(e, list):
            return any(go(v) for v in e)
        return False
    assert go(m), "no ih (S _) call found in seq's successor minor"


fdefs = ROOT / "runs" / "m4-seq"
shutil.rmtree(fdefs, ignore_errors=True)
assert [cli("export", "--manifest", MAN, "--roots", f"{C}.seq", "--out", fdefs)[0],
        cli("translate", "--input", fdefs / "source.ndjson", "--out", fdefs)[0], cli("verify", "--run", fdefs)[0]] == [0, 0, 0]
for name, mut in (("seq-generalized-argument", mut_top_g), ("seq-recursive-call-argument", mut_rec_g)):
    rep = json.loads((fdefs / "translation_report.json").read_text())
    mut(rep)
    dd, kernel_ok, rc, cons_, aud_ = forge_run(fdefs, name, rep)
    struct = [x for x in aud_.get("problems", []) if x["detector"] == "structure" and x["message"].startswith(f"{C}.seq:")]
    check(kernel_ok and cons_.get("status") == "OK" and rc == 2 and struct,
          f"e2e {name}: type-correct, kernel-accepted, consumer OK; verify rejects via the structural audit of seq")
    RESULTS.setdefault("mutations", []).append({"mutation": name, "declaration": f"{C}.seq",
                                                "kernel": "ACCEPTED" if kernel_ok else "REJECTED", "detector": "structure"})

# 9. Former blocker: Corelib nth (its decreasing match on l is not outermost) is supported since M6
# completion (ι-generalized lowering); inspect no longer reports a blocker (it is VERIFIED in test-m6).
for root in (f"{C}.nth",):
    rc, out = cli("inspect", "--manifest", MAN, "--roots", root)
    rep = json.loads(out[:out.rindex("}") + 1]) if "}" in out else {"roots": {}}
    v = rep["roots"].get(root, {})
    check(rc == 0 and v.get("status") == "CANDIDATE_SUPPORTED",
          f"inspect {root}: a candidate since M6 completion (non-outermost decreasing match), not a blocker")
    RESULTS.setdefault("former_blockers", []).append({"root": root, "status": v.get("status")})

# 10. Former M4 blockers (setoid Morphisms: universe-polymorphic constants, relation's sort floor,
# Prop-typing facts of proof-local levels), translated since M6 (rules R6, R2⁺, R2B-P): VERIFIED.
fb = ROOT / "runs" / "m4-former-blockers"
shutil.rmtree(fb, ignore_errors=True)
rcs = [cli("export", "--manifest", MAN, "--roots", f"{L}.length_rev,{L}.in_rev", "--out", fb)[0]]
rcs += [cli("translate", "--input", fb / "source.ndjson", "--out", fb)[0], cli("verify", "--run", fb)[0]]
check(rcs == [0, 0, 0], f"former blockers length_rev and in_rev (through Corelib.Classes.Morphisms) VERIFIED since M6 {rcs}")
RESULTS["former_blockers_verified"] = {"roots": [f"{L}.length_rev", f"{L}.in_rev"], "exit_codes": rcs}

(ROOT / "reports" / "m4").mkdir(parents=True, exist_ok=True)
(ROOT / "reports" / "m4" / "m4_results.json").write_text(json.dumps(RESULTS, indent=2) + "\n")
finish("test-m4")

"""Universe interpretation (hardening P1): rule R3 in translator and auditor, source facts."""
import copy
import json
import os
import shutil
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "tools"))
from lib import ROOT, audit_report, check, cli, finish, results, SWITCH  # noqa: E402
import audit as A  # noqa: E402
import replay  # noqa: E402

MAN = ROOT / "fixtures" / "universes" / "manifest.json"
RUN = ROOT / "runs" / "hu-univ"
ROOTS = ["U.Univ." + n for n in ("usea", "useb", "usea_twice", "use_set", "via_usea", "usea_id")]
shutil.rmtree(RUN, ignore_errors=True)
rcs = [cli("export", "--manifest", MAN, "--roots", ",".join(ROOTS), "--out", RUN)[0],
       cli("translate", "--input", RUN / "source.ndjson", "--out", RUN)[0], cli("verify", "--run", RUN)[0]]
check(rcs == [0, 0, 0], "positive: related levels, shared level, repeated refs, Set, composition — VERIFIED")
REP = json.loads((RUN / "translation_report.json").read_text())
aud = json.loads((RUN / "audit.json").read_text())
tr_checks = sum(r.get("universe_checks", 0) for r in REP["results"])
check(aud["universe_arguments_checked"] == tr_checks and tr_checks > 0,
      f"translator and independent auditor checked the same {tr_checks} universe arguments")
check(sum(r.get("universe_level_defaults", 0) for r in REP["results"]) == 0, "no defaulted universe levels")
check(all(not r.get("universe_diagnostics") for r in REP["results"]), "no solver diagnostics")


def lvl_param(n):
    return {"k": "param", "n": n}


def mutate_ref(rep, decl, target_const, new_level):
    """Replace the universe argument of every reference to `target_const` inside decl's target."""
    rep = copy.deepcopy(rep)
    r = next(x for x in rep["results"] if x["source"] == decl)

    def go(e):
        if isinstance(e, dict):
            if e.get("k") == "const" and e["n"] == target_const:
                e["u"] = [new_level(u) for u in e["u"]]
            for v in e.values():
                go(v)
        elif isinstance(e, list):
            for v in e:
                go(v)
    go(r["target_value"])
    go(r["target_type"])
    return rep


def classify(name, rep, decl):
    d = RUN / f"mut-{name}"
    shutil.rmtree(d, ignore_errors=True)
    d.mkdir()
    (d / "report.json").write_text(json.dumps(rep))
    kern = next(x for x in replay.replay(d / "report.json", d) if x["source"] == decl)["kernel"]
    rc, probs = audit_report(RUN, rep, f"mut-{name}")
    dets = sorted({p["detector"] for p in probs})
    return kern, rc, dets


IDB = "Rocq.U.Univ.idb"
# (1) Target level raised by one, same number of arguments.
k, rc, dets = classify("succ", mutate_ref(REP, "U.Univ.usea", IDB, lambda u: {"k": "succ", "l": u}), "U.Univ.usea")
check(rc != 0 and "universe" in dets, f"raised target level rejected by the universe detector (kernel: {k}; classification: "
      f"{'kernel+audit' if k == 'REJECTED' else 'audit-only'})")
# (2) Shared-level coherence: useb must use its own parameter; use a foreign param instead.
k, rc, dets = classify("foreign", mutate_ref(REP, "U.Univ.useb", IDB, lambda u: lvl_param("u_U_Univ_21")), "U.Univ.useb")
check(rc != 0 and "universe" in dets, f"foreign/incoherent level argument rejected by the universe detector (kernel: {k})")
# (3) Positive normalization controls: equivalent spellings are accepted by kernel and audit.
for name, f in (("max-self", lambda u: {"k": "max", "a": u, "b": u}), ("max-zero", lambda u: {"k": "max", "a": {"k": "zero"}, "b": u})):
    k, rc, dets = classify(name, mutate_ref(REP, "U.Univ.usea", IDB, f), "U.Univ.usea")
    check(k == "ACCEPTED" and rc == 0, f"equivalent level spelling '{name}' accepted by kernel and audit (intentionally equivalent)")
# (4) Python level normal form: equivalences and non-equivalences.
nf = A.level_nf
u = lvl_param("u")
check(nf({"k": "max", "a": {"k": "succ", "l": {"k": "zero"}}, "b": {"k": "succ", "l": u}}) == nf({"k": "succ", "l": u}),
      "level_nf: max(1, u+1) == u+1")
check(nf({"k": "succ", "l": {"k": "max", "a": u, "b": lvl_param("v")}}) ==
      nf({"k": "max", "a": {"k": "succ", "l": u}, "b": {"k": "succ", "l": lvl_param("v")}}), "level_nf: (max u v)+1 == max(u+1, v+1)")
check(nf({"k": "succ", "l": u}) != nf(u), "level_nf: u+1 != u")


# (5) Source constraint mutated independently of term bodies.
def mutate_facts(drop=None, add=None):
    lines = [json.loads(l) for l in open(RUN / "source.ndjson")]
    rels = lines[4]["relations"]
    if drop:
        rels[:] = [x for x in rels if (x["l"], x["r"]) != drop]
    if add:
        rels.append(add)
    return lines


ua, ub = "U.Univ.21", "U.Univ.22"
for name, lines in (("drop-ua<=ub", mutate_facts(drop=(ua, ub))),
                    ("add-ub<=ua", mutate_facts(add={"l": ub, "rel": "le", "r": ua}))):
    d = RUN / f"facts-{name}"
    shutil.rmtree(d, ignore_errors=True)
    d.mkdir()
    (d / "source.ndjson").write_text("".join(json.dumps(x) + "\n" for x in lines))
    env = dict(os.environ, PATH=f"{Path.home()}/.local/bin:" + os.environ["PATH"])
    p = subprocess.run(["opam", "exec", "--switch=" + SWITCH, "--", sys.executable, "-I", str(ROOT / "tools" / "roundtrip.py"),
                        str(d / "source.ndjson"), str(d), "-Q", str(MAN.parent), "U", "--", "U.Univ"],
                       capture_output=True, text=True, env=env)
    check(p.returncode != 0 and "UREL_MISMATCH" in p.stdout, f"[{name}] native re-check rejects the mutated universe fact")
    # The auditor, given the mutated facts, rejects the dependent reference by its universe detector.
    shutil.copy(RUN / "contract.json", d / "contract.json")
    rc, probs = audit_report(d, REP, "u")
    dets = {x["detector"] for x in probs}
    if name.startswith("drop"):
        check("universe" in dets and any("U.Univ.usea" in x["message"] for x in probs if x["detector"] == "universe"),
              f"[{name}] auditor's universe detector rejects usea once ua <= ub is not entailed")
    else:
        check("binding" in dets, f"[{name}] auditor rejects the mutated IR (binding to the contract digest)")

# (6) Strict inclusion Type@{ub} : Type@{uc} (ub < uc). Under R2 alone (independent parameters) this was
#     an honest kernel rejection; under R2S (since M5) Lean's unifier solves uc := u_ub + 1, which
#     satisfies the native fact ub < uc, so the declaration translates and verifies with that solution.
big = ROOT / "runs" / "hu-univ-big"
shutil.rmtree(big, ignore_errors=True)
rcs = [cli("export", "--manifest", MAN, "--roots", "U.Univ.big", "--out", big)[0],
       cli("translate", "--input", big / "source.ndjson", "--out", big)[0], cli("verify", "--run", big)[0]]
R, _ = results(big)
bg = R["U.Univ.big"]
sol = {x["level"]: x["sigma"] for x in bg.get("solved_levels", [])}
check(rcs == [0, 0, 0] and bg["level_params"] == ["u_U_Univ_22"] and
      sol.get("U.Univ.23") == {"k": "succ", "l": {"k": "param", "n": "u_U_Univ_22"}},
      f"Type@{{ub}} : Type@{{uc}} (ub < uc): R2S solves uc := u_ub + 1 (native fact holds) and the run VERIFIES {rcs}")

# (7) Defaulted (residual) levels: justified by a kernel check of the generic declaration, re-checked
#     by the consumer; forged or missing justifications are rejected through the full pipeline.
import hashlib  # noqa: E402
RES = ROOT / "runs" / "hu-resid"
shutil.rmtree(RES, ignore_errors=True)
rcs = [cli("export", "--manifest", MAN, "--roots", "U.UnivResidual.use_cst_eq", "--out", RES)[0],
       cli("translate", "--input", RES / "source.ndjson", "--out", RES)[0], cli("verify", "--run", RES)[0]]
RR, _ = results(RES)
uc = RR["U.UnivResidual.cst"]
cons = json.loads((RES / "consumer_result.json").read_text())
ONE = {"k": "succ", "l": {"k": "zero"}}
# ur occurs only in cst's body: a proof-local level (R2B); nothing constrains it, so it defaults to its
# minimal model (Set < ur gives 1), justified by the kernel for every value, re-checked by the consumer.
check(rcs == [0, 0, 0] and uc["level_params"] == [] and uc["universe_level_defaults"] == 1
      and uc["universe_residuals"]["params"] == ["u_residual_0"] and uc["universe_residuals"]["defaults"] == [ONE]
      and [b["sigma"] for b in uc["solved_levels"]] == [ONE] and cons["residual_levels_checked"] == 1
      and RR["U.UnivResidual.use_cst"]["universe_level_defaults"] == 0,
      "residual proof-local level: cst defaults ur to its minimal model (1), justified (kernel, every value) and re-checked by the consumer — VERIFIED")


def e2e(run, name, mutate):
    d = run.parent / f"{run.name}-e2e-{name}"
    shutil.rmtree(d, ignore_errors=True)
    shutil.copytree(run, d, ignore=shutil.ignore_patterns(".rocq2lean.lock"))
    rep = json.loads((d / "translation_report.json").read_text())
    mutate({r["source"]: r for r in rep["results"]})
    (d / "translation_report.json").write_text(json.dumps(rep))
    tm = json.loads((d / "translation_manifest.json").read_text())
    tm["report_sha256"] = hashlib.sha256((d / "translation_report.json").read_bytes()).hexdigest()
    (d / "translation_manifest.json").write_text(json.dumps(tm))
    rc, _ = cli("verify", "--run", d)
    c = json.loads((d / "consumer_result.json").read_text()) if (d / "consumer_result.json").exists() else {"problems": []}
    rcA, probsA = audit_report(d, rep, "forged")
    return rc, c["problems"], probsA


def forge_unjustified(rows):
    r = rows["U.UnivResidual.use_cst_eq"]
    gty = json.loads(json.dumps(r["target_type"]))
    def raise_eq(e):                         # Eq.{1} -> Eq.{u_residual_0 + 1}: equal at 0, ill typed otherwise
        if isinstance(e, dict):
            if e.get("k") == "const" and e["n"] == "Eq":
                e["u"] = [{"k": "succ", "l": {"k": "param", "n": "u_residual_0"}}]
            for v in e.values():
                raise_eq(v)
    raise_eq(gty)
    r["universe_level_defaults"] = 1
    r["universe_residuals"] = {"params": ["u_residual_0"], "defaults": [{"k": "zero"}], "justification": "forged",
                               "generic_type": gty, "generic_value": r["target_value"]}
rc, cp, ap = e2e(RES, "unjustified", forge_unjustified)
check(rc == 2 and any(x["detector"] == "residual_levels" and "rejected by the kernel" in x["message"] for x in cp),
      "forged residual whose generic declaration is not valid for every level: consumer kernel re-check rejects (verify exit 2)")
check(not any(x["detector"] == "universe" for x in ap),
      "  (the auditor's syntactic residual check alone accepts it: the kernel re-check is the necessary gate)")
rc, cp, ap = e2e(RES, "unrecorded", lambda rows: rows["U.UnivResidual.cst"].update(universe_residuals=None))
check(rc == 2 and any(x["detector"] == "residual_levels" and "without a justification" in x["message"] for x in cp)
      and any(x["detector"] == "universe" and "without a justification record" in x["message"] for x in ap),
      "defaulted level with its justification record removed: rejected by consumer and auditor")


def forge_generic(rows):
    g = rows["U.UnivResidual.cst"]["universe_residuals"]["generic_value"]
    done = []

    def bump(e):                             # first occurrence of the residual parameter -> its successor
        if isinstance(e, dict):
            for k_, v_ in list(e.items()):
                if not done and v_ == {"k": "param", "n": "u_residual_0"}:
                    e[k_] = {"k": "succ", "l": v_}
                    done.append(1)
                else:
                    bump(v_)
        elif isinstance(e, list):
            for v_ in e:
                bump(v_)
    bump(g)
    assert done
rc, cp, ap = e2e(RES, "generic-mismatch", forge_generic)
check(rc == 2 and any(x["detector"] == "residual_levels" and "not the imported one" in x["message"] for x in cp)
      and any("differs from the reported declaration" in x["message"] for x in ap),
      "justification record that does not instantiate to the accepted declaration: rejected by consumer and auditor")

# (8) Typing-determined instance levels (Eq template level, recursor motive level): recomputed by the
#     auditor from the audited terms and checked at every occurrence by the consumer.
aud = json.loads((RES / "audit.json").read_text())
check(aud["instance_levels"]["checked"] >= 2 and cons["instance_levels_checked"] >= 2,
      f"instance levels: auditor determined {aud['instance_levels']}, consumer checked {cons['instance_levels_checked']}")
REPR = json.loads((RES / "translation_report.json").read_text())


def bump_const(rep, decl, cname, part="target_type"):
    rep = copy.deepcopy(rep)
    r = next(x for x in rep["results"] if x["source"] == decl)

    def go(e):
        if isinstance(e, dict):
            if e.get("k") == "const" and e["n"] == cname and e["u"]:
                e["u"][0] = {"k": "succ", "l": e["u"][0]}
            for v in e.values():
                go(v)
    go(r[part])
    return rep


d = RES / "mut-eq-level"
shutil.rmtree(d, ignore_errors=True)
d.mkdir()
rep = bump_const(REPR, "U.UnivResidual.use_cst_eq", "Eq")
(d / "report.json").write_text(json.dumps(rep))
k = next(x for x in replay.replay(d / "report.json", d) if x["source"] == "U.UnivResidual.use_cst_eq")["kernel"]
rc, probs = audit_report(RES, rep, "mut-eq-level")
check(rc != 0 and any(x["detector"] == "instance_levels" for x in probs),
      f"Eq template level raised: auditor's instance_levels detector rejects (kernel: {k})")
M3RUN = ROOT / "runs" / "hu-m3rec"
shutil.rmtree(M3RUN, ignore_errors=True)
rcs = [cli("export", "--manifest", ROOT / "fixtures" / "m3" / "manifest.json", "--roots", "M3.M3Proofs.mirror_mirror,M3.M3Fix.addR_RS",
           "--out", M3RUN)[0], cli("translate", "--input", M3RUN / "source.ndjson", "--out", M3RUN)[0], cli("verify", "--run", M3RUN)[0]]
am = json.loads((M3RUN / "audit.json").read_text())
cm = json.loads((M3RUN / "consumer_result.json").read_text())
check(rcs == [0, 0, 0] and am["instance_levels"]["checked"] > 0 and cm["instance_levels_checked"] >= am["instance_levels"]["checked"],
      f"M3 (mirror_mirror, addR_RS): auditor determined {am['instance_levels']} recursor/Eq levels; consumer checked {cm['instance_levels_checked']}")
M3REP = json.loads((M3RUN / "translation_report.json").read_text())
d = M3RUN / "mut-rec-level"
shutil.rmtree(d, ignore_errors=True)
d.mkdir()
rep = bump_const(M3REP, "M3.M3Fix.addR", "Rocq.M3.M3Types.RNat.rec", "target_value")
(d / "report.json").write_text(json.dumps(rep))
k = next(x for x in replay.replay(d / "report.json", d) if x["source"] == "M3.M3Fix.addR")["kernel"]
rc, probs = audit_report(M3RUN, rep, "mut-rec-level")
check(k == "REJECTED" and rc != 0 and any(x["detector"] == "instance_levels" for x in probs),
      f"recursor motive level raised (RNat.rec in addR): kernel {k}, auditor instance_levels rejects")

# (9) MetaRocq's own constraint record must be entailed by the native graph.
lines = [json.loads(l) for l in open(RUN / "source.ndjson")]
lines[3]["constraints"].append({"l": {"k": "global", "n": ub}, "rel": {"k": "le", "offset": 1}, "r": {"k": "global", "n": ua}})
d = RUN / "facts-metarocq-constraint"
shutil.rmtree(d, ignore_errors=True)
d.mkdir()
(d / "source.ndjson").write_text("".join(json.dumps(x) + "\n" for x in lines))
env = dict(os.environ, PATH=f"{Path.home()}/.local/bin:" + os.environ["PATH"])
p = subprocess.run(["opam", "exec", "--switch=" + SWITCH, "--", sys.executable, "-I", str(ROOT / "tools" / "roundtrip.py"),
                    str(d / "source.ndjson"), str(d), "-Q", str(MAN.parent), "U", "--", "U.Univ"],
                   capture_output=True, text=True, env=env)
check(p.returncode != 0 and "is not entailed by the native facts" in p.stdout,
      "invented MetaRocq constraint (ub < ua) rejected by the native round trip (not entailed)")
finish("test-universe-audit")

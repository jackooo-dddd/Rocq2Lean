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
from lib import ROOT, audit_report, check, cli, finish, results  # noqa: E402
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
    p = subprocess.run(["opam", "exec", "--switch=rocq930", "--", sys.executable, "-I", str(ROOT / "tools" / "roundtrip.py"),
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

# (6) Strict inclusion that the generalized translation cannot express: honest rejection.
big = ROOT / "runs" / "hu-univ-big"
shutil.rmtree(big, ignore_errors=True)
assert cli("export", "--manifest", MAN, "--roots", "U.Univ.big", "--out", big)[0] == 0
rc, _ = cli("translate", "--input", big / "source.ndjson", "--out", big)
R, _ = results(big)
check(rc != 0 and R["U.Univ.big"]["status"] in ("KERNEL_REJECTED", "UNIVERSE_REJECTED"),
      f"Type@{{ub}} : Type@{{uc}} (strict inclusion) rejected honestly ({R['U.Univ.big']['status']}) — documented limitation")
finish("test-universe-audit")

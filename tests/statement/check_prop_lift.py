"""Rule P (docs/PROP_LIFT.md, approved 2026-10-15): a proposition used at a type (Rocq's Prop ≤ Type
cumulativity) is lifted by Lean's core `PULift`. Fixture fixtures/stmt/plift (synthetic, the shapes of
CoqEAL's `fun_hrel` / `Rnat` refinement relations), through the real exporter and translator.

1. Pipeline: export, translate, validate (consumer, audit).
2. Positive: every fixture declaration claimed, with the rule's four shapes:
   * value lift (`frel := fun … => PULift (f b = a)`, `prop_lift` = 5);
   * term level, `PULift.up` (`r1`: a proof used as an inhabitant of `R 1 0`; `r2`: at `pick`'s argument),
     η-transport (`r_succ`'s η-reduced proof body), `PULift.down` (`dmatch`: a match on `h : R a b`);
   * a lifted obligation statement stated as its proposition (`r2`'s obligation: the head chain `R`,
     `frel` δβ-inlined, `prop_lift_unfold`).
3. Negative (forged rows; kernel- and/or audit-rejected):
   * the value lift at a wrong level (not the image of the source sort);
   * a lift depth that does not reach the source's `Type`;
   * a lift reported on a definition whose source type ends in no sort (no cumulativity there);
   * the lift of a type (`PULift.{_, 0} Nat`: kernel-rejected);
   * a coercion in a row that reports none;
   * a coercion at a non-Prop universe (`PULift.up.{r, 1}`);
   * a statement unfolding that is not the source's head chain, and one reported on a definition.
4. Correspondence C1–C5 (tests/statement/proofs/prop_lift_correspondence.lean), checked without axioms;
   unit controls on the audit's η and coercion peeling.

Writes reports/statement_only/test_prop_lift.json.
"""
import copy
import json
import os
import shutil
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from lib import ROOT, audit_report, check, cli, finish, forge_run, results  # noqa: E402

import importlib.util  # noqa: E402
_spec = importlib.util.spec_from_file_location("r2l_audit", ROOT / "tools" / "audit.py")
A = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(A)

OUT = {}
RUN = ROOT / "runs" / "st-plift"
F = "SF.Plift."
ROOTS = [F + x for x in ("frel", "R", "r1", "back", "r_succ", "refine_one", "refine_back", "r2", "dmatch")]
CLAIMED = ("TRANSLATED_AND_CHECKED", "STATEMENT_KERNEL_CHECKED", "PENDING_KERNEL_CHECKED", "STATEMENT_PENDING_KERNEL_CHECKED")

# 1. pipeline
shutil.rmtree(RUN, ignore_errors=True)
rcs = [cli("export", "--mode", "statement", "--manifest", ROOT / "fixtures/stmt/plift/manifest.json",
           "--roots", ",".join(ROOTS), "--out", RUN)[0]]
rcs.append(cli("translate", "--input", RUN / "source.ndjson", "--out", RUN)[0])
rcs.append(cli("validate", "--run", RUN)[0])
v = json.loads((RUN / "validate.json").read_text())
R, rep = results(RUN)
OUT["pipeline"] = {"exit_codes": rcs, "validation": v.get("status"), "by_validation": v.get("by_validation")}
check(rcs[0] == 0 and rcs[2] == 0 and v.get("status") == "STATEMENT_VALIDATED", "fixture: validated (consumer and audit)")

# 2. positive
fx = {n: r for n, r in R.items() if n.startswith(F)}
OUT["rows"] = {n: {k: r.get(k) for k in ("status", "prop_lift", "prop_lift_coercions", "prop_lift_unfold")} for n, r in fx.items()}
check(all(r["status"] in CLAIMED for r in fx.values()), f"every fixture declaration claimed ({len(fx)})")
check(R[F + "frel"].get("prop_lift") == 5, "frel: value lifted under its 5 binders (prop_lift = 5)")
for n in ("r1", "r2", "r_succ", "dmatch"):
    check((R[F + n].get("prop_lift_coercions") or 0) >= 1, f"{n}: term-level coercion inserted ({R[F + n].get('prop_lift_coercions')})")
check(R[F + "r2__rocq2lean_obligation_1"].get("prop_lift_unfold") == [F + "R", F + "frel"],
      "r2's obligation (expected type R 1 0): stated as the proposition, head chain [R, frel] inlined")
check(not any(R[F + n].get("prop_lift") or R[F + n].get("prop_lift_coercions") or R[F + n].get("prop_lift_unfold")
              for n in ("R", "pick", "refines", "back")),
      "no lift where none is needed (R, pick, refines, back)")


def nodes(j, pred, acc=None):
    acc = [] if acc is None else acc
    if isinstance(j, dict):
        if pred(j):
            acc.append(j)
        for x in j.values():
            nodes(x, pred, acc)
    elif isinstance(j, list):
        for x in j:
            nodes(x, pred, acc)
    return acc


is_const = lambda name: (lambda j: j.get("k") == "const" and j.get("n") == name)


# 3. negative: forged rows
def forge(label, row, edit):
    rep2 = copy.deepcopy(rep)
    rows = {x["source"]: x for x in rep2["results"]}
    edit(rows[row])
    d, _, rc, cons, aud = forge_run(RUN, label, rep2, check_cmd="validate")
    # (when the consumer stops first, e.g. on a kernel-rejected row, the audit is run directly)
    aprobs = aud.get("problems") if aud else audit_report(d, rep2, "forged")[1]
    probs = [p_["message"][:300] for p_ in aprobs if p_["message"].startswith(row + ":")]
    rp = d / "lean" / "replay.json"
    replay = {x["source"]: x["kernel"] for x in json.loads(rp.read_text())["results"]} if rp.exists() else {}
    OUT.setdefault("negative", {})[label] = {"forged_row_kernel": replay.get(row), "validate_exit": rc,
                                             "audit_problems": probs[:4], "consumer": (cons or {}).get("status")}
    return replay.get(row), rc, probs


def lift_level(r):
    pl = nodes(r["target_value"], is_const("PULift"))[0]
    pl["u"][0] = {"k": "succ", "l": pl["u"][0]}


k, rc, probs = forge("lift-wrong-level", F + "frel", lift_level)
check(k != "ACCEPTED" and rc == 2 and any("not the image of the source sort" in p for p in probs),
      f"frel lifted at a wrong level: kernel- and audit-rejected (forged row kernel: {k})")
k, rc, probs = forge("lift-wrong-depth", F + "frel", lambda r: r.update(prop_lift=4))
check(rc == 2 and any("rule P" in p for p in probs), f"frel with a lift depth short of the source's Type: audit-rejected (kernel: {k})")
k, rc, probs = forge("lift-no-cumulativity", F + "pick", lambda r: r.update(prop_lift=3))
check(rc == 2 and any("rule P" in p for p in probs),
      f"a lift reported on pick (source type ends in nat, no cumulativity): audit-rejected (kernel: {k})")


def lift_type(r):
    app = nodes(r["target_value"], lambda j: j.get("k") == "app" and j["f"].get("k") == "const" and j["f"].get("n") == "PULift")[0]
    app["a"] = {"k": "const", "n": "Nat", "u": []}


k, rc, probs = forge("lift-of-type", F + "frel", lift_type)
check(k != "ACCEPTED" and rc == 2, f"PULift.{{_, 0}} of a type (Nat): kernel-rejected (forged row kernel: {k})")
k, rc, probs = forge("coercion-unreported", F + "r1", lambda r: r.update(prop_lift_coercions=0))
check(k == "ACCEPTED" and rc == 2 and probs, f"r1's PULift.up in a row reporting no coercion: kernel-accepted, audit-rejected")


def up_non_prop(r):
    up = nodes(r["target_value"], lambda j: j.get("k") == "const" and j.get("n") in ("PULift.up", "PULift.mk"))
    up[0]["u"][1] = {"k": "succ", "l": {"k": "zero"}}


k, rc, probs = forge("coercion-non-prop", F + "r1", up_non_prop)
check(k != "ACCEPTED" and rc == 2 and any("non-Prop universe" in p for p in probs),
      f"r1's coercion at a non-Prop universe: kernel- and audit-rejected (forged row kernel: {k})")
k, rc, probs = forge("unfold-not-head-chain", F + "r2__rocq2lean_obligation_1", lambda r: r.update(prop_lift_unfold=[F + "R"]))
check(rc == 2 and any("head chain" in p for p in probs), "r2's obligation with an unfolding that is not the head chain: audit-rejected")
k, rc, probs = forge("unfold-on-definition", F + "pick", lambda r: r.update(prop_lift_unfold=[F + "R", F + "frel"]))
check(rc == 2 and any("not a statement" in p for p in probs), "an unfolding reported on a definition (pick): audit-rejected")

# 4. correspondence proofs; unit controls
lean = RUN / "lean"
proof = ROOT / "tests" / "statement" / "proofs" / "prop_lift_correspondence.lean"
(lean / "PropLiftCorrespondence.lean").write_text(proof.read_text())
env = dict(os.environ, PATH=f"{Path.home()}/.elan/bin:" + os.environ["PATH"])
lp = subprocess.run(["lake", "-d", str(ROOT), "env", "printenv", "LEAN_PATH"], capture_output=True, text=True, env=env).stdout.strip()
env["LEAN_PATH"] = f"{lp}:{lean}"
q = subprocess.run(["lean", "PropLiftCorrespondence.lean"], cwd=lean, capture_output=True, text=True, env=env)
outq = q.stdout + q.stderr
n_ax = outq.count("does not depend on any axioms")
OUT["correspondence"] = {"exit": q.returncode, "theorems_without_axioms": n_ax, "output": outq[:2000]}
check(q.returncode == 0 and n_ax == 12 and "sorry" not in outq and "depends on axioms" not in outq,
      f"correspondence C1–C4 and fixture transport proofs: {n_ax} theorems, no axioms")

bv = lambda i: {"k": "bvar", "i": i}
c_ = lambda n: {"k": "const", "n": n, "u": []}
ap = lambda f, a: {"k": "app", "f": f, "a": a}
lam = lambda b: {"k": "lam", "n": "x", "t": c_("T"), "b": b}
up = lambda x, u1=None: ap(ap({"k": "const", "n": "PULift.up", "u": [{"k": "succ", "l": {"k": "zero"}}, u1 or {"k": "zero"}]}, c_("P")), x)
OUT["unit"] = u = {
    "eta_simple": A.peel_eta(lam(ap(c_("f"), bv(0)))) == (c_("f"), 1),
    "eta_coerced": A.peel_eta(lam(lam(up(ap(ap(c_("f"), up(bv(1))), bv(0)))))) == (c_("f"), 2),
    "eta_swapped": A.peel_eta(lam(lam(ap(ap(c_("f"), bv(0)), bv(1))))) is None,
    "eta_missing_arg": A.peel_eta(lam(c_("f"))) is None,
    "peel_up": A.peel_lift_coercion(up(c_("t"))) == c_("t"),
    "peel_other": A.peel_lift_coercion(ap(ap(c_("g"), c_("P")), c_("t"))) is None,
}
try:
    A.peel_lift_coercion(up(c_("t"), {"k": "succ", "l": {"k": "zero"}}))
    u["peel_non_prop_rejected"] = False
except A.Mismatch:
    u["peel_non_prop_rejected"] = True
check(all(u.values()), f"audit η and coercion peeling: {u}")

(ROOT / "reports" / "statement_only" / "test_prop_lift.json").write_text(json.dumps(OUT, indent=1) + "\n")
finish("test-prop-lift")

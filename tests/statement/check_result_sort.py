#!/usr/bin/env python3
"""R3G-F (experimental rule, docs/RESULT_SORT_LEVELS.md): a level that is result-sort-only in a declaration
referenced by a constructor field becomes an implicit universe parameter of the block (R2F-interpreted),
instead of R3″'s 0. Through the real CLI on fixtures/stmt/rs (synthetic Rs.v, MathComp HB's shape) plus
the real MathComp structures and the corpus obligation Builders_32.HB_unnamed_factory_34 obligation 5.

1. Fixture: axE / typeE carry the mixin's result level (and typeE the class's); unify_like (the corpus
   obligation's shape), pack_eta (dependent elimination), mk_op (projections of a constructed instance)
   accepted generic; wrapA's carrier level stays an arity (R3G) level; holder is kernel-rejected as before
   the rule (its field carrier level is defaulted: an existing limitation, reported).
2. Real: hasDecEq.axioms_'s result level eqtype.32 is a parameter of Equality.axioms_ and Equality.type
   (and Equality.axioms_'s eqtype.55 of Equality.type); factory_34 obligation 5 accepted.
3. Negative controls, kernel-accepted, rejected by the independent checks: a genuine carrier level
   claimed as result-sort-only (wrapA, self-reported); a field type changed (axE's mixin level not its
   interpretation); a carrier range changed (typeE's sort field raised by the new level); a dependent use
   narrowed (unify_like's mixin level fixed).
4. Positive control at nonzero universes: fixture and real declarations through the kernel.

Writes reports/statement_only/test_result_sort.json.
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

OUT = {}
RUN = ROOT / "runs" / "st-rs"
OBL = "mathcomp.order.preorder/Order/Builders_32.HB_unnamed_factory_34__rocq2lean_obligation_5"
ROOTS = ["SF.Rs.unify_like", "SF.Rs.pack_eta", "SF.Rs.mk_op", "SF.Rs.holder", "SF.Rs.wrapA",
         "mathcomp.order.preorder.Order.Builders_32.HB_unnamed_factory_34"]

shutil.rmtree(RUN, ignore_errors=True)
rcs = [cli("export", "--mode", "statement", "--manifest", ROOT / "fixtures/stmt/rs/manifest.json",
           "--roots", ",".join(ROOTS), "--out", RUN)[0]]
rcs.append(cli("translate", "--input", RUN / "source.ndjson", "--out", RUN)[0])
rcs.append(cli("validate", "--run", RUN)[0])
v = json.loads((RUN / "validate.json").read_text())
R, rep = results(RUN)
aud0 = json.loads((RUN / "audit.json").read_text())
OUT["pipeline"] = {"exit_codes": rcs, "validation": v.get("status"),
                   "result_sort_implicit_checked": aud0.get("result_sort_implicit_checked")}
check(rcs[0] == 0 and rcs[2] == 0 and v.get("status") == "STATEMENT_VALIDATED", "fixture + MathComp: export/translate/validate")
rsi = lambda n: R[n].get("result_sort_implicit_levels") or []
lv = {n: l for n, l in [(x, None) for x in []]}
src = [json.loads(x) for x in (RUN / "source.ndjson").read_text().splitlines()]
decl = {d["name"]: d for d in src if d.get("kind") in ("constant", "inductive")}
res_lv = lambda n: [e["l"]["n"] for e in decl[n]["bodies"][0]["sort"]["u"]]
OUT["rows"] = {n: {k: R[n].get(k) for k in ("status", "level_params", "implicit_levels", "result_sort_implicit_levels")}
               for n in R if n.startswith("SF.") or n.startswith("mathcomp.boot.eqtype/")}
hd32 = res_lv("SF.Rs.hasDec")[0]
ax55 = res_lv("SF.Rs.axE")[0]
check(rsi("SF.Rs.axE") == [hd32] and sorted(rsi("SF.Rs.typeE")) == sorted([hd32, ax55]),
      "fixture: axE carries the mixin's result level, typeE the mixin's and the class's")
for n in ("SF.Rs.unify_like", "SF.Rs.pack_eta", "SF.Rs.mk_op"):
    check(R[n]["status"] == "STATEMENT_KERNEL_CHECKED", f"{n}: accepted")
check(not rsi("SF.Rs.wrapA") and R["SF.Rs.wrapA"]["status"] == "TRANSLATED_AND_CHECKED",
      "wrapA: its carrier level is an arity (R3G) level, not a result-sort level")
# (entry 14, R3G for field-only classes: holder's field typeE keeps its levels as implicit parameters
# instead of R3″'s 0, which the kernel rejected; the limitation recorded in entry 10 is lifted)
_h = R["SF.Rs.holder"]
check(_h["status"] == "TRANSLATED_AND_CHECKED" and len(_h.get("implicit_levels") or []) >= 2
      and all(("u_" + l.replace(".", "_")) in _h["level_params"] for l in _h.get("implicit_levels") or []),
      "holder: accepted, typeE's levels implicit parameters of the block (R3G for fields; was kernel-rejected under R3″)")
e32 = res_lv("mathcomp.boot.eqtype/hasDecEq.axioms_")[0]
e55 = res_lv("mathcomp.boot.eqtype/Equality.axioms_")[0]
check(rsi("mathcomp.boot.eqtype/Equality.axioms_") == [e32] and sorted(rsi("mathcomp.boot.eqtype/Equality.type")) == sorted([e32, e55]),
      "real: Equality.axioms_ carries eqtype.32, Equality.type eqtype.32 and eqtype.55")
check(R[OBL]["status"] == "STATEMENT_KERNEL_CHECKED", "real: Builders_32.HB_unnamed_factory_34 obligation 5 accepted")
check((aud0.get("result_sort_implicit_checked") or 0) >= 6, "audit: every R3G-F level checked independently")


def subst(j, m):
    if isinstance(j, list):
        return [subst(x, m) for x in j]
    if not isinstance(j, dict):
        return j
    if j.get("k") == "param" and j.get("n") in m:
        return m[j["n"]]
    return {k: subst(x, m) for k, x in j.items()}


def forge(label, edit, srcs):
    rep2 = copy.deepcopy(rep)
    rows = {x["source"]: x for x in rep2["results"]}
    edit(rows)
    d, kernel_ok, rc, cons, aud = forge_run(RUN, label, rep2, check_cmd="validate")
    aprobs = aud.get("problems") if aud else audit_report(d, rep2, "forged")[1]
    probs = [p["message"][:300] for p in aprobs if any(p["message"].startswith(s + ":") for s in srcs)]
    cprobs = [p["message"][:300] for p in cons.get("problems", []) if any(p["message"].startswith(s + ":") for s in srcs)]
    rp = d / "lean" / "replay.json"
    replay = {x["source"]: x["kernel"] for x in json.loads(rp.read_text())["results"]} if rp.exists() else {}
    own_ok = bool(replay) and all(replay.get(s_) == "ACCEPTED" for s_ in srcs)
    OUT.setdefault("negative", {})[label] = {"kernel": kernel_ok, "forged_rows_kernel_accepted": own_ok, "validate_exit": rc,
                                            "audit_problems": probs[:4], "consumer_problems": cprobs[:4],
                                            "dependents_rejected_by_kernel": sorted(k_ for k_, v_ in replay.items() if v_ != "ACCEPTED")[:8]}
    return (kernel_ok or (label in OWN_ONLY and own_ok)), rc, probs, cprobs


# (a forged structure whose dependents were built against the real one: only the forged row itself must
# be kernel-accepted; its dependents' rejection is recorded)
OWN_ONLY = {"typeE-carrier-range", "axE-field-level"}
P = lambda l: "u_" + l.replace(".", "_")
par = lambda l: {"k": "param", "n": P(l)}
# (1) a genuine carrier level claimed as result-sort-only
carrier = R["SF.Rs.wrapA"]["implicit_levels"][0]
k, rc, probs, _ = forge("wrapA-carrier-claimed", lambda rows: rows["SF.Rs.wrapA"].update(result_sort_implicit_levels=[carrier]),
                        ["SF.Rs.wrapA"])
check(k and rc == 2 and any("R3G-F" in p for p in probs),
      "a carrier level claimed as result-sort-only (self-reported): kernel-accepted, audit-rejected")


# (2) axE's field type changed: the mixin level not its interpretation
def field(rows):
    r = rows["SF.Rs.axE"]
    for c in r["target_ctors"]:
        def go(j):
            if isinstance(j, list):
                return [go(x) for x in j]
            if not isinstance(j, dict):
                return j
            if j.get("k") == "const" and j["n"] == R["SF.Rs.hasDec"]["target"]:
                return dict(j, u=[j["u"][0], {"k": "max", "a": par(hd32), "b": par(ax55)}])
            return {k_: go(x) for k_, x in j.items()}
        c["type"] = go(c["type"])


k, rc, probs, _ = forge("axE-field-level", field, ["SF.Rs.axE"])
check(k and rc == 2 and probs, "axE's field at a level that is not its interpretation: the forged axE kernel-accepted, audit-rejected")


# (3) typeE's carrier range changed: the sort field raised by the new level
def carrier_range(rows):
    r = rows["SF.Rs.typeE"]
    c = r["target_ctors"][0]
    t = c["type"]
    t["t"] = {"k": "sort", "l": {"k": "max", "a": t["t"]["l"], "b": {"k": "succ", "l": par(hd32)}}}
    # the class field at the raised carrier
    def go(j):
        if isinstance(j, list):
            return [go(x) for x in j]
        if not isinstance(j, dict):
            return j
        if j.get("k") == "const" and j["n"] == R["SF.Rs.axE"]["target"]:
            u = list(j["u"])
            u[1] = {"k": "max", "a": u[1], "b": par(hd32)}
            u[0] = {"k": "max", "a": u[0], "b": u[1]}
            u[2] = {"k": "max", "a": u[2], "b": u[1]}
            return dict(j, u=u)
        return {k_: go(x) for k_, x in j.items()}
    t["b"] = go(t["b"])
    ar = r["target_type"]
    ar["l"] = {"k": "max", "a": ar["l"], "b": {"k": "succ", "l": {"k": "succ", "l": par(hd32)}}}


k, rc, probs, cprobs = forge("typeE-carrier-range", carrier_range, ["SF.Rs.typeE"])
check(k and rc == 2 and probs and cprobs,
      "typeE's carrier range raised by the new level: the forged typeE kernel-accepted, consumer- and audit-rejected")

# (4) a dependent use narrowed: unify_like's mixin level fixed at 0
ul = R["SF.Rs.unify_like"]
k, rc, probs, _ = forge("unify_like-narrowed", lambda rows: rows["SF.Rs.unify_like"].update(
    target_type=subst(ul["target_type"], {P(hd32): {"k": "zero"}}), target_value=subst(ul["target_value"], {P(hd32): {"k": "zero"}}),
    level_params=[p for p in ul["level_params"] if p != P(hd32)],
    implicit_levels=[l for l in ul.get("implicit_levels") or [] if l != hd32]), ["SF.Rs.unify_like"])
check(k and rc == 2 and probs, "unify_like with its mixin level fixed (no self-report): kernel-accepted, audit-rejected")

# positive control at nonzero universes
lean = RUN / "lean"
POS = f"""import Rocq2LeanOut
open Lean Meta Elab Command
def posInst (n : Name) (tag : String) (base : Nat) : MetaM Unit := do
  let ci ← getConstInfo n
  let us := (List.range ci.levelParams.length).map fun k => Level.ofNat (base + 2 * k + 1)
  addDecl (.defnDecl {{ name := Name.mkSimple ("posctrl_" ++ tag), levelParams := [], type := ← instantiateTypeLevelParams ci.toConstantVal us,
                       value := mkConst n us, hints := .opaque, safety := .safe }})
run_meta posInst `{R["SF.Rs.typeE"]["target"]} "typeE" 2
run_meta posInst `{R["SF.Rs.axE"]["target"]} "axE" 3
run_meta posInst `{R["SF.Rs.unify_like"]["target"]} "unify_like" 1
run_meta posInst `{R["SF.Rs.mk_op"]["target"]} "mk_op" 4
run_meta posInst `{R["mathcomp.boot.eqtype/Equality.type"]["target"]} "Equality_type" 2
run_meta posInst `{R[OBL]["target"]} "obligation" 3
"""
(lean / "PositiveControl.lean").write_text(POS)
env = dict(os.environ, PATH=f"{Path.home()}/.elan/bin:" + os.environ["PATH"])
lp = subprocess.run(["lake", "-d", str(ROOT), "env", "printenv", "LEAN_PATH"], capture_output=True, text=True, env=env).stdout.strip()
env["LEAN_PATH"] = f"{lp}:{lean}"
p = subprocess.run(["lean", "PositiveControl.lean"], cwd=lean, capture_output=True, text=True, env=env)
OUT["positive"] = {"exit": p.returncode, "output": (p.stdout + p.stderr)[:600]}
check(p.returncode == 0, "positive control: fixture and real declarations at nonzero universes")

(ROOT / "reports" / "statement_only" / "test_result_sort.json").write_text(json.dumps(OUT, indent=1) + "\n")
finish("test-result-sort")

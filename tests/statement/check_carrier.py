#!/usr/bin/env python3
"""R-CARRIER (experimental rule, docs/CARRIER_LEVELS.md): per-operand carrier universe levels. Through the
real CLI on fixtures/stmt/cb: the real MathComp declarations (prod_eqType, nat_eqType, Countable /
HB_unnamed_mixin_107, insub, HB_unnamed_factory_57) with two synthetic statements (Cb.v), and a synthetic
eqType / subType hierarchy (CbSyn.v) for the correspondence proofs.

1. Reproduced failures are fixed: pair_nat_refl / pair_nat_in (case B: prod_eqType T nat_eqType),
   HB_unnamed_mixin_107 and its obligations (Countable's carrier), insub (SubType's carriers),
   HB_unnamed_factory_57 (a proof-local level against isSub's motive level); everything validated.
2. Representation: prod_eqType / prodEq name their operands' carrier classes separately (P2), the result
   carrier is their join; nat_eqType's carrier stays Nat (no ULift anywhere); SubType.type's parameter
   carrier is a plain universe parameter (P1, not max(u573, u577)); prod_same (operands equal) keeps one
   carrier (a genuine dependency is not split).
3. Negative controls: accidental pinning (kernel-accepted, audit-rejected); incorrect level
   identification (kernel-accepted, audit-rejected); splitting a genuine dependency (rejected by the
   kernel itself); P1 coupling restored on subT (the forged row kernel-accepted, audit-rejected).
4. Positive controls at mixed nonzero universes (fixture and real declarations), and the synthetic
   correspondence proofs (tests/statement/proofs/carrier_correspondence.lean) checked without axioms.
5. Refinement 5 (equal-level arguments in the generality check): accepted only for source-equal levels.

Writes reports/statement_only/test_carrier.json.
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
RUN = ROOT / "runs" / "st-cb"
EQ = "mathcomp.boot.eqtype."
ROOTS = ["SF.Cb.pair_nat_refl", "SF.Cb.pair_nat_in", "mathcomp.boot.choice.HB_unnamed_mixin_107", EQ + "insub",
         "mathcomp.boot.fintype.HB_unnamed_factory_57", "SF.CbSyn.prod_nat_refl", "SF.CbSyn.insub_some", "SF.CbSyn.prod_same"]
CLAIMED = ("TRANSLATED_AND_CHECKED", "STATEMENT_KERNEL_CHECKED", "PENDING_KERNEL_CHECKED", "STATEMENT_PENDING_KERNEL_CHECKED")

shutil.rmtree(RUN, ignore_errors=True)
rcs = [cli("export", "--mode", "statement", "--manifest", ROOT / "fixtures/stmt/cb/manifest.json",
           "--roots", ",".join(ROOTS), "--out", RUN)[0]]
rcs.append(cli("translate", "--input", RUN / "source.ndjson", "--out", RUN)[0])
rcs.append(cli("validate", "--run", RUN)[0])
v = json.loads((RUN / "validate.json").read_text())
R, rep = results(RUN)
aud0 = json.loads((RUN / "audit.json").read_text())
OUT["pipeline"] = {"exit_codes": rcs, "validation": v.get("status"), "by_validation": v.get("by_validation"),
                   "level_copies_checked": aud0.get("level_copies_checked")}
check(rcs[0] == 0 and rcs[2] == 0 and v.get("status") == "STATEMENT_VALIDATED", "fixture (real MathComp + synthetic): validated")
OUT["rows"] = {n: {k: R[n].get(k) for k in ("status", "level_params", "level_copies", "solved_levels")} for n in ROOTS}
for n, what in (("SF.Cb.pair_nat_refl", "case B: a generic eqType paired with nat_eqType"),
                ("SF.Cb.pair_nat_in", "case B: membership in a sequence of such pairs"),
                ("mathcomp.boot.choice.HB_unnamed_mixin_107", "Countable's subtype mixin (and its obligations)"),
                (EQ + "insub", "insub (SubType's carriers)"),
                ("mathcomp.boot.fintype.HB_unnamed_factory_57", "ordinal's isSub factory (proof-local motive level)")):
    check(R[n]["status"] in CLAIMED, f"{n}: claimed ({what})")
check(all(R[f"mathcomp.boot.choice.HB_unnamed_mixin_107__rocq2lean_obligation_{k}"]["status"] in CLAIMED for k in (2, 4, 8)),
      "HB_unnamed_mixin_107 obligations 2, 4, 8 claimed")
f57 = R["mathcomp.boot.fintype.HB_unnamed_factory_57"]
check(any(x["level"] == EQ + "551" and x["sigma"] == {"k": "param", "n": "u_mathcomp_boot_eqtype_542"}
          for x in f57.get("solved_levels") or []), "factory_57: its body level 551 is isSub's motive level 542 (551 = 542 in the source)")

P = lambda l: "u_" + l.replace(".", "_")
# (eqT's carrier level: the sort of its constructor's first field; its structure level: the other one)
_e = R["SF.CbSyn.eqT"]
CAR = next(l for l in json.loads((RUN / "source.ndjson").read_text().splitlines()[4])["levels"]
           if "u_" + l.replace(".", "_") == _e["target_ctors"][0]["type"]["t"]["l"]["l"]["n"])
STR = next(l for l in json.loads((RUN / "source.ndjson").read_text().splitlines()[4])["levels"]
           if "u_" + l.replace(".", "_") in _e["level_params"] and l != CAR)
OUT["eqT_levels"] = {"carrier": CAR, "structure": STR}
# 2. representation
pe = R[EQ + "Datatypes_prod__canonical__eqtype_Equality"]
cop = {x["level"]: x["copies"] for x in pe.get("level_copies") or []}
check(len(cop.get(EQ + "51", [])) == 2, "prod_eqType: its two operands' carriers are independent copies of eqtype.51")
syn = R["SF.CbSyn.prodEq"]
check({x["level"]: len(x["copies"]) for x in syn.get("level_copies") or []}.get(CAR) == 2,
      "prodEq (synthetic): the two operands' carriers are independent copies")
alltext = json.dumps([[r.get("target_type"), r.get("target_value"), r.get("target_ctors")] for r in rep["results"]])
check("ULift" not in alltext, "no ULift anywhere in the translation (no lifted representation)")
st = R[EQ + "SubType.type"] if (EQ + "SubType.type") in R else R["mathcomp.boot.eqtype/SubType.type"]
dom = st["target_type"]["t"]               # (T : Type u) -> ...: the parameter's sort
check(dom == {"k": "sort", "l": {"k": "succ", "l": {"k": "param", "n": "u_mathcomp_boot_eqtype_573"}}},
      "SubType.type: the parameter carrier is a plain universe parameter (P1), not max(u573, u577)")
ps = R["SF.CbSyn.prod_same"]
check(ps["status"] in CLAIMED and P(CAR) in ps["level_params"]
      and not any(x["level"] == CAR for x in ps.get("level_copies") or []),
      "prod_same (operands equal): one carrier level, the dependency is not split")


def subst(j, m):
    if isinstance(j, list):
        return [subst(x, m) for x in j]
    if not isinstance(j, dict):
        return j
    if j.get("k") == "param" and j.get("n") in m:
        return m[j["n"]]
    return {k: subst(x, m) for k, x in j.items()}


OWN_ONLY = {"subT-coupled"}


def forge(label, edit, srcs):
    rep2 = copy.deepcopy(rep)
    rows = {x["source"]: x for x in rep2["results"]}
    edit(rows)
    d, kernel_ok, rc, cons, aud = forge_run(RUN, label, rep2, check_cmd="validate")
    aprobs = aud.get("problems") if aud else audit_report(d, rep2, "forged")[1]
    probs = [p["message"][:300] for p in aprobs if any(p["message"].startswith(s + ":") for s in srcs)]
    cprobs = [p["message"][:300] for p in cons.get("problems", []) if any(p["message"].startswith(s + ":") for s in srcs)]
    rp = d / "lean" / "replay.json"
    replay = {x["source"]: (x["kernel"], x.get("message", "")[:200]) for x in json.loads(rp.read_text())["results"]} if rp.exists() else {}
    own_ok = bool(replay) and all(replay.get(s_, ("",))[0] == "ACCEPTED" for s_ in srcs)
    OUT.setdefault("negative", {})[label] = {"kernel_all": kernel_ok, "forged_rows_kernel_accepted": own_ok, "validate_exit": rc,
                                            "audit_problems": probs[:4], "consumer_problems": cprobs[:4],
                                            "forged_rows_kernel": {s_: replay.get(s_) for s_ in srcs}}
    return (kernel_ok or (label in OWN_ONLY and own_ok)), own_ok, rc, probs, cprobs


# (1) accidental pinning: prod_nat_refl's generic carrier fixed at 0
pn = R["SF.CbSyn.prod_nat_refl"]


def pin(rows):
    r = rows["SF.CbSyn.prod_nat_refl"]
    m = {P(CAR): {"k": "zero"}}
    r["target_type"], r["target_value"] = subst(r["target_type"], m), subst(r["target_value"], m)
    r["level_params"] = [p for p in r["level_params"] if p != P(CAR)]
    r["implicit_levels"] = [l for l in r.get("implicit_levels") or [] if l != CAR]


k, _, rc, probs, _ = forge("pinned-carrier", pin, ["SF.CbSyn.prod_nat_refl"])
check(k and rc == 2 and any("free in the statement" in p for p in probs),
      "a generic carrier pinned at 0 (no self-report): kernel-accepted, audit-rejected")


# (2) incorrect level identification: one of prodEq's structure-level copies relabelled as a carrier copy
def relabel(rows):
    r = rows["SF.CbSyn.prodEq"]
    m = {P(STR + "__c2"): {"k": "param", "n": P(CAR + "__c2")}}
    r["target_type"], r["target_value"] = subst(r["target_type"], m), subst(r["target_value"], m)
    r["level_params"] = [P(CAR + "__c2") if p == P(STR + "__c2") else p for p in r["level_params"]]
    r["implicit_levels"] = [CAR + "__c2" if l == STR + "__c2" else l for l in r.get("implicit_levels") or []]
    for x in r["level_copies"]:
        if x["level"] == CAR:
            x["copies"] = x["copies"] + [CAR + "__c2"]
        if x["level"] == STR:
            x["copies"] = [c for c in x["copies"] if c != STR + "__c2"]


k, _, rc, probs, _ = forge("misidentified-copy", relabel, ["SF.CbSyn.prodEq"])
check(k and rc == 2 and probs, "a structure-level copy relabelled as a carrier copy: kernel-accepted, audit-rejected")


# (3) splitting a genuine dependency: prod_same's single carrier split between its two operands
def split_dep(rows):
    r = rows["SF.CbSyn.prod_same"]
    v_ = r["target_value"]                        # forall T1 T2, ...: T2's domain gets its own carrier copy
    v_["b"]["t"] = subst(v_["b"]["t"], {P(CAR): {"k": "param", "n": P(CAR + "__c9")}})
    r["level_params"] = r["level_params"] + [P(CAR + "__c9")]


k, own_ok, rc, probs, _ = forge("split-dependency", split_dep, ["SF.CbSyn.prod_same"])
check(not own_ok and rc == 2, "the operands-equal statement with its carrier split: rejected by the kernel (the dependency is enforced)")


# (4) P1 coupling restored: subT's parameter carrier read as max(u31, u32) again
# (subT's parameter carrier: its first binder's sort; its sub sort: the sort of the constructor's first field)
sub = R["SF.CbSyn.subT"]
BASE = sub["target_type"]["t"]["l"]["l"]["n"]
_c = sub["target_ctors"][0]["type"]
for _ in range(2):
    _c = _c["b"]
SORTP = _c["t"]["l"]["l"]["n"]
OUT["subT_levels"] = {"base_carrier": BASE, "sub_sort": SORTP}


def couple(rows):
    r = rows["SF.CbSyn.subT"]
    b = {"k": "max", "a": {"k": "param", "n": BASE}, "b": {"k": "param", "n": SORTP}}
    old = {"k": "sort", "l": {"k": "succ", "l": {"k": "param", "n": BASE}}}
    new = {"k": "sort", "l": {"k": "succ", "l": b}}

    def go(j):
        if isinstance(j, list):
            return [go(x) for x in j]
        if not isinstance(j, dict):
            return j
        if j == old:
            return new
        return {kk: go(x) for kk, x in j.items()}
    r["target_type"] = go(r["target_type"])
    for c in r["target_ctors"]:
        c["type"] = go(c["type"])


k, own_ok, rc, probs, _ = forge("subT-coupled", couple, ["SF.CbSyn.subT"])
check(BASE != SORTP and k and rc == 2 and probs,
      "subT with its carriers coupled again (max(base, sort)): the forged subT kernel-accepted, audit-rejected")

# 4. positive controls at mixed nonzero universes; correspondence proofs
lean = RUN / "lean"
inst = lambda n, base: f'run_meta posInst `{R[n]["target"]} {[base + 2 * k + (k % 2) for k in range(len(R[n]["level_params"]))]} "{n.split(".")[-1]}"'
POS = "\n".join(["import Rocq2LeanOut", "open Lean Meta Elab Command",
                 "def posInst (n : Name) (us : List Nat) (tag : String) : MetaM Unit := do",
                 "  let ci ← getConstInfo n",
                 "  let us := us.map Level.ofNat",
                 "  addDecl (.defnDecl { name := Name.mkSimple (\"posctrl_\" ++ tag), levelParams := [], type := ← instantiateTypeLevelParams ci.toConstantVal us,",
                 "                       value := mkConst n us, hints := .opaque, safety := .safe })"]
                + [inst(n, b) for n, b in (("SF.CbSyn.prodEq", 1), ("SF.CbSyn.prod_nat_refl", 2), ("SF.CbSyn.insubT", 1),
                                           ("SF.CbSyn.subT", 3), (EQ + "Datatypes_prod__canonical__eqtype_Equality", 1),
                                           ("SF.Cb.pair_nat_refl", 2), (EQ + "insub", 1),
                                           ("mathcomp.boot.fintype.HB_unnamed_factory_57", 2))]
                + ["-- natEq's carrier is Nat (definitionally), at the lowest level",
                   "run_meta do",
                   f"  let e := mkApp (mkConst `{R['SF.CbSyn.carrier']['target']} (List.replicate {len(R['SF.CbSyn.carrier']['level_params'])} levelZero)) (mkConst `{R['SF.CbSyn.natEq']['target']} (List.replicate {len(R['SF.CbSyn.natEq']['level_params'])} (Level.ofNat 4)))",
                   "  unless ← Meta.isDefEq e (mkConst ``Nat) do throwError \"natEq's carrier is not Nat\""])
(lean / "PositiveControl.lean").write_text(POS + "\n")
env = dict(os.environ, PATH=f"{Path.home()}/.elan/bin:" + os.environ["PATH"])
lp = subprocess.run(["lake", "-d", str(ROOT), "env", "printenv", "LEAN_PATH"], capture_output=True, text=True, env=env).stdout.strip()
env["LEAN_PATH"] = f"{lp}:{lean}"
p = subprocess.run(["lean", "PositiveControl.lean"], cwd=lean, capture_output=True, text=True, env=env)
OUT["positive"] = {"exit": p.returncode, "output": (p.stdout + p.stderr)[:800]}
check(p.returncode == 0, "positive control: split declarations and statements at mixed nonzero universes; natEq's carrier is Nat")
proof = ROOT / "tests" / "statement" / "proofs" / "carrier_correspondence.lean"
if proof.exists():
    (lean / "CarrierCorrespondence.lean").write_text(proof.read_text())
    q = subprocess.run(["lean", "CarrierCorrespondence.lean"], cwd=lean, capture_output=True, text=True, env=env)
    outq = q.stdout + q.stderr
    n_ax = outq.count("does not depend on any axioms")
    OUT["correspondence"] = {"exit": q.returncode, "theorems_without_axioms": n_ax, "output": outq[:2000]}
    check(q.returncode == 0 and n_ax >= 6 and "sorry" not in outq and "depends on axioms" not in outq,
          f"correspondence proofs: split instances vs lifted common-universe instances ({n_ax} declarations, no axioms)")
else:
    check(False, "correspondence proofs present")

# 5. Refinement 5 (the generality check, audit side; the translator's freeLevelRef is the independent copy):
# an argument max(u_a, u_b) for a referenced level l of a statement is l's reading only when a and b are
# *equal* to l in the source graph (<= both ways). A unit-level control on audit.check_statement_generality
# with synthetic facts: accepted for equal levels; rejected when one summand is merely below l, has an
# offset, or is not an own level (each a specialization the source does not force).
import importlib.util  # noqa: E402
_spec = importlib.util.spec_from_file_location("r2l_audit", ROOT / "tools" / "audit.py")
A = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(A)


def _gen(rels, sigma, own=("SF.a", "SF.b")):
    facts = A.Facts({"levels": ["SF.a", "SF.b", "SF.l", "SF.c"],
                     "relations": [{"l": x, "rel": r, "r": y} for x, r, y in rels]})
    stmt = {"k": "app", "f": {"k": "const", "n": "C", "u": [sigma]}, "a": {"k": "sort", "l": {"k": "zero"}}}
    types = {"C": ({"k": "forall", "t": {"k": "sort", "l": {"k": "zero"}}, "b": {"k": "sort", "l": {"k": "zero"}}},
                   [A.level_param("SF.l")], 0)}
    try:
        A.check_statement_generality(facts, set(own), {"C": ["SF.l"]}, [stmt], {}, types)
        return True
    except A.Mismatch:
        return False


_P = lambda n: {"k": "param", "n": A.level_param(n)}
_MAX = {"k": "max", "a": _P("SF.a"), "b": _P("SF.b")}
_EQ = [("SF.a", "le", "SF.l"), ("SF.l", "le", "SF.a"), ("SF.b", "le", "SF.l"), ("SF.l", "le", "SF.b")]
OUT["equal_level_generality"] = r5 = {
    "equal": _gen(_EQ, _MAX),
    # (since stage 3, entry 13: the general form, equal to l at every model of the facts — a = l, b <= l)
    "one_summand_only_below": _gen(_EQ[:3], _MAX),
    "all_summands_only_below": _gen([_EQ[0], _EQ[2]], _MAX),
    "offset": _gen(_EQ, {"k": "max", "a": _P("SF.a"), "b": {"k": "succ", "l": _P("SF.b")}}),
    "not_own": _gen(_EQ, _MAX, own=("SF.a",)),
}
check(r5["equal"] and r5["one_summand_only_below"] and not (r5["all_summands_only_below"] or r5["offset"] or r5["not_own"]),
      "refinement 5 (general form): max(u_a, u_b) for l accepted only when it equals l at every model of the source facts "
      f"(a = l, b <= l: accepted; both only below, offset, not own: rejected) {r5}")

(ROOT / "reports" / "statement_only" / "test_carrier.json").write_text(json.dumps(OUT, indent=1) + "\n")
finish("test-carrier")

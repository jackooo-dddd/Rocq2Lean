#!/usr/bin/env python3
"""R-SPLIT (experimental rule, docs/LEVEL_SPLIT.md): one source level that is the sort of several
parameter binders, translated with one universe parameter per binder. Through the real CLI on
fixtures/stmt/split (synthetic Split.v; not Prosa).

1. pR (inductive, list_R's shape) and fun_R (definition, map_R's shape) are translated through the
   split view (`level_split` = the source-derived split), as is pR_tail (a split definition passing its
   copies to pR's: `us__s<i> <= us`); the statements using them at carriers of
   independent levels are accepted; the ineligible qR (level also in a constructor argument) and gR
   (level also in the body) are not split, and qR_intro stays refused (binder independence).
2. Negative controls, kernel-accepted, rejected by the independent checks:
   - a forged split of the ineligible gR (self-reported, and with the report field hidden);
   - fun_R's copies exchanged between binders (wrong group mapping);
   - pR_tail with one copy identified with another (a split row whose copies are not all generic);
   - fun_R_id narrowed to the diagonal (its carriers identified: the old shape).
3. Positive control: pR, fun_R and the two statements at off-diagonal nonzero universes, kernel.
4. Correspondence (synthetic, fixture only): tests/statement/proofs/split_correspondence.lean proves
   every off-diagonal instance isomorphic to the diagonal (source) instance at the ULift-ed carriers;
   checked without axioms.

Writes reports/statement_only/test_level_split.json.
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
RUN = ROOT / "runs" / "st-split"
ROOTS = ["SF.Split.pR_intro", "SF.Split.fun_R_id", "SF.Split.qR_intro", "SF.Split.gR", "SF.Split.pR_tail"]

shutil.rmtree(RUN, ignore_errors=True)
rcs = [cli("export", "--mode", "statement", "--manifest", ROOT / "fixtures/stmt/split/manifest.json",
           "--roots", ",".join(ROOTS), "--out", RUN)[0]]
rcs.append(cli("translate", "--input", RUN / "source.ndjson", "--out", RUN)[0])
rcs.append(cli("validate", "--run", RUN)[0])
v = json.loads((RUN / "validate.json").read_text())
R, rep = results(RUN)
aud0 = json.loads((RUN / "audit.json").read_text())
OUT["pipeline"] = {"exit_codes": rcs, "validation": v.get("status"), "level_split_checked": aud0.get("level_split_checked")}
check(rcs[0] == 0 and rcs[2] == 0 and v.get("status") == "STATEMENT_VALIDATED", "fixture: export/translate/validate")
check(aud0.get("level_split_checked") == 3, "audit: three split rows checked against the source-derived split")
OUT["rows"] = {s: {k: R[s].get(k) for k in ("status", "level_params", "level_split")} for s in R if s.startswith("SF.")}
for n in ("SF.Split.pR", "SF.Split.fun_R", "SF.Split.pR_tail"):
    ls = R[n].get("level_split") or []
    check(R[n]["status"] == "TRANSLATED_AND_CHECKED" and len(ls) == 1 and ls[0]["params"] == [0, 1, 2],
          f"{n}: translated through the split view (one level, binders 0, 1, 2)")
for n in ("SF.Split.pR_intro", "SF.Split.fun_R_id"):
    check(R[n]["status"] == "STATEMENT_KERNEL_CHECKED", f"{n}: accepted with carriers at independent levels")
check(len(R["SF.Split.pR_intro"]["level_params"]) == 4 and len(R["SF.Split.fun_R_id"]["level_params"]) == 3,
      "the statements keep one universe parameter per carrier")
for n in ("SF.Split.qR", "SF.Split.gR"):
    check(R[n]["status"] == "TRANSLATED_AND_CHECKED" and not R[n].get("level_split"), f"{n}: not eligible, not split")
qi = R["SF.Split.qR_intro"]
check(qi["status"] == "UNIVERSE_REJECTED" and "binder levels" in qi.get("message", ""),
      "qR_intro (ineligible coupled level) stays refused: binder independence")


def subst(j, m):
    if isinstance(j, list):
        return [subst(x, m) for x in j]
    if not isinstance(j, dict):
        return j
    if j.get("k") == "param" and j.get("n") in m:
        return m[j["n"]]
    return {k: subst(x, m) for k, x in j.items()}


def mentions(j, p):
    return json.dumps(j).count(f'"n": "{p}"')


def forge(label, edit, srcs):
    rep2 = copy.deepcopy(rep)
    rows = {x["source"]: x for x in rep2["results"]}
    edit(rows)
    d, kernel_ok, rc, cons, aud = forge_run(RUN, label, rep2, check_cmd="validate")
    # (validate stops at the consumer: the standalone auditor is run on the forged report as well)
    aprobs = aud.get("problems") if aud else audit_report(d, rep2, "forged")[1]
    probs = [p["message"][:300] for p in aprobs if any(p["message"].startswith(s + ":") for s in srcs)]
    cprobs = [p["message"][:300] for p in cons.get("problems", []) if any(p["message"].startswith(s + ":") for s in srcs)]
    OUT.setdefault("negative", {})[label] = {"kernel": kernel_ok, "validate_exit": rc, "audit_problems": probs[:4],
                                            "consumer_problems": cprobs[:4]}
    return kernel_ok, rc, probs, cprobs


# (1) a split of the ineligible gR: `ug` renamed to a copy per binder, the result sort the join
g = R["SF.Split.gR"]
OUT["gR"] = {"type": g["target_type"], "level_params": g["level_params"]}
src_lines = (RUN / "source.ndjson").read_text().splitlines()
gsrc = next(d for d in map(json.loads, src_lines) if d.get("kind") == "constant" and d.get("name") == "SF.Split.gR")
binder_l = gsrc["type"]["ty"]["s"]["u"][0]["l"]["n"]
pl = "u_" + binder_l.replace(".", "_")


def split_g(rows, report=True):
    r = rows["SF.Split.gR"]
    c0, c1 = pl + "__s0", pl + "__s1"
    t = r["target_type"]           # forall A1 : Type ug, forall A2 : Type ug, Sort (ug + 2)
    t["t"] = subst(t["t"], {pl: {"k": "param", "n": c0}})
    t["b"]["t"] = subst(t["b"]["t"], {pl: {"k": "param", "n": c1}})
    res = t["b"]["b"]
    sc = lambda c: {"k": "succ", "l": {"k": "param", "n": c}}
    res["l"] = {"k": "max", "a": res["l"], "b": {"k": "max", "a": sc(c0), "b": sc(c1)}}
    val = r["target_value"]
    val["t"] = subst(val["t"], {pl: {"k": "param", "n": c0}})
    val["b"]["t"] = subst(val["b"]["t"], {pl: {"k": "param", "n": c1}})
    r["level_params"] = r["level_params"] + [c0, c1]
    if report:
        r["level_split"] = [{"level": binder_l, "params": [0, 1], "copies": [binder_l + "__s0", binder_l + "__s1"]}]


k, rc, probs, _ = forge("gR-split", split_g, ["SF.Split.gR"])
check(k and rc == 2 and any("not the split derived from the source" in p for p in probs),
      "forged split of the ineligible gR (self-reported): kernel-accepted, audit-rejected (eligibility)")
k, rc, probs, _ = forge("gR-split-hidden", lambda rows: split_g(rows, report=False), ["SF.Split.gR"])
check(k and rc == 2 and probs, "the same split with the report field hidden: kernel-accepted, audit-rejected")

# (2) fun_R's copies exchanged between binders 0 and 1 (wrong group mapping); the parameter list and
# fun_R_id's universe arguments adjusted so that every declaration still type-checks
f = R["SF.Split.fun_R"]
s0, s1 = f["level_params"][0], f["level_params"][1]


def swap_refs(j, name):
    if isinstance(j, list):
        return [swap_refs(x, name) for x in j]
    if not isinstance(j, dict):
        return j
    j = {k: swap_refs(x, name) for k, x in j.items()}
    if j.get("k") == "const" and j.get("n") == name:
        u = list(j["u"])
        u[0], u[1] = u[1], u[0]
        j["u"] = u
    return j


def swap(rows):
    r = rows["SF.Split.fun_R"]
    m = {s0: {"k": "param", "n": s1}, s1: {"k": "param", "n": s0}}
    r["target_type"], r["target_value"] = subst(r["target_type"], m), subst(r["target_value"], m)
    u = rows["SF.Split.fun_R_id"]
    u["target_type"], u["target_value"] = swap_refs(u["target_type"], f["target"]), swap_refs(u["target_value"], f["target"])


k, rc, probs, cprobs = forge("funR-swapped", swap, ["SF.Split.fun_R"])
check(k and rc == 2 and any("parameter binder" in p for p in cprobs) and probs,
      "fun_R's copies exchanged between binders: kernel-accepted, consumer- and audit-rejected")

# (2b) a split row whose copy is not kept generic: pR_tail's third copy identified with the first
t = R["SF.Split.pR_tail"]
t0, t2 = t["level_params"][0], t["level_params"][2]


def degenerate(rows):
    r = rows["SF.Split.pR_tail"]
    m = {t2: {"k": "param", "n": t0}}
    r["target_type"], r["target_value"] = subst(r["target_type"], m), subst(r["target_value"], m)
    r["level_params"] = [p_ for p_ in r["level_params"] if p_ != t2]


k, rc, probs, cprobs = forge("pRtail-degenerate", degenerate, ["SF.Split.pR_tail"])
check(k and rc == 2 and any("not a universe parameter" in p for p in probs) and cprobs,
      "a split row with a copy identified with another: kernel-accepted, consumer- and audit-rejected")

# (3) fun_R_id at the diagonal only (its three carrier levels identified: the pre-split shape)
fi = R["SF.Split.fun_R_id"]
a_, b_, c_ = fi["level_params"]


def diag(rows):
    r = rows["SF.Split.fun_R_id"]
    m = {b_: {"k": "param", "n": a_}, c_: {"k": "param", "n": a_}}
    r["target_type"], r["target_value"] = subst(r["target_type"], m), subst(r["target_value"], m)
    r["level_params"] = [a_]
    # (a consistent report: the identified levels are reported solved to the remaining one)
    src_l = {("u_" + l.replace(".", "_")): l for l in json.loads(src_lines[4])["levels"]}
    r.setdefault("solved_levels", []).extend({"level": src_l[p_], "sigma": {"k": "param", "n": a_}} for p_ in (b_, c_))
    r["universe_level_defaults"], r["universe_residuals"] = 0, None


k, rc, probs, _ = forge("funRid-diagonal", diag, ["SF.Split.fun_R_id"])
check(k and rc == 2 and any("binder levels" in p or "not entailed" in p for p in probs),
      "fun_R_id narrowed to the diagonal (no self-report): kernel-accepted, audit-rejected (not forced by the source)")

# (3) positive control: off-diagonal nonzero instances; (4) correspondence proofs, no axioms
lean = RUN / "lean"
POS = f"""import Rocq2LeanOut
open Lean Meta Elab Command
def posInst (n : Name) (us : List Nat) (tag : String) : MetaM Unit := do
  let ci ← getConstInfo n
  let us := us.map Level.ofNat
  addDecl (.defnDecl {{ name := Name.mkSimple ("posctrl_" ++ tag), levelParams := [], type := ← instantiateTypeLevelParams ci.toConstantVal us,
                       value := mkConst n us, hints := .opaque, safety := .safe }})
run_meta posInst `{R["SF.Split.pR"]["target"]} [3, 7, 5, 9] "pR"
run_meta posInst `{f["target"]} [2, 6, 4, 1, 8, 3] "fun_R"
run_meta posInst `{R["SF.Split.pR_intro"]["target"]} [9, 3, 7, 5] "pR_intro"
run_meta posInst `{fi["target"]} [2, 6, 4] "fun_R_id"
"""
(lean / "PositiveControl.lean").write_text(POS)
corr = (ROOT / "tests" / "statement" / "proofs" / "split_correspondence.lean").read_text()
corr += "\n" + "\n".join(f"#print axioms SplitCorrespondence.{n}" for n in ("up", "down", "down_up", "up_down", "fup", "fdown",
                                                                         "fdown_fup", "fup_fdown")) + "\n"
(lean / "SplitCorrespondence.lean").write_text(corr)
env = dict(os.environ, PATH=f"{Path.home()}/.elan/bin:" + os.environ["PATH"])
lp = subprocess.run(["lake", "-d", str(ROOT), "env", "printenv", "LEAN_PATH"], capture_output=True, text=True, env=env).stdout.strip()
env["LEAN_PATH"] = f"{lp}:{lean}"
p = subprocess.run(["lean", "PositiveControl.lean"], cwd=lean, capture_output=True, text=True, env=env)
OUT["positive"] = {"exit": p.returncode, "output": (p.stdout + p.stderr)[:500]}
check(p.returncode == 0, "positive control: pR, fun_R and both statements at off-diagonal nonzero universes")
q = subprocess.run(["lean", "SplitCorrespondence.lean"], cwd=lean, capture_output=True, text=True, env=env)
outq = q.stdout + q.stderr
OUT["correspondence"] = {"exit": q.returncode, "output": outq[:1500]}
check(q.returncode == 0 and outq.count("does not depend on any axioms") == 8 and "sorry" not in outq,
      "correspondence: off-diagonal instances isomorphic to the diagonal at ULift-ed carriers (8 declarations, no axioms)")

(ROOT / "reports" / "statement_only" / "test_level_split.json").write_text(json.dumps(OUT, indent=1) + "\n")
finish("test-level-split")

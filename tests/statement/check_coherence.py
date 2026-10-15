"""Rules R and H (docs/COHERENCE_READINGS.md). Fixture fixtures/stmt/coh: the real exporter and
translator on the real MathComp declarations (choice's sub-type Countable instance, fintype's factory_66
at ordinal) and synthetic statements and definitions (task_ord_affinity: Classic's task_affinity shape).

1. Pipeline: export, translate, validate (consumer, audit).
2. Positive: the Countable instance is generic (no defaulted level); its references read the shared level
   choice.299 as max(u_299, u_577) (577 <= 299 in the source); factory_66, its obligation 1 and the
   synthetic statements are claimed.
3. Negative (forged rows, audit): a raising summand in such a reading (1007 <= 299 not entailed), and the
   reading's u_l dropped on a plain tier (a specialization 299 := 577; the R3-down tier reports lower
   arguments and checks them by R3 only), are audit-rejected (the kernel's verdict is recorded).
4. Unit controls on audit.check_universe_args (the translator's copy is tests/smoke/UniverseRules.lean):
   reading accepted; raising, offset, constant above l, no u_l summand, motive-level parameter and
   proof-local level rejected.
5. Rule H: task_ord_affinity (a generic eqType binder beside prerequisite hypotheses instantiated at
   nat's eqType) is claimed on a plain tier with its binder's carrier generic (u_51; without H it was
   accepted only on the R3-down tier with the binder at carrier 0); a forged raising argument at a
   prerequisite statement is audit-rejected; unit controls: a lower argument for a shared level is
   accepted at a proof task's statement only, a raising one nowhere.

Writes reports/statement_only/test_coherence.json.
"""
import copy
import json
import shutil
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from lib import ROOT, audit_report, check, cli, finish, forge_run, results  # noqa: E402

OUT = {}
RUN = ROOT / "runs" / "st-coh"
CH, FT = "mathcomp.boot.choice.", "mathcomp.boot.fintype."
CNT = CH + "eqtype_sub_type__canonical__choice_Countable"
TA = "SF.Coh.task_ord_affinity"
ROOTS = ["SF.Coh.sub_pickle_refl", "SF.Coh.ord_pickle_refl", TA, CNT, FT + "HB_unnamed_factory_66"]
CLAIMED = ("TRANSLATED_AND_CHECKED", "STATEMENT_KERNEL_CHECKED", "PENDING_KERNEL_CHECKED", "STATEMENT_PENDING_KERNEL_CHECKED")
P = lambda l: "u_" + l.replace(".", "_")

import importlib.util  # noqa: E402
_spec = importlib.util.spec_from_file_location("r2l_audit", ROOT / "tools" / "audit.py")
A = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(A)

# 1. pipeline
shutil.rmtree(RUN, ignore_errors=True)
rcs = [cli("export", "--mode", "statement", "--manifest", ROOT / "fixtures/stmt/coh/manifest.json",
           "--roots", ",".join(ROOTS), "--out", RUN)[0]]
rcs.append(cli("translate", "--input", RUN / "source.ndjson", "--out", RUN)[0])
rcs.append(cli("validate", "--run", RUN)[0])
v = json.loads((RUN / "validate.json").read_text())
R, rep = results(RUN)
OUT["pipeline"] = {"exit_codes": rcs, "validation": v.get("status"), "by_validation": v.get("by_validation")}
check(rcs[0] == 0 and rcs[2] == 0 and v.get("status") == "STATEMENT_VALIDATED", "fixture (real MathComp + synthetic): validated")

# 2. positive
OUT["rows"] = {n: {k: R[n].get(k) for k in ("status", "universe_level_defaults", "universe_lowered")}
               for n in ROOTS + [FT + "HB_unnamed_factory_66__rocq2lean_obligation_1"]}
cnt = R[CNT]
check(cnt["status"] in CLAIMED and not cnt.get("universe_level_defaults"),
      "choice's sub-type Countable instance: claimed with no defaulted level (was 4 defaults on the lowered tier)")
L, M = CH + "299", "mathcomp.boot.eqtype.577"
READ = {"k": "max", "a": {"k": "param", "n": P(L)}, "b": {"k": "param", "n": P(M)}}
occ = [(n, us) for part in ("target_type", "target_value") for n, us in A.const_occurrences(cnt[part], [])]
reads = [n for n, us in occ if any(A.level_nf(u) == A.level_nf(READ) for u in us)]
OUT["reading_references"] = sorted(set(reads))
check(CH + "Countable.type" in "".join(reads) and P(L) in cnt["level_params"],
      "its references to Countable.type read the shared level 299 as max(u_299, u_577), and u_299 stays a parameter")
F = A.Facts(json.loads((RUN / "source.ndjson").read_text().splitlines()[4]))
RAISE = CH + "1007"
check(F.entails(M, L, 0) and not F.entails(L, M, 0) and not F.entails(RAISE, L, 0) and P(RAISE) in cnt["level_params"],
      "source facts: 577 <= 299 (strictly), 1007 <= 299 not entailed")
for n in (FT + "HB_unnamed_factory_66", FT + "HB_unnamed_factory_66__rocq2lean_obligation_1",
          "SF.Coh.ord_pickle_refl", "SF.Coh.sub_pickle_refl"):
    check(R[n]["status"] in CLAIMED, f"{n}: claimed")


# 3. negative: forged readings
def subst_level(j, f):
    if isinstance(j, list):
        return [subst_level(x, f) for x in j]
    if not isinstance(j, dict):
        return j
    if j.get("k") == "const" and "u" in j:
        j = dict(j, u=[f(u) for u in j["u"]])
    return {k: subst_level(x, f) if k != "u" else x for k, x in j.items()}


def forge(label, new, plain=False, row=CNT, edit=None):
    rep2 = copy.deepcopy(rep)
    rows = {x["source"]: x for x in rep2["results"]}
    r = rows[row]
    if plain:                      # the row claims a plain tier (no R3-down lowering report)
        r["universe_lowered"] = False
    if edit is not None:
        edit(r)
    else:
        f = lambda u: new if A.level_nf(u) == A.level_nf(READ) else u
        r["target_type"], r["target_value"] = subst_level(r["target_type"], f), subst_level(r["target_value"], f)
    d, kernel_ok, rc, cons, aud = forge_run(RUN, label, rep2, check_cmd="validate")
    aprobs = aud.get("problems") if aud else audit_report(d, rep2, "forged")[1]
    probs = [p["message"][:300] for p in aprobs if p["message"].startswith(row + ":")]
    rp = d / "lean" / "replay.json"
    replay = {x["source"]: x["kernel"] for x in json.loads(rp.read_text())["results"]} if rp.exists() else {}
    OUT.setdefault("negative", {})[label] = {"kernel_all": kernel_ok, "forged_row_kernel": replay.get(row),
                                            "validate_exit": rc, "audit_problems": probs[:4]}
    return replay.get(row), rc, probs


k, rc, probs = forge("raising-summand", {"k": "max", "a": {"k": "param", "n": P(L)}, "b": {"k": "param", "n": P(RAISE)}})
check(rc == 2 and any("not entailed" in p or "299 is shared" in p for p in probs),
      f"forged max(u_299, u_1007) (raising): audit-rejected (forged row kernel: {k})")
OUT["countable_tier"] = "R3-down" if cnt.get("universe_lowered") else "plain"
# (since stage 3, entry 13, the instance is on a plain tier — shared levels per occurrence; before, on R3-down)
k, rc, probs = forge("no-u_l", {"k": "param", "n": P(M)}, plain=True)
check(rc == 2 and any("299 is shared" in p for p in probs),
      f"forged u_577 for the shared 299 on a plain tier (a specialization, no u_l summand): audit-rejected (forged row kernel: {k})")


# 4. unit controls (audit side)
def _args(rels, sigma, own=("SF.a", "SF.l"), adm=False, own_adm=False, body=None, hyp=False):
    facts = A.Facts({"levels": ["SF.a", "SF.b", "SF.l"], "relations": [{"l": x, "rel": r, "r": y} for x, r, y in rels]})
    e = {"k": "const", "n": "C", "u": [sigma]}
    saved = set(A.HYP_STATEMENTS)
    A.HYP_STATEMENTS.clear()
    if hyp:
        A.HYP_STATEMENTS.add("C")          # C is a proof task's statement (rule H)
    try:
        A.check_universe_args(facts, set(own), {"C": ["SF.l"]}, [e], body=body,
                              admit={"C": {"SF.l"}} if adm else None, own_admit=frozenset({"SF.l"}) if own_adm else frozenset())
        return True
    except A.Mismatch:
        return False
    finally:
        A.HYP_STATEMENTS.clear()
        A.HYP_STATEMENTS.update(saved)


_p = lambda n: {"k": "param", "n": P(n)}
_mx = lambda *xs: xs[0] if len(xs) == 1 else {"k": "max", "a": xs[0], "b": _mx(*xs[1:])}
_S = lambda x, n=1: x if n == 0 else {"k": "succ", "l": _S(x, n - 1)}
FACTS = [("Set", "lt", "SF.a"), ("Set", "lt", "SF.l"), ("SF.a", "le", "SF.l")]
OUT["unit"] = u = {
    "identity": _args(FACTS, _p("SF.l")),
    "reading": _args(FACTS, _mx(_p("SF.l"), _p("SF.a"))),
    "reading_reordered": _args(FACTS, _mx(_p("SF.a"), _p("SF.l"))),
    "reading_with_set1": _args(FACTS, _mx(_p("SF.l"), _S({"k": "zero"}))),
    "raising_summand": _args(FACTS, _mx(_p("SF.l"), _p("SF.b")), own=("SF.b", "SF.l")),
    "offset_summand": _args(FACTS, _mx(_p("SF.l"), _S(_p("SF.a")))),
    "constant_above": _args(FACTS, _mx(_p("SF.l"), _S({"k": "zero"}, 2))),
    "u_l_offset": _args(FACTS, _mx(_S(_p("SF.l")), _p("SF.a"))),
    "no_u_l": _args(FACTS, _p("SF.a")),
    "motive_level": _args(FACTS, _mx(_p("SF.l"), _p("SF.a")), adm=True),
    "proof_local": _args(FACTS, _mx(_p("SF.l"), _p("SF.a")), body={"SF.l": _p("SF.a")}),
}
pos = ("identity", "reading", "reading_reordered", "reading_with_set1")
check(all(u[x] for x in pos) and not any(v_ for x, v_ in u.items() if x not in pos),
      f"unit controls: readings accepted; raising, offset, constant above l, u_l + 1, no u_l, motive level and "
      f"proof-local level rejected {u}")

# 5. rule H
E51 = "mathcomp.boot.eqtype.51"
ta = R[TA]
t = ta["target_type"]
while t.get("k") == "forall" and t["n"].startswith("h_"):
    t = t["b"]
eqT = t["t"] if t.get("k") == "forall" else {}
pos51 = [i for i, l in enumerate(R[EQ_T]["level_params"]) if l == P(E51)] if (EQ_T := "mathcomp.boot.eqtype/Equality.type") in R else []
OUT["task_ord_affinity"] = {"status": ta["status"], "universe_lowered": ta.get("universe_lowered"),
                            "binder_type": eqT, "level_params": ta["level_params"]}
check(ta["status"] in CLAIMED and not ta.get("universe_lowered") and P(E51) in ta["level_params"]
      and eqT.get("n") == "Rocq.mathcomp.boot.eqtype.Equality.type" and {"k": "param", "n": P(E51)} in eqT.get("u", []),
      "rule H: task_ord_affinity claimed on a plain tier, its binder T : Equality.type at the generic carrier u_51")
stmts = {x["target"]: x for x in rep["results"] if x.get("target_kind") == "statement"}
lowered = []
for n, us in A.const_occurrences(ta["target_type"], []):
    if n in stmts:
        for lp, u in zip(stmts[n]["level_params"], us):
            if lp == P(E51) and A.level_nf(u) == A.level_nf({"k": "zero"}):
                lowered.append(n)
OUT["hypotheses_at_carrier_0"] = sorted(set(lowered))
check(bool(lowered), "rule H: some prerequisite hypothesis of task_ord_affinity is instantiated at carrier 0 for the shared 51")


def raise_hyp(r):
    def f(j):
        if isinstance(j, list):
            return [f(x) for x in j]
        if not isinstance(j, dict):
            return j
        if j.get("k") == "const" and j.get("n") in stmts:
            lps = stmts[j["n"]]["level_params"]
            j = dict(j, u=[{"k": "succ", "l": {"k": "param", "n": P(E51)}} if lp == P(E51) and A.level_nf(u) == A.level_nf({"k": "zero"})
                           else u for lp, u in zip(lps, j["u"])])
        return {k: (f(x) if k != "u" else x) for k, x in j.items()}
    r["target_type"], r["target_value"] = f(r["target_type"]), f(r["target_value"])


k, rc, probs = forge("hyp-raising", None, row=TA, edit=raise_hyp)
check(rc == 2 and any("not entailed" in p for p in probs),
      f"rule H: a prerequisite hypothesis forged at u_51 + 1 for the shared 51 (raising): audit-rejected (forged row kernel: {k})")
OUT["unit_h"] = uh = {
    "lower_at_statement": _args(FACTS, _p("SF.a"), hyp=True),
    "set_at_statement": _args(FACTS, {"k": "zero"}, hyp=True),
    "lower_elsewhere": _args(FACTS, _p("SF.a")),
    "raising_at_statement": _args(FACTS, _p("SF.b"), own=("SF.b", "SF.l"), hyp=True),
    "offset_at_statement": _args(FACTS, _S(_p("SF.a")), hyp=True),
}
check(uh["lower_at_statement"] and uh["set_at_statement"] and not (uh["lower_elsewhere"] or uh["raising_at_statement"] or uh["offset_at_statement"]),
      f"rule H unit controls: a lower argument for a shared level accepted at a proof task's statement only; raising and "
      f"offset rejected there {uh}")

(ROOT / "reports" / "statement_only" / "test_coherence.json").write_text(json.dumps(OUT, indent=1) + "\n")
finish("test-coherence")

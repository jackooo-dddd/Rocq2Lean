"""Stage 4 (ITERATION_LOG entry 14): blocks and terminations. Fixture fixtures/stmt/s4: the real exporter
and translator on the real Prosa roots `lcmseq.lcml` (through MathComp's `div.gcdn`),
`paper_model.SystemEvolutions` (a template block) and `definitions.task.concrete_job` (a block whose
field type uses `reverse_coercion`).

1. Pipeline: export, translate, validate (consumer, audit).
2. Positive:
   * B-P (docs/TERMINATION.md): `gcdn` is termination-lowered with a termination statement over the
     prerequisites its call relation mentions (`modn`'s); `lcmn` and the root `lcml` are claimed;
   * R3G for template blocks: `SystemEvolutions` has `JobType`'s 32/55/58 as implicit parameters, every
     universe argument of its parameter types equal to its level at every source model;
   * δβ-inlining of erasing polymorphic definitions: `concrete_job` is claimed with `reverse_coercion`
     inlined, its implicit levels each the argument of a reference for that level.
3. Negative (forged rows, audit-rejected):
   * a termination statement over a hypothesis that is not a prerequisite of its constant;
   * an implicit level of the template block that occurs explicitly in its source;
   * `delta_inlined` naming a definition that is not erasing; the inlining report removed;
   * `concrete_job` with an implicit level that is no reference's argument (the instance at 0).
4. Unit controls on audit.erasing_poly_body.

Writes reports/statement_only/test_blocks.json.
"""
import copy
import json
import shutil
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from lib import ROOT, audit_report, check, cli, finish, forge_run, results  # noqa: E402

import importlib.util  # noqa: E402
_spec = importlib.util.spec_from_file_location("r2l_audit", ROOT / "tools" / "audit.py")
A = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(A)

OUT = {}
RUN = ROOT / "runs" / "st-s4"
LCML, SE, CJ = ("prosa.util.lcmseq.lcml", "prosa.results.transfer_schedulability.paper_model.SystemEvolutions",
                "prosa.implementation.definitions.task.concrete_job")
JT = "prosa.implementation.definitions.task.job_task"
GCD, GCDT = "mathcomp.boot.div.gcdn", "mathcomp.boot.div.gcdn__rocq2lean_termination_1"
RC = "Corelib.Init.Prelude.reverse_coercion"
CLAIMED = ("TRANSLATED_AND_CHECKED", "STATEMENT_KERNEL_CHECKED", "PENDING_KERNEL_CHECKED", "STATEMENT_PENDING_KERNEL_CHECKED")
P = lambda l: "u_" + l.replace(".", "_")

# 1. pipeline
shutil.rmtree(RUN, ignore_errors=True)
rcs = [cli("export", "--mode", "statement", "--manifest", ROOT / "fixtures/stmt/s4/manifest.json",
           "--roots", ",".join([LCML, SE, CJ, JT]), "--out", RUN)[0]]
rcs.append(cli("translate", "--input", RUN / "source.ndjson", "--out", RUN)[0])
rcs.append(cli("validate", "--run", RUN)[0])
v = json.loads((RUN / "validate.json").read_text())
R, rep = results(RUN)
OUT["pipeline"] = {"exit_codes": rcs, "validation": v.get("status"), "by_validation": v.get("by_validation")}
check(rcs[0] == 0 and rcs[2] == 0 and v.get("status") == "STATEMENT_VALIDATED", "fixture (real Prosa + MathComp): validated")
_facts = json.loads((RUN / "source.ndjson").read_text().splitlines()[4])
F = A.Facts(_facts)
SRC = {P(l): l for l in _facts["levels"]}
gen = {}
for r in rep["results"]:
    for n in [r.get("target")] + [c["name"] for c in r.get("target_ctors") or []]:
        if n:
            gen[n] = list(r.get("level_params") or [])

# 2. positive
OUT["rows"] = {n: {k: R[n].get(k) for k in ("status", "pending_hypotheses", "implicit_levels", "delta_inlined", "template")}
               for n in (LCML, SE, CJ, GCD, GCDT)}
g, gt = R[GCD], R[GCDT]
check(g["status"] in CLAIMED and GCDT in (g.get("pending_hypotheses") or []),
      "div.gcdn: termination-lowered, its termination obligation among its hypotheses")
check(gt["status"] == "STATEMENT_PENDING_KERNEL_CHECKED" and gt.get("pending_hypotheses")
      and set(gt["pending_hypotheses"]) <= set(g["pending_hypotheses"]) - {GCDT},
      "B-P: gcdn's termination statement is a pending proof task over prerequisites of gcdn (modn's)")
check(R["mathcomp.boot.div.lcmn"]["status"] in CLAIMED and R[LCML]["status"] in CLAIMED,
      "downstream: lcmn and the root lcml are claimed (were blocked by gcdn's internal error)")


def binder_args_generic(row):
    params = {q: SRC[q] for q in row["level_params"] if q in SRC}
    t = row["target_type"]
    while t.get("k") == "forall" and t["n"].startswith("h_"):
        t = t["b"]
    bad = []
    while t.get("k") == "forall":
        for n, us in A.const_occurrences(t["t"], []):
            for p_, u in zip(gen.get(n, []), us):
                l = SRC.get(p_)
                if l is not None and not A.equal_at_models(F, {**params, p_: l}, u, {"k": "param", "n": p_}):
                    bad.append((t["n"], n, l, u))
        t = t["b"]
    return bad


se = R[SE]
bad = binder_args_generic(se)
OUT["SystemEvolutions_not_generic"] = [str(b)[:200] for b in bad]
check(se["status"] in CLAIMED and se.get("template") and {"mathcomp.boot.eqtype.32", "mathcomp.boot.eqtype.58"} <= set(se.get("implicit_levels") or [])
      and not bad, "R3G for template blocks: SystemEvolutions claimed, JobType's levels implicit parameters, every "
                   "parameter-type argument equal to its level at every source model")
cj = R[CJ]
alltxt = json.dumps([cj.get("target_type"), cj.get("target_ctors")])
check(cj["status"] in CLAIMED and cj.get("delta_inlined") == [RC] and "reverse_coercion" not in alltxt,
      "concrete_job claimed with reverse_coercion δβ-inlined (no occurrence left)")
occ_ok = []
for l in cj.get("implicit_levels") or []:
    found = any(p_ == P(l) and u == {"k": "param", "n": P(l)}
                for e in [cj["target_type"]] + [c["type"] for c in cj["target_ctors"]]
                for n, us in A.const_occurrences(e, []) for p_, u in zip(gen.get(n, []), us))
    occ_ok.append((l, found))
OUT["concrete_job_implicit_as_arguments"] = occ_ok
check(occ_ok and all(f for _, f in occ_ok), "concrete_job: every implicit level is the argument of a reference for that level")


jt = R[JT]
check(jt["status"] in CLAIMED and jt.get("delta_inlined") == [RC] and "reverse_coercion" not in json.dumps([jt.get("target_type"), jt.get("target_value")]),
      "job_task (a constant, entry 15): claimed with reverse_coercion δβ-inlined in its type and value")


# 3. negative: forged rows
def forge(label, row, edit):
    rep2 = copy.deepcopy(rep)
    rows = {x["source"]: x for x in rep2["results"]}
    edit(rows[row], rows)
    d, kernel_ok, rc, cons, aud = forge_run(RUN, label, rep2, check_cmd="validate")
    aprobs = aud.get("problems") if aud else audit_report(d, rep2, "forged")[1]
    probs = [p_["message"][:300] for p_ in aprobs if p_["message"].startswith(row + ":")]
    rp = d / "lean" / "replay.json"
    replay = {x["source"]: x["kernel"] for x in json.loads(rp.read_text())["results"]} if rp.exists() else {}
    OUT.setdefault("negative", {})[label] = {"forged_row_kernel": replay.get(row), "validate_exit": rc, "audit_problems": probs[:4]}
    return replay.get(row), rc, probs


other = next(x["source"] for x in rep["results"] if x["source"].endswith("__rocq2lean_termination_1")
             and x["source"] not in (g.get("pending_hypotheses") or []) and x["source"] != GCDT)


def extra_hyp(r, rows):
    o = rows[other]
    r["pending_hypotheses"] = [other] + r["pending_hypotheses"]
    t = {"k": "const", "n": o["target"], "u": [{"k": "param", "n": q} for q in o.get("level_params") or []]}
    r["target_type"] = {"k": "forall", "n": "h_extra", "t": t, "b": r["target_type"]}
    r["target_value"] = {"k": "lam", "n": "h_extra", "t": t, "b": r["target_value"]}


k, rc, probs = forge("termination-extra-hyp", GCDT, extra_hyp)
check(rc == 2 and any("not prerequisites of its constant" in p_ or "hypothesis" in p_ for p_ in probs),
      f"a termination statement over a hypothesis ({other}) that is not a prerequisite of gcdn: audit-rejected (kernel: {k})")
tmpl = next(iter((se.get("template_params") or [{}])))
tl = tmpl.get("level") if isinstance(tmpl, dict) else None
k, rc, probs = forge("template-implicit-explicit", SE,
                     lambda r, rows: r.update(implicit_levels=sorted((r.get("implicit_levels") or []) + [tl])))
check(tl is not None and rc == 2 and any("occur explicitly in the source" in p_ for p_ in probs),
      f"SystemEvolutions with its template level {tl} reported implicit: audit-rejected (kernel: {k})")
k, rc, probs = forge("delta-not-erasing", CJ, lambda r, rows: r.update(delta_inlined=["prosa.behavior.job.JobType"]))
check(rc == 2 and any("is not an erasing polymorphic definition" in p_ for p_ in probs),
      f"concrete_job with delta_inlined naming a non-erasing definition (JobType): audit-rejected (kernel: {k})")
k, rc, probs = forge("delta-not-erasing-constant", JT, lambda r, rows: r.update(delta_inlined=["prosa.behavior.job.JobType"]))
check(rc == 2 and probs, f"job_task with delta_inlined naming a non-erasing definition: audit-rejected (kernel: {k}) {probs[:1]}")
k, rc, probs = forge("delta-hidden-constant", JT, lambda r, rows: r.update(delta_inlined=[]))
check(rc == 2 and probs, f"job_task with its inlining unreported: audit-rejected (kernel: {k}) {probs[:1]}")
k, rc, probs = forge("delta-hidden", CJ, lambda r, rows: r.update(delta_inlined=[]))
check(rc == 2 and probs, f"concrete_job with its inlining unreported: audit-rejected (kernel: {k}) {probs[:1]}")


def pin32(r, rows):
    # (every reference at 0 for the implicit 32, which stays a parameter: kernel-valid, 32 then stands for
    # nothing, and the instance is specialized — what the fresh-and-default R3-down attempt produced)
    def f(j):
        if isinstance(j, list):
            return [f(x) for x in j]
        if not isinstance(j, dict):
            return j
        if j.get("k") == "param" and j.get("n") == P("mathcomp.boot.eqtype.32"):
            return {"k": "zero"}
        return {kk: f(x) for kk, x in j.items()}
    for c in r["target_ctors"]:
        c["type"] = f(c["type"])
    r["target_type"] = f(r["target_type"])


k, rc, probs = forge("implicit-not-argument", CJ, pin32)
check(rc == 2 and probs, f"concrete_job with the instance's 32 at 0 (its implicit 32 no reference's argument): audit-rejected "
                         f"(kernel: {k}) {probs[:1]}")

# 4. unit controls
decls = {}
for l in (RUN / "source.ndjson").read_text().splitlines():
    try:
        d = json.loads(l)
    except ValueError:
        continue
    if d.get("kind") in ("constant", "inductive"):
        decls[d["name"]] = d
mono = next(n for n, d in decls.items() if d["kind"] == "constant" and d.get("body_state") == "transparent"
            and (d.get("universes") or {}).get("k") == "monomorphic" and d.get("body") is not None)
_var_sort = {"k": "sort", "s": {"k": "type", "u": [{"l": {"k": "var", "i": 0}, "n": 0}]}}
_poly_lv = {"kind": "constant", "name": "SF.poly_sort", "body_state": "transparent",
            "universes": {"k": "polymorphic", "names": [None], "constraints": []},
            "body": {"k": "lam", "n": {"n": "x", "r": "R"}, "ty": _var_sort, "b": _var_sort}}
_poly_opaque = dict(decls[RC], body_state="opaque_present")
OUT["unit"] = u = {"reverse_coercion": A.erasing_poly_body(decls[RC]) is not None,
                   "monomorphic": (mono, A.erasing_poly_body(decls[mono]) is not None),
                   "polymorphic_body_with_levels": A.erasing_poly_body(_poly_lv) is not None,
                   "polymorphic_opaque": A.erasing_poly_body(_poly_opaque) is not None}
check(u["reverse_coercion"] and not (u["monomorphic"][1] or u["polymorphic_body_with_levels"] or u["polymorphic_opaque"]),
      f"erasing_poly_body: reverse_coercion erasing; a monomorphic, a level-using polymorphic and an opaque definition are not {u}")

(ROOT / "reports" / "statement_only" / "test_blocks.json").write_text(json.dumps(OUT, indent=1) + "\n")
finish("test-blocks")

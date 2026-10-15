"""Coherence by unification: shared levels per occurrence (docs/COHERENCE_READINGS.md §6). Fixture
fixtures/stmt/occ: the real exporter and translator on the real Prosa declarations `schedule`, `JobReady`
and `ideal.processor_state` (with their MathComp closure).

1. Pipeline: export, translate, validate (consumer, audit).
2. Positive (generality checked directly: fixture rows are not protected, so the translator's own
   generality refusal does not apply to them):
   * `schedule`: no solved level (its level 22 a parameter; with the corpus-wide facts it is interpreted
     by its R2F reading, not solved to `max (51, 101)`, entry 13);
   * `JobReady`, `processor_state`: every universe argument in their parameters' types equals its level
     at every model of the source facts (no binder range narrowed: `Job`'s carrier 51 and level 32 are
     generic);
   * `ProcessorState`: plain parameters per occurrence with its sort read through R2F (`sort_interp`).
3. Negative (forged rows, audit-rejected):
   * `ProcessorState`'s sort replaced by a sort that is not its R2F reading;
   * `sort_interp` claimed on a block without plain parameters;
   * `JobReady`'s `Job` binder at `JobType` with level 58's reading lacking `u58` (a specialization);
   * a reported R2F interpretation added for `schedule`'s level 22 (`u22` alone) that is not the R2F
     interpretation.
4. Unit controls on audit.equal_at_models (the translator's copy, `equalAtModels`, has #guards in
   tests/smoke/UniverseRules.lean).

Writes reports/statement_only/test_occurrence.json.
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
RUN = ROOT / "runs" / "st-occ"
SCH, JR, PS, PSI = ("prosa.behavior.schedule.schedule", "prosa.behavior.ready.JobReady",
                    "prosa.model.processor.ideal.processor_state", "prosa.behavior.schedule.ProcessorState")
ROOTS = [JR, PS, SCH]
CLAIMED = ("TRANSLATED_AND_CHECKED", "STATEMENT_KERNEL_CHECKED", "PENDING_KERNEL_CHECKED", "STATEMENT_PENDING_KERNEL_CHECKED")
P = lambda l: "u_" + l.replace(".", "_")

# 1. pipeline
shutil.rmtree(RUN, ignore_errors=True)
rcs = [cli("export", "--mode", "statement", "--manifest", ROOT / "fixtures/stmt/occ/manifest.json",
           "--roots", ",".join(ROOTS), "--out", RUN)[0]]
rcs.append(cli("translate", "--input", RUN / "source.ndjson", "--out", RUN)[0])
rcs.append(cli("validate", "--run", RUN)[0])
v = json.loads((RUN / "validate.json").read_text())
R, rep = results(RUN)
OUT["pipeline"] = {"exit_codes": rcs, "validation": v.get("status"), "by_validation": v.get("by_validation")}
check(rcs[0] == 0 and rcs[2] == 0 and v.get("status") == "STATEMENT_VALIDATED", "fixture (real Prosa + MathComp): validated")
_facts = json.loads((RUN / "source.ndjson").read_text().splitlines()[4])
F = A.Facts(_facts)
SRC = {P(l): l for l in _facts["levels"]}       # universe parameter -> source level
# target name -> the source levels of its universe parameters (in order)
gen = {}
for r in rep["results"]:
    for n in [r.get("target")] + [c["name"] for c in r.get("target_ctors") or []]:
        if n:
            gen[n] = list(r.get("level_params") or [])


def binder_args_generic(row):
    """Every universe argument in the row's parameter types (after its hypotheses) equals, at every
    model of the source facts, the level its position stands for."""
    params = {q: SRC[q] for q in row["level_params"] if q in SRC}
    t = row["target_type"]
    while t.get("k") == "forall" and t["n"].startswith("h_"):
        t = t["b"]
    bad = []
    while t.get("k") == "forall":
        for n, us in A.const_occurrences(t["t"], []):
            for p_, u in zip(gen.get(n, []), us):
                l = SRC.get(p_)
                if l is None:
                    continue
                if not A.equal_at_models(F, {**params, p_: l}, u, {"k": "param", "n": p_}):
                    bad.append((t["n"], n, l, u))
        t = t["b"]
    return bad


# 2. positive
sch = R[SCH]
OUT["schedule"] = {k: sch.get(k) for k in ("status", "solved_levels", "universe_level_defaults")}
check(sch["status"] in CLAIMED and not sch.get("solved_levels") and
      (P("prosa.behavior.schedule.22") in sch["level_params"]),
      "schedule: no solved level, 22 a universe parameter (corpus run U3: 22 interpreted by its R2F reading, "
      "where it had been solved to max (51, 101))")
for n in (JR, PS):
    bad = binder_args_generic(R[n])
    OUT.setdefault("binder_generality", {})[n] = {"status": R[n]["status"], "not_equal": [str(b)[:200] for b in bad]}
    check(R[n]["status"] in CLAIMED and not bad,
          f"{n}: claimed, every parameter-type universe argument equals its level at every source model")
psi = R[PSI]
check(psi["status"] in CLAIMED and psi.get("plain_levels") and psi.get("sort_interp"),
      "ProcessorState: plain parameters per occurrence, sort read through R2F (sort_interp)")


# 3. negative: forged rows
def forge(label, row, edit):
    rep2 = copy.deepcopy(rep)
    rows = {x["source"]: x for x in rep2["results"]}
    edit(rows[row])
    d, kernel_ok, rc, cons, aud = forge_run(RUN, label, rep2, check_cmd="validate")
    aprobs = aud.get("problems") if aud else audit_report(d, rep2, "forged")[1]
    probs = [p_["message"][:300] for p_ in aprobs if p_["message"].startswith(row + ":")]
    rp = d / "lean" / "replay.json"
    replay = {x["source"]: x["kernel"] for x in json.loads(rp.read_text())["results"]} if rp.exists() else {}
    OUT.setdefault("negative", {})[label] = {"forged_row_kernel": replay.get(row), "validate_exit": rc, "audit_problems": probs[:4]}
    return replay.get(row), rc, probs


def final_sort(t):
    while t.get("k") == "forall":
        t = t["b"]
    return t


def plain_sort(r):
    final_sort(r["target_type"])["l"] = {"k": "succ", "l": {"k": "param", "n": P("prosa.behavior.schedule.22")}}


k, rc, probs = forge("sort-not-r2f", PSI, plain_sort)
check(rc == 2 and any("sort_interp" in p_ for p_ in probs),
      f"ProcessorState with a sort that is not its R2F reading: audit-rejected (forged row kernel: {k})")
r2f = next(x["source"] for x in rep["results"] if x["kind"] == "inductive" and x["status"] in CLAIMED
           and not x.get("plain_levels") and x.get("level_params"))
k, rc, probs = forge("sort-interp-not-plain", r2f, lambda r: r.update(sort_interp=True))
check(rc == 2 and any("sort_interp reported for a block without plain parameters" in p_ for p_ in probs),
      f"sort_interp claimed on a block without plain parameters ({r2f}): audit-rejected (forged row kernel: {k})")


def drop_u58(r):
    t = r["target_type"]
    while t.get("k") == "forall" and t["n"].startswith("h_"):
        t = t["b"]
    jt = t["t"]               # Job : JobType.{…}
    u = jt["u"][3]
    c, ps = A.level_nf(u)
    keep = [{"k": "param", "n": p_} if k_ == 0 else {"k": "succ", "l": {"k": "param", "n": p_}}
            for p_, k_ in ps if p_ != P("mathcomp.boot.eqtype.58")]
    if not keep:      # (58 plain here: its reading without u58, max (u32, u51 + 1, u55))
        keep = [jt["u"][0], {"k": "succ", "l": jt["u"][1]}, jt["u"][2]]
    acc = keep[0]
    for x in keep[1:]:
        acc = {"k": "max", "a": acc, "b": x}
    jt["u"][3] = acc


k, rc, probs = forge("binder-reading-without-u58", JR, drop_u58)
check(rc == 2 and any("eqtype.58" in p_ and ("is shared" in p_ or "free in the statement" in p_) for p_ in probs),
      f"JobReady's Job binder with 58's reading lacking u58 (a specialization): audit-rejected (forged row kernel: {k})")


def interp_22(r):
    r["level_interp"] = (r.get("level_interp") or []) + [
        {"level": "prosa.behavior.schedule.22", "sigma": {"k": "max", "a": {"k": "param", "n": P("prosa.behavior.schedule.22")},
                                                          "b": {"k": "succ", "l": {"k": "zero"}}}}]


k, rc, probs = forge("interp-not-r2f", SCH, interp_22)
check(rc == 2 and any("interpretation of prosa.behavior.schedule.22" in p_ or "interpreted levels" in p_ for p_ in probs),
      f"schedule with a reported interpretation of 22 that is not its R2F interpretation: audit-rejected (forged row kernel: {k})")

# 4. unit controls (audit side)
_f = A.Facts({"levels": ["SF.a", "SF.b", "SF.l", "SF.e"],
              "relations": [{"l": x, "rel": r_, "r": y} for x, r_, y in
                            [("Set", "lt", "SF.a"), ("SF.a", "le", "SF.l"), ("SF.a", "lt", "SF.l"), ("SF.e", "le", "SF.l"), ("SF.l", "le", "SF.e")]]})
own = {P(x): x for x in ("SF.a", "SF.b", "SF.l", "SF.e")}
_p = lambda n: {"k": "param", "n": P(n)}
_mx = lambda a, b: {"k": "max", "a": a, "b": b}
L = _p("SF.l")
OUT["unit"] = u = {
    "identity": A.equal_at_models(_f, own, L, L),
    "reading": A.equal_at_models(_f, own, _mx(L, _p("SF.a")), L),
    "reading_offset": A.equal_at_models(_f, own, _mx(L, {"k": "succ", "l": _p("SF.a")}), L),
    "source_equal": A.equal_at_models(_f, own, _p("SF.e"), L),
    "raising": A.equal_at_models(_f, own, _mx(L, _p("SF.b")), L),
    "below_only": A.equal_at_models(_f, own, _p("SF.a"), L),
    "foreign": A.equal_at_models(_f, own, {"k": "param", "n": "u_foreign"}, L),
}
pos = ("identity", "reading", "reading_offset", "source_equal")
check(all(u[x] for x in pos) and not any(u[x] for x in u if x not in pos),
      f"equal_at_models: identity, readings (a <= l, a + 1 <= l), source-equal accepted; raising, below only, "
      f"foreign rejected {u}")

(ROOT / "reports" / "statement_only" / "test_occurrence.json").write_text(json.dumps(OUT, indent=1) + "\n")
finish("test-occurrence")

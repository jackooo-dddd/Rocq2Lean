"""P0 focused tests: request stability and public-interface protection (fresh CLI processes).

Request stability (comparable inputs give compatible protected interfaces and consistent
acceptance; binder names are ignored, kernel terms otherwise compared exactly):
  * singleton, combined, reordered and extended requests over JobReady / fintype isFinite.axioms_;
  * the same root under two loaded environments (fintype only / the M6 gate's libraries);
  * a legal reordering of the dependencies of one export (translate-only).
Interface protection:
  * positives: a protected Prosa root and its protected dependencies VERIFIED unchanged; external
    (non-protected) statement specializations still VERIFIED under the checked policy;
  * negatives: a protected declaration that needs a statement specialization is refused as a
    dependency (concrete_job → ArrivalCurvePrefix) and as a requested root; a forged report row
    (specialized protected declaration), a tampered or omitted contract binding, and an altered or
    stale manifest are rejected by the consumer, the audit, verify or export.
"""
import copy
import json
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tests"))
sys.path.insert(0, str(ROOT / "tools"))
from lib import check, cli, finish  # noqa: E402
import protection  # noqa: E402
import rocq2lean  # noqa: E402

FX = ROOT / "fixtures" / "p0"
RUNS = ROOT / "runs"
JOBREADY = "prosa.behavior.ready.JobReady"
ISFINITE = "mathcomp.boot.fintype.isFinite.axioms_"
ISFINITE_K = "mathcomp.boot.fintype/isFinite.axioms_"
FINITE_AXIOM = "mathcomp.boot.fintype.finite_axiom"
REM_IN = "prosa.util.list.rem_in"
ACP = "prosa.implementation.definitions.extrapolated_arrival_curve.ArrivalCurvePrefix"
CONCRETE_JOB = "prosa.implementation.definitions.task.concrete_job"


def request(name, manifest, roots, verify=True):
    d = RUNS / f"p0t-{name}"
    shutil.rmtree(d, ignore_errors=True)
    rc = {"export": cli("export", "--manifest", FX / manifest, "--roots", ",".join(roots), "--out", d)[0]}
    if rc["export"] == 0:
        rc["translate"] = cli("translate", "--input", d / "source.ndjson", "--out", d)[0]
        if verify and rc["translate"] == 0:
            rc["verify"] = cli("verify", "--run", d)[0]
    rep = json.loads((d / "translation_report.json").read_text()) if (d / "translation_report.json").exists() else {"results": []}
    return d, rc, {r["source"]: r for r in rep["results"]}


def alpha(e):
    """Drop binder names (lam/forall/let); constant names and everything else are kept."""
    if isinstance(e, dict):
        return {k: alpha(v) for k, v in e.items() if not (k == "n" and e.get("k") in ("lam", "forall", "let"))}
    if isinstance(e, list):
        return [alpha(x) for x in e]
    return e


def compatible(a, b, only=None):
    """Declarations accepted in both: same level parameters and alpha-equal statements; any declaration
    present in both has the same status. Returns the list of differences."""
    out = []
    for n in sorted(set(a) & set(b)):
        if only and n not in only:
            continue
        x, y = a[n], b[n]
        if x["status"] != y["status"]:
            out.append(f"{n}: {x['status']} vs {y['status']}")
        elif x["status"] == "TRANSLATED_AND_CHECKED" and (
                x.get("level_params") != y.get("level_params") or alpha(x.get("target_type")) != alpha(y.get("target_type"))):
            out.append(f"{n}: different accepted interface")
    return out


def audit(d, rep_path, con_path=None):
    out = Path(tempfile.mkstemp(suffix=".json")[1])
    snap = json.loads((d / "source_snapshot.json").read_text())
    p = subprocess.run([sys.executable, "-I", str(ROOT / "tools" / "audit.py"), snap["ir"], str(con_path or d / "contract.json"),
                        str(rep_path), str(out), str(d / "consumer_result.json")], capture_output=True, text=True)
    res = json.loads(out.read_text()) if out.stat().st_size else {}
    return p.returncode, [x["detector"] for x in res.get("problems", [])]


def consumer(d, rep_path, con_path=None):
    with tempfile.TemporaryDirectory() as td:
        cons, out = Path(td) / "C.lean", Path(td) / "result.json"
        cons.write_text(f'import Rocq2LeanOut\nimport Rocq2Lean.Verify\n#rocq2lean_verify "{con_path or d / "contract.json"}" "{rep_path}" "{out}"\n')
        lp = subprocess.run(["lake", "-d", str(ROOT), "env", "printenv", "LEAN_PATH"], capture_output=True, text=True,
                            env=rocq2lean.lean_env()).stdout.strip()
        env = dict(rocq2lean.lean_env(), LEAN_PATH=f"{lp}:{d / 'lean'}")
        p = subprocess.run([f"{Path.home()}/.elan/bin/lean", str(cons)], capture_output=True, text=True, cwd=d / "lean", env=env)
        res = json.loads(out.read_text()) if out.exists() else {"detectors": {}}
        return p.returncode, res.get("detectors", {})


def main():
    # ---- request stability -------------------------------------------------------------------
    e1, rc1, r1 = request("isfinite-fintype-only", "isfinite_fintype_only.manifest.json", [ISFINITE])
    e2, rc2, r2 = request("isfinite-gate-env", "isfinite_gate_env.manifest.json", [ISFINITE])
    check(rc1.get("verify") == 0 and rc2.get("verify") == 0,
          f"isFinite.axioms_ VERIFIED with only fintype loaded and with the gate's libraries ({rc1}, {rc2})")
    check(not compatible(r1, r2, {FINITE_AXIOM, ISFINITE_K}),
          "finite_axiom / isFinite.axioms_ have the same level parameters and statements in both environments")
    s1, rcs1, rs1 = request("singleton-jobready", "ready.manifest.json", [JOBREADY])
    s2, rcs2, rs2 = request("singleton-isfinite", "ready.manifest.json", [ISFINITE])
    c, rcc, rc_ = request("combined", "ready.manifest.json", [JOBREADY, ISFINITE])
    r, rcr, rr = request("reordered", "ready.manifest.json", [ISFINITE, JOBREADY])
    a, rca, ra = request("added-independent", "ready_list.manifest.json", [JOBREADY, ISFINITE, REM_IN])
    for nm, rc_x in (("singleton JobReady", rcs1), ("singleton isFinite", rcs2), ("combined", rcc), ("reordered", rcr),
                     ("with an added independent root", rca)):
        check(rc_x.get("verify") == 0, f"request {nm}: VERIFIED ({rc_x})")
    prot = set(protection.load()[0]["protected"])
    for nm, x, y in (("singleton/combined", rs1, rc_), ("combined/reordered", rc_, rr), ("combined/added root", rc_, ra),
                     ("singleton isFinite/combined", rs2, rc_)):
        diffs = compatible(x, y)
        check(not diffs, f"{nm}: consistent acceptance and identical accepted interfaces ({diffs[:3]})")
    check(any(n in prot for n in rc_), "the combined request contains protected Prosa declarations")
    # legal reordering of the dependencies of one export (translate-only, fresh process)
    lines = (c / "source.ndjson").read_text().splitlines(keepends=True)
    head, decls, foot = lines[:5], lines[5:-1], lines[-1:]
    recs = [json.loads(l) for l in decls]
    names = {d_["name"] for d_ in recs}
    deps = {d_["name"]: {m for m in (d_.get("deps", {}).get("type", []) + d_.get("deps", {}).get("body", [])) if m in names} for d_ in recs}
    order, done, pending = [], set(), sorted(names, reverse=True)
    while pending:                                    # Kahn with the reverse tie-break: another legal order
        n = next(x for x in pending if deps[x] <= done)
        pending.remove(n)
        order.append(n)
        done.add(n)
    by = {d_["name"]: l for d_, l in zip(recs, decls)}
    o = RUNS / "p0t-reordered-dependencies"
    shutil.rmtree(o, ignore_errors=True)
    o.mkdir(parents=True)
    (o / "source.ndjson").write_text("".join(head + [by[n] for n in order] + foot))
    rco = cli("translate", "--input", o / "source.ndjson", "--out", o)[0]
    ro = {x["source"]: x for x in json.loads((o / "translation_report.json").read_text())["results"]}
    check(order != [d_["name"] for d_ in recs], "the alternative dependency order differs from the exporter's")
    check(rco == 0 and not compatible(rc_, ro), "a legal reordering of the dependencies gives the same acceptance and interfaces")

    # ---- interface protection: positives -----------------------------------------------------
    cres = json.loads((s1 / "consumer_result.json").read_text())
    aud = json.loads((s1 / "audit.json").read_text())
    check(cres["detectors"].get("interface") == "OK" and cres.get("interface_checked", 0) > 0 and aud.get("interface_checked", 0) > 0,
          f"positive: JobReady and its protected dependencies VERIFIED with full statements "
          f"(consumer {cres.get('interface_checked')}, audit {aud.get('interface_checked')} protected declarations checked)")
    x, rcx, rx = request("external-specializations", "specialized.manifest.json",
                         ["Stdlib.Lists.List.length_rev", "Stdlib.Lists.List.in_rev"])
    spec = [n for n, v in rx.items() if v["status"] == "TRANSLATED_AND_CHECKED" and
            (v.get("sort_lowered_levels") or any(y.get("in_type") for y in v.get("r2bp_levels") or []))]
    check(rcx.get("verify") == 0 and spec and not (set(spec) & prot),
          f"positive: {len(spec)} non-protected external statement specializations still VERIFIED (checked policy)")

    # ---- interface protection: negatives -----------------------------------------------------
    n1, rcn1, rn1 = request("concrete-job", "concrete_job.manifest.json", [CONCRETE_JOB], verify=False)
    check(rn1.get(ACP, {}).get("status") == "INTERFACE_REJECTED" and rn1[ACP].get("protected"),
          "negative: ArrivalCurvePrefix (protected) needing R2B-S as a dependency is refused (INTERFACE_REJECTED)")
    check(rn1.get(CONCRETE_JOB, {}).get("status") == "BLOCKED_DEPENDENCY", "negative: concrete_job is honestly blocked by it")
    n2, rcn2, rn2 = request("acp-root", "concrete_job.manifest.json", [ACP], verify=False)
    check(rn2.get(ACP, {}).get("status") == "INTERFACE_REJECTED", "negative: the same declaration as a requested root is refused the same way")
    # forged report: a protected accepted row with a specialized statement
    rep = json.loads((s1 / "translation_report.json").read_text())
    tgt = next(r_ for r_ in rep["results"] if r_.get("protected") and r_["status"] == "TRANSLATED_AND_CHECKED")
    forged = copy.deepcopy(rep)
    for r_ in forged["results"]:
        if r_["source"] == tgt["source"]:
            r_["sort_lowered_levels"] = [{"level": "forged.1", "sigma": {"k": "zero"}}]
    fp = Path(tempfile.mkstemp(suffix=".json")[1])
    fp.write_text(json.dumps(forged))
    rc_a, dets = audit(s1, fp)
    check(rc_a != 0 and "interface" in dets, f"negative: the audit rejects a forged specialized protected row ({tgt['source']})")
    rc_c, cdet = consumer(s1, fp)
    check(rc_c != 0 and cdet.get("interface") == "FAIL", "negative: the consumer rejects the forged specialized protected row")
    # tampered / omitted contract binding
    con = json.loads((s1 / "contract.json").read_text())
    for label, mutate in (("tampered (one protected name removed)", lambda b: dict(b, protected=b["protected"][1:])),
                          ("omitted (no binding)", lambda b: None)):
        t = copy.deepcopy(con)
        t["protection"] = mutate(con["protection"])
        tp = Path(tempfile.mkstemp(suffix=".json")[1])
        tp.write_text(json.dumps(t))
        rc_a, dets = audit(s1, s1 / "translation_report.json", tp)
        rc_c, cdet = consumer(s1, s1 / "translation_report.json", tp)
        check(rc_a != 0 and "interface" in dets and rc_c != 0 and cdet.get("interface") == "FAIL",
              f"negative: {label} contract protection is rejected by the audit and the consumer")
    vt = RUNS / "p0t-tampered-contract"
    shutil.rmtree(vt, ignore_errors=True)
    shutil.copytree(s1, vt, symlinks=True)
    t = copy.deepcopy(con)
    t["protection"]["protected"] = t["protection"]["protected"][1:]
    (vt / "contract.json").write_text(json.dumps(t, indent=1))
    check(cli("verify", "--run", vt)[0] != 0, "negative: verify rejects a run whose contract protection was tampered with")
    # altered and stale manifests
    with tempfile.TemporaryDirectory() as td:
        pin0, m0 = json.loads(protection.PIN.read_text()), json.loads((ROOT / json.loads(protection.PIN.read_text())["manifest"]).read_text())
        saved = protection.PIN
        try:
            mp = Path(td) / "m.json"
            mp.write_text(json.dumps(dict(m0, protected=m0["protected"][1:], count=m0["count"] - 1)))
            pp = Path(td) / "pin.json"
            pp.write_text(json.dumps({"manifest": str(mp), "sha256": pin0["sha256"]}))
            protection.PIN = pp
            try:
                protection.load()
                ok = False
            except protection.ProtectionError as e:
                ok = "altered" in str(e)
            check(ok, "negative: an altered protected-interface manifest is refused")
            mp.write_text(json.dumps(dict(m0, declarations_sha256="0" * 64), indent=1))
            import hashlib
            pp.write_text(json.dumps({"manifest": str(mp), "sha256": hashlib.sha256(mp.read_bytes()).hexdigest()}))
            try:
                protection.load()
                ok = False
            except protection.ProtectionError as e:
                ok = "stale" in str(e)
            check(ok, "negative: a stale protected-interface manifest (inventory changed) is refused")
        finally:
            protection.PIN = saved
    finish("test-p0")


if __name__ == "__main__":
    main()

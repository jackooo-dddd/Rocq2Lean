"""Root/result/dependency contract (hardening P0).

Standalone auditor probes (review counterexamples + required unit cases) and end-to-end report
mutations through `rocq2lean verify`. Every rejection must come from the intended detector;
positive controls must be accepted.
"""
import copy
import hashlib
import json
import shutil
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from lib import ROOT, check, cli, finish  # noqa: E402

MAN = ROOT / "fixtures" / "m3" / "manifest.json"
ROOTS = ["M3.M3Proofs.mirror_mirror", "M3.M3Fix.addR_RS"]
BASE = ROOT / "runs" / "rc-base"
shutil.rmtree(BASE, ignore_errors=True)
assert cli("export", "--manifest", MAN, "--roots", ",".join(ROOTS), "--out", BASE)[0] == 0
assert cli("translate", "--input", BASE / "source.ndjson", "--out", BASE)[0] == 0
rc, _ = cli("verify", "--run", BASE)
check(rc == 0, "positive control: genuine run VERIFIED")
REP = json.loads((BASE / "translation_report.json").read_text())
CON = json.loads((BASE / "contract.json").read_text())
ROOT0 = CON["roots"][0]["canonical"]
DEP = "M3.M3Fix.mirrorR"


def audit(rep, con=CON, name="x"):
    d = ROOT / "runs" / "rc-audit"
    d.mkdir(exist_ok=True)
    (d / f"{name}.report.json").write_text(json.dumps(rep))
    (d / f"{name}.contract.json").write_text(json.dumps(con))
    p = subprocess.run([sys.executable, "-I", str(ROOT / "tools" / "audit.py"), str(BASE / "source.ndjson"),
                        str(d / f"{name}.contract.json"), str(d / f"{name}.report.json"), str(d / f"{name}.audit.json"),
                        str(BASE / "consumer_result.json")],      # kernel recursor metadata (fail closed without it)
                       capture_output=True, text=True)
    out = json.loads((d / f"{name}.audit.json").read_text())
    return p.returncode, [x["detector"] + ": " + x["message"] for x in out["problems"]]


def fail_row(rep, src):
    r = next(x for x in rep["results"] if x["source"] == src)
    r.update(status="UNSUPPORTED_FEATURE", target=None, target_kind="", target_type=None, target_value=None)
    return rep


def expect_reject(name, rep, needle, con=CON):
    rc, probs = audit(rep, con, name)
    hit = any(needle in p for p in probs)
    check(rc != 0 and hit, f"audit rejects {name} via '{needle}'" + ("" if hit else f" — got {probs[:3]}"))


rc, probs = audit(copy.deepcopy(REP), name="correct")
check(rc == 0 and not probs, "audit positive control: correct pair accepted")

# Review counterexamples.
r = copy.deepcopy(REP); r["roots"] = []
expect_reject("roots_empty", r, "report root records disagree")
r = fail_row(copy.deepcopy(REP), ROOT0); r["roots"] = []; r["results"] = [x for x in r["results"] if x["source"] == ROOT0]
expect_reject("no_roots_only_unsupported", r, f"requested root {ROOT0} has status UNSUPPORTED_FEATURE")
r = fail_row(copy.deepcopy(REP), ROOT0)
expect_reject("root_success_result_unsupported", r, f"requested root {ROOT0} has status UNSUPPORTED_FEATURE")
r = fail_row(copy.deepcopy(REP), ROOT0); r["roots"] = [dict(x, status="UNSUPPORTED_FEATURE") for x in r["roots"]]
expect_reject("root_and_result_fail", r, "has status UNSUPPORTED_FEATURE")
# Required unit cases.
r = copy.deepcopy(REP); r["roots"] = r["roots"][1:]
expect_reject("omitted_root", r, "report root records disagree")
r = copy.deepcopy(REP); r["results"].append(copy.deepcopy(r["results"][0]))
expect_reject("duplicate_result", r, "2 result rows")
r = copy.deepcopy(REP); r["roots"].append({"name": "M3.M3Fix.addR", "status": "TRANSLATED_AND_CHECKED"})
expect_reject("extra_root", r, "report root records disagree")
r = copy.deepcopy(REP)
next(x for x in r["roots"] if x["name"] == ROOT0)["status"] = "TRANSLATED_AND_CHECKED"
fail_row(r, ROOT0)
expect_reject("root_result_conflict", r, "report root records disagree")
r = fail_row(copy.deepcopy(REP), DEP)
next(x for x in r["results"] if x["source"] == DEP)["status"] = "NOT_ACCEPTED"
expect_reject("omitted_failed_dependency", r, f"required declaration {DEP} has status NOT_ACCEPTED")
r = copy.deepcopy(REP); r["results"] = [x for x in r["results"] if x["source"] != DEP]
expect_reject("dependency_row_missing", r, f"{DEP}: exported declaration has no result")
r = copy.deepcopy(REP); r["summary"]["translated_dependencies"] += 5
expect_reject("forged_success_count", r, "differs from recomputed")
r = copy.deepcopy(REP)
for x in r["results"]:
    if x["status"] == "TRANSLATED_AND_CHECKED":
        x.update(status="UNSUPPORTED_FEATURE")
expect_reject("zero_accepted", r, "no accepted declaration")
c = copy.deepcopy(CON); c["request"] = []; c["roots"] = []
expect_reject("empty_contract_request", copy.deepcopy(REP), "empty request", c)
c = copy.deepcopy(CON); c["required_closure"] = [x for x in c["required_closure"] if x != DEP]
expect_reject("contract_closure_shrunk", copy.deepcopy(REP), "contract closure differs", c)
r = copy.deepcopy(REP); r["run_id"] = "other-run"
expect_reject("wrong_run_id", r, "report run id differs")
r = copy.deepcopy(REP); x = next(x for x in r["results"] if x["source"] == ROOT0); x["target_value"] = None
expect_reject("success_without_body", r, "success claimed without target type/value")

# Export-side request validation.
for name, roots, needle in [("empty_request", "", "empty root request"),
                            ("duplicate_request", "M3.M3Fix.addR_RS,M3.M3Fix.addR_RS", "duplicate requested roots"),
                            ("whitespace_duplicate", "M3.M3Fix.addR_RS,M3.M3Fix.addR_RS ", "duplicate requested roots"),
                            ("constructor_root", "M3.M3Types.RS", "unsupported root form")]:
    rc, out = cli("export", "--manifest", MAN, "--roots", roots, "--out", ROOT / "runs" / f"rc-{name}")
    check(rc != 0 and needle in out, f"export rejects {name} ('{needle}')" + ("" if needle in out else f" — {out[-200:]}"))
# Two spellings resolving to the same declaration.
rc, out = cli("export", "--manifest", MAN, "--roots", "M3.M3Fix.addR_RS,M3Fix.addR_RS", "--out", ROOT / "runs" / "rc-alias")
check(rc != 0 and "resolve to the same declaration" in out, "export rejects two spellings of one root")


# End-to-end: mutated report with a re-synchronized translation manifest must still fail verify.
def e2e(name, mutate):
    d = ROOT / "runs" / f"rc-e2e-{name}"
    shutil.rmtree(d, ignore_errors=True)
    shutil.copytree(BASE, d, ignore=shutil.ignore_patterns(".rocq2lean.lock"))
    rep = json.loads((d / "translation_report.json").read_text())
    mutate(rep)
    (d / "translation_report.json").write_text(json.dumps(rep))
    tm = json.loads((d / "translation_manifest.json").read_text())
    tm["report_sha256"] = hashlib.sha256((d / "translation_report.json").read_bytes()).hexdigest()
    (d / "translation_manifest.json").write_text(json.dumps(tm))
    rc, out = cli("verify", "--run", d)
    v = json.loads((d / "verify.json").read_text())
    cres = json.loads((d / "consumer_result.json").read_text()) if (d / "consumer_result.json").exists() else {}
    return rc, v["status"], cres.get("detectors", {})


def mut_root_relabel(rep):
    rep["roots"] = []
    fail_row(rep, ROOT0)


def e2e_expect(name, mutate, detector, needle):
    """Full `rocq2lean verify` on a mutated, re-synchronized run: rejected, the consumer's `detector`
    fails, and its problem list contains `needle`."""
    rc, st, dets = e2e(name, mutate)
    probs = json.loads((ROOT / "runs" / f"rc-e2e-{name}" / "consumer_result.json").read_text()).get("problems", [])
    hit = any(p["detector"] == detector and needle in p["message"] for p in probs)
    check(rc == 2 and st == "AUDIT_REJECTED" and dets.get(detector) == "FAIL" and hit,
          f"e2e: {name} rejected by verify (exit {rc}, {st}) via consumer detector '{detector}' ('{needle}')"
          + ("" if hit else f" — got {[(p['detector'], p['message'][:80]) for p in probs][:3]}"))


def set_root(field, value, which=0):
    def f(rep):
        rep["roots"][which][field] = value
    return f


e2e_expect("roots_empty", lambda rep: rep.update(roots=[]), "roots", "0 root record(s)")
e2e_expect("omitted_root", lambda rep: rep.update(roots=rep["roots"][1:]), "roots", "1 root record(s)")
e2e_expect("root_success_result_unsupported", lambda rep: fail_row(rep, ROOT0), "coverage",
           f"({ROOT0}) has status UNSUPPORTED_FEATURE")
e2e_expect("root_record_respelled", set_root("requested", "M3Proofs.mirror_mirror"), "roots", "differs from contract root")
e2e_expect("root_record_retargeted", set_root("name", DEP), "roots", "differs from contract root")
e2e_expect("root_record_status_forged", set_root("status", "UNSUPPORTED_FEATURE"), "roots", "its result row says")
e2e_expect("report_status_forged", lambda rep: rep.update(status="ROOTS_NOT_TRANSLATED"), "roots", "report status")
e2e_expect("duplicate_root_row", lambda rep: rep["results"].append(
    copy.deepcopy(next(x for x in rep["results"] if x["source"] == ROOT0))), "coverage", f"{ROOT0}: 2 result rows")


def zero_accepted(rep):
    for x in rep["results"]:
        if x["status"] == "TRANSLATED_AND_CHECKED":
            x["status"] = "UNSUPPORTED_FEATURE"
    for x in rep["roots"]:
        x["status"] = "UNSUPPORTED_FEATURE"
e2e_expect("zero_accepted", zero_accepted, "coverage", "no accepted declaration")


# A run whose contract *and* snapshot request were emptied consistently (a stronger forgery than the
# report alone) still never verifies: nothing requested means nothing accepted.
d = ROOT / "runs" / "rc-e2e-empty-contract"
shutil.rmtree(d, ignore_errors=True)
shutil.copytree(BASE, d, ignore=shutil.ignore_patterns(".rocq2lean.lock"))
c = json.loads((d / "contract.json").read_text())
c.update(request=[], roots=[], required_closure=[])
(d / "contract.json").write_text(json.dumps(c))
sn = json.loads((d / "source_snapshot.json").read_text())
sn.update(request=[], request_raw=[], contract_sha256=hashlib.sha256((d / "contract.json").read_bytes()).hexdigest())
(d / "source_snapshot.json").write_text(json.dumps(sn))
rc, out = cli("verify", "--run", d)
v = json.loads((d / "verify.json").read_text())
cp = json.loads((d / "consumer_result.json").read_text()).get("problems", []) if (d / "consumer_result.json").exists() else []
check(rc == 2 and v["status"] == "AUDIT_REJECTED" and any("no accepted declaration" in p["message"] for p in cp),
      f"e2e: emptied contract + snapshot request rejected ('no accepted declaration'; verify {v['status']})")


# Translator side: the request recorded in the IR is authoritative; an IR whose roots record is
# empty, duplicated or unresolvable is refused before translation (exit 2, report status).
def ir_with_roots(name, mutate):
    d = ROOT / "runs" / f"rc-ir-{name}"
    shutil.rmtree(d, ignore_errors=True)
    d.mkdir(parents=True)
    lines = [json.loads(l) for l in open(BASE / "source.ndjson")]
    mutate(lines[1]["roots"])
    (d / "source.ndjson").write_text("".join(json.dumps(x) + "\n" for x in lines))
    rc, out = cli("translate", "--input", d / "source.ndjson", "--out", d)
    rep = json.loads((d / "translation_report.json").read_text()) if (d / "translation_report.json").exists() else {}
    return rc, out, rep, (d / "translation_manifest.json").exists()


for name, mutate, needle in [
        ("empty", lambda rs: rs.clear(), "no requested root"),
        ("duplicate", lambda rs: rs.append(dict(rs[0])), "duplicate requested root"),
        ("same_resolution", lambda rs: rs.append(dict(rs[0], requested="M3Proofs.mirror_mirror")), "resolve to the same declaration"),
        ("unknown", lambda rs: rs.append({"requested": "M3.M3Fix.nope", "name": "M3.M3Fix.nope", "term": {"k": "const"}}),
         "is not an exported declaration")]:
    rc, out, rep, tm = ir_with_roots(name, mutate)
    check(rc == 2 and "ROOT_CONTRACT_REJECTED" in out and needle in out and rep.get("status") == "ROOT_CONTRACT_REJECTED"
          and not rep.get("results") and not tm,
          f"translate refuses an IR whose root record is {name} ('{needle}'; exit {rc}; no manifest)")

rc, st, dets = e2e("roots_empty_relabel", mut_root_relabel)
check(rc != 0 and st == "AUDIT_REJECTED" and dets.get("coverage") == "FAIL",
      f"e2e: review exploit (roots emptied, root relabelled) now rejected by the coverage detector ({st}, {dets.get('coverage')})")
rc, st, dets = e2e("dep_relabel", lambda rep: fail_row(rep, DEP))
check(rc != 0 and dets.get("coverage") == "FAIL", "e2e: failed dependency in the closure rejected (coverage)")
rc, st, dets = e2e("dup_row", lambda rep: rep["results"].append(copy.deepcopy(rep["results"][-1])))
check(rc != 0 and dets.get("coverage") == "FAIL", "e2e: duplicate result row rejected (coverage)")
finish("test-root-contract")

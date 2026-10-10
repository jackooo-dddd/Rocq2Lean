"""M5: MathComp 2.6.0 / SSReflect foundation — genuine declarations with their original proof terms.

Positive (public CLI: export with round trip, translate, verify, status):
  * eqType and Boolean reflection (eqP, eq_refl, eq_sym, eqVneq, eqnP, eqnE, andP, orP, negP, idP,
    introT, elimT, iffP), with the HB structure Equality.type, its primitive class record and
    projections, and the canonical nat instance;
  * sequences (count_cat, filter_cat, size_cat, cat0s, cats0, catA, size_map, map_cat, count_filter,
    size_filter, has_count, all_count, count_predT, size_iota, index_iota);
  * finite sums and membership (big_nil, big_cons through the sealed HB.lock implementation of bigop;
    mem_iota through the kernel-validated ssr_have_upoly lowering; mem_cat through mem_pred/predType);
  * the fix-lowering soundness regression (fixtures/fixref) and MathComp computation (Rocq vs Lean).
Negative: the old (unsound) fix lowering as a type-correct mutation through verify; a tampered
sealed implementation and a tampered lowered body (fresh-process round trip); forged solved levels
(R2S) and forged primitive-record status (audit); known blockers reported with dependency paths.
"""
import json
import shutil
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from lib import ROOT, audit_report, check, cli, finish, forge_run, results  # noqa: E402

MAN = ROOT / "fixtures" / "m5" / "manifest.json"
E, S, B, N, G = ("mathcomp.boot.eqtype", "mathcomp.boot.seq", "Corelib.ssr.ssrbool", "mathcomp.boot.ssrnat",
                 "mathcomp.boot.bigop")
SETS = {
    "m5-eq": [f"{E}.{n}" for n in ("eqP", "eq_refl", "eq_sym", "eqVneq")] + [f"{N}.eqnP", f"{N}.eqnE"]
             + [f"{B}.{n}" for n in ("andP", "orP", "negP", "idP", "introT", "elimT", "iffP")],
    "m5-seq": [f"{S}.{n}" for n in ("count_cat", "filter_cat", "size_cat", "cat0s", "cats0", "catA", "size_map",
                                     "map_cat", "count_filter", "size_filter", "has_count", "all_count",
                                     "count_predT", "size_iota")] + [f"{G}.index_iota"],
    "m5-big": [f"{G}.big_nil", f"{G}.big_cons", f"{S}.mem_iota", f"{S}.mem_cat"],
}
RESULTS = {}


def pipeline(name, man, roots):
    run = ROOT / "runs" / name
    shutil.rmtree(run, ignore_errors=True)
    rcs = [cli("export", "--manifest", man, "--roots", ",".join(roots), "--out", run)[0]]
    rcs.append(cli("translate", "--input", run / "source.ndjson", "--out", run)[0] if rcs[0] == 0 else None)
    rcs.append(cli("verify", "--run", run)[0] if rcs[1] == 0 else None)
    rcs.append(cli("status", "--run", run)[0] if rcs[2] == 0 else None)
    R = results(run)[0] if (run / "translation_report.json").exists() else {}
    v = json.loads((run / "verify.json").read_text()) if (run / "verify.json").exists() else {}
    RESULTS[name] = {"roots": {r: R.get(r, {}).get("status") for r in roots}, "exit_codes": rcs,
                     "closure": v.get("required_closure_size")}
    return run, rcs, R


for name, roots in SETS.items():
    run, rcs, R = pipeline(name, MAN, roots)
    check(rcs == [0, 0, 0, 0] and all(R.get(r, {}).get("status") == "TRANSLATED_AND_CHECKED" for r in roots),
          f"{name}: {len(roots)} genuine MathComp/SSReflect roots VERIFIED (closure {RESULTS[name]['closure']}) {rcs}")
eqR = results(ROOT / "runs" / "m5-eq")[0]
cls = eqR.get("mathcomp.boot.eqtype/Equality.axioms_", {})
check(cls.get("primitive_record") is True and eqR.get("mathcomp.boot.eqtype/Equality.type", {}).get("status") == "TRANSLATED_AND_CHECKED"
      and eqR.get("mathcomp.boot.ssrnat.Datatypes_nat__canonical__eqtype_Equality", {}).get("status") == "TRANSLATED_AND_CHECKED",
      "eqType: HB structure Equality.type, its primitive class record Equality.axioms_ and the canonical nat instance translated")
rel = eqR.get("Corelib.ssr.ssrbool.rel", {})
check([x["level"] for x in rel.get("solved_levels", [])] == ["Corelib.ssr.ssrbool.1171"],
      "R2S: Corelib ssrbool.rel's level 1171 is solved by unification (identified with pred's level)")
bigrun = ROOT / "runs" / "m5-big"
src = {d["name"]: d for d in map(json.loads, open(bigrun / "source.ndjson")) if d.get("kind") == "constant"}
sealed = sorted(n for n, d in src.items() if d["body_state"] == "sealed_implementation")
lowered = sorted(n for n, d in src.items() if (d["native"].get("prepared") or {}).get("lowered_ssr_have_upoly"))
rt = json.loads((bigrun / "roundtrip.json").read_text())
check(sealed == ["mathcomp.boot.bigop/bigop.body", "mathcomp.boot.bigop/bigop.unlock"] and lowered
      and rt["status"] == "OK" and all(rt["results"].get(n) == "RT_OK" for n in sealed + lowered),
      f"prepared environment: sealed {[s.split('/')[-1] for s in sealed]}, lowered {[s.split('.')[-1] for s in lowered]}; "
      "fresh-process round trip re-prepared and kernel-re-checked them")
RESULTS["prepared"] = {"sealed": sealed, "lowered": lowered}

# The fix-lowering soundness regression.
fr, rcs, FR = pipeline("m5-fixref", ROOT / "fixtures" / "fixref" / "manifest.json",
                       [f"FR.FixRef.{n}" for n in ("keep_3", "subx_3_3", "subx_5_2", "vlen_2", "sub_3_3")])
check(rcs == [0, 0, 0, 0], f"fixpoint branches mentioning the decreasing argument / an index variable compute correctly "
                           f"(keep 3 = 0, subx 3 3 = 0, vlen = 2, 3 - 3 = 0, by reflexivity) VERIFIED {rcs}")
# The old lowering (decreasing argument = outermost call's argument), as a type-correct mutation of
# `keep`'s zero branch, through the full pipeline: kernel-accepted, consumer OK, structural audit rejects.
dr, _, _ = pipeline("m5-fixref-def", ROOT / "fixtures" / "fixref" / "manifest.json", ["FR.FixRef.keep"])
rep = json.loads((dr / "translation_report.json").read_text())
row = next(x for x in rep["results"] if x["source"] == "FR.FixRef.keep")
v = row["target_value"]                 # λ n. Nat.rec motive mz ms n
app = v["b"]
spine = []
while app["k"] == "app":
    spine.append(app)
    app = app["f"]
spine.reverse()
spine[1]["a"] = {"k": "bvar", "i": 0}   # zero branch: Nat.zero  ->  the outermost n (old unsound rule)
d, kernel_ok, rc, cons, aud = forge_run(dr, "old-lowering", rep)
struct = [p for p in aud.get("problems", []) if p["detector"] == "structure" and p["message"].startswith("FR.FixRef.keep:")]
check(kernel_ok and cons.get("status") == "OK" and rc == 2 and struct,
      "old fix lowering (decreasing argument read as the outermost argument) is kernel-accepted but rejected by the audit through verify")

# Negative: tampered prepared bodies are caught by the fresh-process round trip.
import os  # noqa: E402
import subprocess  # noqa: E402
from lib import SWITCH  # noqa: E402
lines = [json.loads(l) for l in open(bigrun / "source.ndjson")]
for name, key in (("sealed", "mathcomp.boot.bigop/bigop.body"), ("lowered", lowered[0])):
    tl = [dict(x) for x in lines]
    dd = next(x for x in tl if x.get("name") == key)
    dd["body"] = {"k": "cast", "t": dd["body"], "kind": "default", "ty": dd["type"]}   # convertible, but not the prepared body
    out = ROOT / "runs" / f"m5-neg-prepared-{name}"
    shutil.rmtree(out, ignore_errors=True)
    (out / "logs").mkdir(parents=True)
    (out / "source.ndjson").write_text("".join(json.dumps(x) + "\n" for x in tl))
    env = dict(os.environ, PATH=f"{Path.home()}/.local/bin:" + os.environ["PATH"])
    p = subprocess.run(["opam", "exec", "--switch=" + SWITCH, "--", sys.executable, "-I", str(ROOT / "tools" / "roundtrip.py"),
                        str(out / "source.ndjson"), str(out), "-Q", str(MAN.parent), "M5", "--", "M5.M5MC"],
                       capture_output=True, text=True, env=env)
    r2 = json.loads((out / "roundtrip.json").read_text()) if (out / "roundtrip.json").exists() else {}
    check(p.returncode != 0 and r2.get("results", {}).get(key) == "RT_PREPARED_MISMATCH",
          f"tampered {name} body of {key.split('/')[-1].split('.')[-1]} rejected by the fresh-process round trip")

# Negative: forged solved levels / primitive-record status (audit).
eqrun = ROOT / "runs" / "m5-eq"
for nm, decl, mut, det in (
        ("solved-level-forged", "Corelib.ssr.ssrbool.rel",
         lambda r: [x.update(sigma={"k": "zero"}) for x in r["solved_levels"]], "structure"),
        ("primitive-record-forged", "mathcomp.boot.eqtype/Equality.axioms_", lambda r: r.update(primitive_record=False),
         "structure")):
    rep = json.loads((eqrun / "translation_report.json").read_text())
    mut(next(x for x in rep["results"] if x["source"] == decl))
    rc, probs = audit_report(eqrun, rep, nm)
    check(rc == 1 and any(p["detector"] == det and p["message"].startswith(decl) for p in probs),
          f"{nm}: rejected by the audit's '{det}' detector")

# Known blockers with exact dependency paths (inspect).
for root, needle in ((f"{G}.big_ord_recr", None), ("mathcomp.boot.fintype.card_ord", None)):
    rc, out = cli("inspect", "--manifest", MAN, "--roots", root)
    rep = json.loads(out[out.index("{"):out.rindex("}") + 1]) if "{" in out else {"roots": {}}
    v = rep["roots"].get(root, {})
    RESULTS.setdefault("blockers", []).append({"root": root, "status": v.get("status"), "reasons": v.get("reasons"),
                                               "dependency_path": v.get("dependency_path")})
    print(f"NOTE inspect {root}: {v.get('status')} {v.get('reasons')} via "
          f"{' -> '.join(x.split('.')[-1] for x in v.get('dependency_path', []))}")

(ROOT / "reports" / "m5").mkdir(parents=True, exist_ok=True)
(ROOT / "reports" / "m5" / "m5_results.json").write_text(json.dumps(RESULTS, indent=2) + "\n")
finish("test-m5")

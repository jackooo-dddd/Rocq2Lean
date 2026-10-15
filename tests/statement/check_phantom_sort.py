"""Rule Q-a (docs/PHANTOM_SORT.md, approved 2026-10-15; Q-b not adopted): the sort arguments of a phantom
check (HB's `unify T1 T2 t1 t2 s := phantom T1 t1 → phantom T2 t2`) are lowered, per occurrence, to the
types of their values; levels that occur only there are no longer the declaration's. Fixture
fixtures/stmt/phant (synthetic, HB's shape: a check at one common sort over carriers at independent
levels), through the real exporter and translator.

1. Pipeline: export, translate, validate (consumer, audit).
2. Positive: a proof of a phantom check (`id_ph`, HB's `id_phant`) passed at the common sort is lowered
   (`chk_id`'s obligation); `chk` and the statement `chk_stmt` keep independent carrier levels (25, 26) with the common
   sort's level 27 lowered (`phantom_lowered` = [27]); without the rule `chk`'s plain translation identifies
   the carriers (a narrowing) and `chk_stmt` is refused as a specialization. The phantom definition itself and
   a non-phantom check (`notph`, `chk_np`) are untouched.
3. Negative (forged rows): a lowered-level set that is not the phantom-only levels; a lowering reported where
   no phantom check is lowered; a non-sort at a phantom sort position (kernel and audit); a sort that is not
   the value's type (kernel).
4. Equivalence (tests/statement/proofs/phantom_sort_equivalence.lean), checked without axioms; unit controls
   on the audit's independent phantom-definition criterion.

Writes reports/statement_only/test_phantom_sort.json.
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
RUN = ROOT / "runs" / "st-phant"
F = "SF.Phant."
ROOTS = [F + x for x in ("unify", "chk", "chk_stmt", "notph", "chk_np", "id_ph", "chk_id")]
CLAIMED = ("TRANSLATED_AND_CHECKED", "STATEMENT_KERNEL_CHECKED", "PENDING_KERNEL_CHECKED", "STATEMENT_PENDING_KERNEL_CHECKED")
P = lambda l: "u_" + l.replace(".", "_")

# 1. pipeline
shutil.rmtree(RUN, ignore_errors=True)
rcs = [cli("export", "--mode", "statement", "--manifest", ROOT / "fixtures/stmt/phant/manifest.json",
           "--roots", ",".join(ROOTS), "--out", RUN)[0]]
rcs.append(cli("translate", "--input", RUN / "source.ndjson", "--out", RUN)[0])
rcs.append(cli("validate", "--run", RUN)[0])
v = json.loads((RUN / "validate.json").read_text())
R, rep = results(RUN)
OUT["pipeline"] = {"exit_codes": rcs, "validation": v.get("status"), "by_validation": v.get("by_validation")}
check(rcs[0] == 0 and rcs[2] == 0 and v.get("status") == "STATEMENT_VALIDATED", "fixture: validated (consumer and audit)")

# 2. positive
fx = {n: r for n, r in R.items() if n.startswith(F)}
OUT["rows"] = {n: {k: r.get(k) for k in ("status", "level_params", "phantom_lowered")} for n, r in fx.items()}
check(all(r["status"] in CLAIMED for r in fx.values()), f"every fixture declaration claimed ({len(fx)})")
for n in ("chk", "chk_stmt"):
    r = R[F + n]
    check(r.get("phantom_lowered") == [F + "27"] and r.get("level_params") == [P(F + "25"), P(F + "26")],
          f"{n}: carriers at independent levels (25, 26), the check's common sort level 27 lowered")
check(R[F + "chk_id__rocq2lean_obligation_1"].get("phantom_lowered") == [F + "27"],
      "chk_id: the proof of the phantom check (id_ph's shape, HB's id_phant) at the common sort, lowered in its obligation")
check(not any(R[F + n].get("phantom_lowered") for n in ("unify", "notph", "chk_np", "id_ph")),
      "no lowering for the phantom definition itself or a non-phantom check")

# 3. negative: forged rows
def forge(label, row, edit):
    rep2 = copy.deepcopy(rep)
    rows = {x["source"]: x for x in rep2["results"]}
    edit(rows[row])
    d, _, rc, cons, aud = forge_run(RUN, label, rep2, check_cmd="validate")
    aprobs = aud.get("problems") if aud else audit_report(d, rep2, "forged")[1]
    probs = [p_["message"][:300] for p_ in aprobs if p_["message"].startswith(row + ":")]
    rp = d / "lean" / "replay.json"
    replay = {x["source"]: x["kernel"] for x in json.loads(rp.read_text())["results"]} if rp.exists() else {}
    OUT.setdefault("negative", {})[label] = {"forged_row_kernel": replay.get(row), "validate_exit": rc, "audit_problems": probs[:4]}
    return replay.get(row), rc, probs


k, rc, probs = forge("levels-not-phantom-only", F + "chk", lambda r: r.update(phantom_lowered=[F + "25", F + "27"]))
check(rc == 2 and any("phantom" in p for p in probs), f"chk reporting a carrier level as lowered: audit-rejected (kernel: {k})")
k, rc, probs = forge("lowering-without-check", F + "chk_np", lambda r: r.update(phantom_lowered=[F + "27"]))
check(rc == 2 and any("phantom" in p for p in probs), f"a lowering reported on chk_np (no phantom check): audit-rejected (kernel: {k})")


def unify_app(r):
    """The application `unify X1 X2 A B 0` in chk's type: its first sort argument node (holder, key)."""
    t = r["target_type"]
    while t["k"] == "forall":
        if "unify" in json.dumps(t["t"]):
            a = t["t"]
            while a["k"] == "app":
                if a["f"]["k"] == "app" and a["f"]["f"]["k"] == "app" and a["f"]["f"]["f"]["k"] == "app" and \
                        a["f"]["f"]["f"]["f"]["k"] == "app" and a["f"]["f"]["f"]["f"]["f"].get("n", "").endswith("unify"):
                    return a["f"]["f"]["f"]["f"]      # `unify X1`: its argument is X1
                a = a["f"]
        t = t["b"]
    raise AssertionError("no unify application in chk's type")


def non_sort(r):
    unify_app(r)["a"] = {"k": "const", "n": "Nat", "u": []}


k, rc, probs = forge("phantom-arg-not-sort", F + "chk", non_sort)
check(k != "ACCEPTED" and rc == 2 and any("not a sort" in p for p in probs),
      f"chk with a non-sort at a phantom sort position: kernel- and audit-rejected (kernel: {k})")


def wrong_sort(r):
    x = unify_app(r)
    x["a"] = {"k": "sort", "l": {"k": "succ", "l": {"k": "succ", "l": {"k": "param", "n": P(F + "25")}}}}


k, rc, probs = forge("phantom-sort-not-value-type", F + "chk", wrong_sort)
check(k != "ACCEPTED" and rc == 2, f"chk with a sort that is not the value's type: kernel-rejected (kernel: {k})")

# 4. equivalence proofs; unit controls
lean = RUN / "lean"
proof = ROOT / "tests" / "statement" / "proofs" / "phantom_sort_equivalence.lean"
(lean / "PhantomSortEquivalence.lean").write_text(proof.read_text())
env = dict(os.environ, PATH=f"{Path.home()}/.elan/bin:" + os.environ["PATH"])
lp = subprocess.run(["lake", "-d", str(ROOT), "env", "printenv", "LEAN_PATH"], capture_output=True, text=True, env=env).stdout.strip()
env["LEAN_PATH"] = f"{lp}:{lean}"
q = subprocess.run(["lean", "PhantomSortEquivalence.lean"], cwd=lean, capture_output=True, text=True, env=env)
outq = q.stdout + q.stderr
n_ax = outq.count("does not depend on any axioms")
OUT["equivalence"] = {"exit": q.returncode, "theorems_without_axioms": n_ax, "output": outq[:2000]}
check(q.returncode == 0 and n_ax == 6 and "sorry" not in outq and "depends on axioms" not in outq,
      f"equivalence proofs (every phantom check holds; any two instances equivalent): {n_ax} theorems, no axioms")

src = {d["name"]: d for d in map(json.loads, open(RUN / "source.ndjson")) if d.get("kind") in ("constant", "inductive")}
bad = copy.deepcopy(src[F + "unify"])
b = bad["body"]
while b["k"] == "lam":
    b = b["b"]
b["ty"]["args"][1] = {"k": "rel", "i": 3}            # phantom T1 t2: the value is not of the sort parameter
OUT["unit"] = u = {
    "unify_pairs": A.phantom_def_pairs(src[F + "unify"]) == [(0, 2), (1, 3)],
    "id_ph_pairs": A.phantom_def_pairs(src[F + "id_ph"]) == [(0, 1), (0, 1)],
    "notph_none": A.phantom_def_pairs(src[F + "notph"]) is None,
    "chk_none": A.phantom_def_pairs(src[F + "chk"]) is None,
    "mismatched_value_none": A.phantom_def_pairs(bad) is None,
}
check(all(u.values()), f"audit's phantom-definition criterion: {u}")

(ROOT / "reports" / "statement_only" / "test_phantom_sort.json").write_text(json.dumps(OUT, indent=1) + "\n")
finish("test-phantom-sort")

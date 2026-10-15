"""Rule T (docs/COINDUCTIVE.md, approved 2026-10-15): a non-recursive coinductive type (one body, no
constructor argument or index mentioning it) is translated as the Lean inductive; recursive coinductive
types and `cofix` terms stay refused. Fixture fixtures/stmt/coind (synthetic, Classic's `Task_T` shape),
through the real exporter and translator.

1. Pipeline: export, translate, validate (consumer, audit).
2. Positive: `Task_T` (flag `coinductive_as_inductive`), its projections and two lemmas claimed (the
   Rocq-proved η lemma `Task_T_eta`, T1's Rocq side, among them).
3. Negative: the recursive `stream` refused (and `zeros` blocked); the non-recursive cofixpoint `task0`
   refused; forged rows — `Task_T` without the flag, an inductive with the flag — audit-rejected; unit
   controls on the audit's criterion (`stream` rejected as recursive).
4. Correspondence (tests/statement/proofs/coinductive_correspondence.lean), checked without axioms.

Writes reports/statement_only/test_coinductive.json.
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
RUN = ROOT / "runs" / "st-coind"
F = "SF.Coind."
ROOTS = [F + x for x in ("Task_T", "get_P", "get_C", "get_P_build", "Task_T_eta", "stream", "zeros", "task0", "fin2")]
CLAIMED = ("TRANSLATED_AND_CHECKED", "STATEMENT_KERNEL_CHECKED", "PENDING_KERNEL_CHECKED", "STATEMENT_PENDING_KERNEL_CHECKED")

# 1. pipeline
shutil.rmtree(RUN, ignore_errors=True)
rcs = [cli("export", "--mode", "statement", "--manifest", ROOT / "fixtures/stmt/coind/manifest.json",
           "--roots", ",".join(ROOTS), "--out", RUN)[0]]
rcs.append(cli("translate", "--input", RUN / "source.ndjson", "--out", RUN)[0])
rcs.append(cli("validate", "--run", RUN)[0])
v = json.loads((RUN / "validate.json").read_text())
R, rep = results(RUN)
OUT["pipeline"] = {"exit_codes": rcs, "validation": v.get("status"), "by_validation": v.get("by_validation")}
OUT["rows"] = {n: {k: r.get(k) for k in ("status", "coinductive_as_inductive", "message")} for n, r in R.items() if n.startswith(F)}
check(rcs[0] == 0 and rcs[2] == 0 and v.get("status") == "STATEMENT_VALIDATED", "fixture: validated (consumer and audit)")

# 2. positive
check(R[F + "Task_T"]["status"] == "TRANSLATED_AND_CHECKED" and R[F + "Task_T"].get("coinductive_as_inductive") is True,
      "Task_T (non-recursive coinductive): translated as an inductive, reported")
check(all(R[F + n]["status"] in CLAIMED for n in ("get_P", "get_C", "get_P_build", "Task_T_eta")),
      "its projections (matches on the coinductive) and lemmas, the Rocq-proved η lemma among them, claimed")
check(R[F + "fin2"]["status"] in CLAIMED and not R[F + "fin2"].get("coinductive_as_inductive"), "an inductive: unflagged")

# 3. negative
check(R[F + "stream"]["status"] == "UNSUPPORTED_FEATURE" and "recursive coinductive" in R[F + "stream"]["message"]
      and R[F + "zeros"]["status"] not in CLAIMED, "the recursive coinductive stream refused, its cofixpoint not claimed")
check(R[F + "task0"]["status"] == "UNSUPPORTED_FEATURE" and "cofixpoint" in R[F + "task0"]["message"],
      "a cofixpoint of the non-recursive type (no guarded call) stays refused")


def forge(label, row, edit):
    rep2 = copy.deepcopy(rep)
    rows = {x["source"]: x for x in rep2["results"]}
    edit(rows[row])
    d, _, rc, cons, aud = forge_run(RUN, label, rep2, check_cmd="validate")
    aprobs = aud.get("problems") if aud else audit_report(d, rep2, "forged")[1]
    probs = [p_["message"][:300] for p_ in aprobs if p_["message"].startswith(row + ":")]
    OUT.setdefault("negative", {})[label] = {"validate_exit": rc, "audit_problems": probs[:4]}
    return rc, probs


rc, probs = forge("flag-dropped", F + "Task_T", lambda r: r.update(coinductive_as_inductive=False))
check(rc == 2 and any("coinductive_as_inductive" in p for p in probs), "Task_T translated without the rule-T flag: audit-rejected")
rc, probs = forge("flag-on-inductive", F + "fin2", lambda r: r.update(coinductive_as_inductive=True))
check(rc == 2 and any("coinductive_as_inductive" in p for p in probs), "the rule-T flag on an inductive: audit-rejected")

src = {d["name"]: d for d in map(json.loads, open(RUN / "source.ndjson")) if d.get("kind") in ("constant", "inductive")}
u = {}
try:
    A.check_coinductive(src[F + "stream"], {"coinductive_as_inductive": True})
    u["stream_rejected"] = False
except A.Mismatch:
    u["stream_rejected"] = True
try:
    A.check_coinductive(src[F + "Task_T"], {"coinductive_as_inductive": True})
    u["task_accepted"] = True
except A.Mismatch:
    u["task_accepted"] = False
OUT["unit"] = u
check(all(u.values()), f"audit's rule-T criterion: {u}")

# 4. correspondence proofs
lean = RUN / "lean"
proof = ROOT / "tests" / "statement" / "proofs" / "coinductive_correspondence.lean"
(lean / "CoinductiveCorrespondence.lean").write_text(proof.read_text())
env = dict(os.environ, PATH=f"{Path.home()}/.elan/bin:" + os.environ["PATH"])
lp = subprocess.run(["lake", "-d", str(ROOT), "env", "printenv", "LEAN_PATH"], capture_output=True, text=True, env=env).stdout.strip()
env["LEAN_PATH"] = f"{lp}:{lean}"
q = subprocess.run(["lean", "CoinductiveCorrespondence.lean"], cwd=lean, capture_output=True, text=True, env=env)
outq = q.stdout + q.stderr
n_ax = outq.count("does not depend on any axioms")
OUT["correspondence"] = {"exit": q.returncode, "theorems_without_axioms": n_ax, "output": outq[:2000]}
check(q.returncode == 0 and n_ax == 4 and "sorry" not in outq and "depends on axioms" not in outq,
      f"correspondence T1/T2 (record isomorphism, η, ι): {n_ax} theorems, no axioms")

(ROOT / "reports" / "statement_only" / "test_coinductive.json").write_text(json.dumps(OUT, indent=1) + "\n")
finish("test-coinductive")

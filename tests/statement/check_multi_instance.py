#!/usr/bin/env python3
"""P3 (ITERATION_LOG entry 8): a proof prerequisite needed at several universe instances in one
declaration, through the real CLI on fixtures/stmt/p3 (P3.v). The proof is a tiny synthetic test proof
(tests/statement/proofs/p3_odat_obligation.lean).

1. use2 uses opaque data odat at two instances (nat's level and B's): its pending artifact has one
   hypothesis per instance of odat's obligation (never one hypothesis reused at a different type);
   use2_id inherits both; the run validates (consumer, audit).
2. Negative control: the two hypotheses forged to the same type (a duplicate) are kernel-accepted
   and audit-rejected.
3. Assembly with the generic synthetic proof: use2 and use2_id are assembled (each instance of the
   obligation discharged by the one final theorem at its own instance).

Writes reports/statement_only/test_multi_instance.json.
"""
import copy
import json
import shutil
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from lib import ROOT, check, cli, finish, forge_run, results  # noqa: E402

OUT = {}
P = ROOT / "tests" / "statement" / "proofs"
RUN = ROOT / "runs" / "st-p3"
OBL = "SF.P3.odat__rocq2lean_obligation_1"

shutil.rmtree(RUN, ignore_errors=True)
rcs = [cli("export", "--mode", "statement", "--manifest", ROOT / "fixtures/stmt/p3/manifest.json",
           "--roots", "SF.P3.use2_id", "--out", RUN)[0]]
rcs.append(cli("translate", "--input", RUN / "source.ndjson", "--out", RUN)[0])
rcs.append(cli("validate", "--run", RUN)[0])
rcs.append(cli("tasks", "--run", RUN)[0])
v = json.loads((RUN / "validate.json").read_text())
R, rep = results(RUN)
OUT["pipeline"] = {"exit_codes": rcs, "validation": v.get("status"), "reason": v.get("reason"),
                   "rows": {n: {k: r.get(k) for k in ("status", "level_params", "pending_hypotheses")} for n, r in R.items() if n.startswith("SF.")}}
check(rcs == [0, 0, 0, 0] and v.get("status") == "STATEMENT_VALIDATED", "fixture: export/translate/validate/tasks")
u2 = R["SF.P3.use2"]
check(u2["status"] == "PENDING_KERNEL_CHECKED" and u2["pending_hypotheses"] == [OBL, OBL],
      "use2: one hypothesis per instance of odat's obligation")
hyp_t, t = [], u2["target_type"]
for _ in u2["pending_hypotheses"]:
    hyp_t.append(t["t"])
    t = t["b"]
check(hyp_t[0] != hyp_t[1] and all(x.get("n") == f"Rocq.{OBL}.statement" for x in hyp_t),
      "the two hypotheses are the obligation's statement at two different universe instances")
check(R["SF.P3.use2_id"]["status"] == "STATEMENT_PENDING_KERNEL_CHECKED" and R["SF.P3.use2_id"]["pending_hypotheses"] == [OBL, OBL],
      "use2_id inherits both instances")

# 2. negative control: both hypotheses at the same type
rep2 = copy.deepcopy(rep)
r = next(x for x in rep2["results"] if x["source"] == "SF.P3.use2")
for k in ("target_type", "target_value"):
    r[k]["b"]["t"] = copy.deepcopy(r[k]["t"])
_, kernel_ok, rc, cons, aud = forge_run(RUN, "same-type-hypotheses", rep2, check_cmd="validate")
probs = [p["message"][:300] for p in aud.get("problems", []) if p["message"].startswith("SF.P3.use2")]
probs += [f"consumer {d}" for d, x in (cons.get("detectors") or {}).items() if x != "OK"]
OUT["negative_same_type"] = {"kernel": kernel_ok, "validate_exit": rc, "problems": probs[:4]}
check(rc == 2 and probs, "two hypotheses of one prerequisite at the same type: rejected")

# 3. assembly
T = {t["source"]["kernel_name"]: t for t in map(json.loads, open(RUN / "PROOF_TASKS.jsonl"))}
f = RUN / "submissions" / f"{T[OBL]['task_id']}.lean"
f.parent.mkdir(exist_ok=True)
f.write_text((P / "p3_odat_obligation.lean").read_text().replace("@TASK@", T[OBL]["task_id"]))
rc, out = cli("check-proof", "--run", RUN, "--task", T[OBL]["task_id"], "--file", f)
res = json.loads((RUN / "proofs" / T[OBL]["task_id"] / "result.json").read_text())
check(rc == 0 and res["status"] == "LEAN_PROOF_KERNEL_VERIFIED", "check-proof accepts the synthetic (generic) obligation proof")
rc, out = cli("assemble", "--run", RUN)
ds = sorted((RUN / "assembly").glob("*/assembly.json"), key=lambda p: p.stat().st_mtime_ns)
asm = json.loads(ds[-1].read_text()) if ds else None
A = {x["source"]: x for x in json.loads((Path(asm["assembly_dir"]) / "assembly_report.json").read_text())["results"]} if asm else {}
OUT["assembly"] = {"exit": rc, "status": asm and asm["status"],
                   "rows": {n: {k: x.get(k) for k in ("status", "target", "assembly", "proof_state")} for n, x in A.items() if n.startswith("SF.")}}
check(rc == 0 and asm and asm["status"] == "ASSEMBLY_VALIDATED", "assembly: ASSEMBLY_VALIDATED")
check(A["SF.P3.use2"]["assembly"] == "ASSEMBLED" and A["SF.P3.use2_id"]["assembly"] == "ASSEMBLED",
      "use2 and use2_id assembled: the one final theorem discharges both instances")

(ROOT / "reports" / "statement_only" / "test_multi_instance.json").write_text(json.dumps(OUT, indent=1) + "\n")
finish("test-multi-instance")

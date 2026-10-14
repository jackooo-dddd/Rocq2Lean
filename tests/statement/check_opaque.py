#!/usr/bin/env python3
"""A′ (docs/OPAQUE_DATA.md): opaque data translated with its body, through the real CLI, on the
synthetic fixture fixtures/stmt/opq (Opq.v). The proof is a tiny synthetic test proof
(tests/statement/proofs/opq_bounded_obligation.lean), never Prosa/Classic/MathComp.

1. Pipeline: export --mode statement (round trip included), translate, validate, tasks. Each opaque
   data constant is exported with its prepared body (`opaque_data`) and translated as a Lean `opaque`
   constant under its own name; its proof subterms are obligations (proof tasks); no opaque-value task
   remains; dependents reference the constant, not a hypothesis.
2. Opacity: the Lean constant does not unfold (`pick = 3` is not provable by `rfl`), as Rocq never
   unfolds Qed.
3. Negative controls, kernel-accepted and audit-rejected: a different value for the opaque body; the
   opaque data emitted as a transparent `def` (it would expose an unfolding the source hides).
4. Assembly with the synthetic obligation proof: `bounded` and `bval` are assembled as Rocq.* (the
   opaque constant itself, kind opaque); `nat_eqP` (no proofs supplied) and `eq_dec_nat` stay pending.

Writes reports/statement_only/test_opaque.json.
"""
import copy
import json
import os
import shutil
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from lib import ROOT, check, cli, finish, forge_run, results  # noqa: E402

OUT = {}
P = ROOT / "tests" / "statement" / "proofs"
RUN = ROOT / "runs" / "st-opq"
ROOTS = ["SF.Opq.pick_succ_pos", "SF.Opq.bval_le", "SF.Opq.eq_dec_nat", "SF.Opq.eqb_refl"]
OBL = "SF.Opq.bounded__rocq2lean_obligation_1"


def tasks():
    return {t["source"]["kernel_name"]: t for t in map(json.loads, open(RUN / "PROOF_TASKS.jsonl"))}


def lean_env(*dirs):
    lp = subprocess.run(["lake", "-d", str(ROOT), "env", "printenv", "LEAN_PATH"], capture_output=True, text=True,
                        env=dict(os.environ, PATH=f"{Path.home()}/.elan/bin:" + os.environ["PATH"])).stdout.strip()
    return {"LEAN_PATH": ":".join([lp, *map(str, dirs)]), "PATH": "/usr/bin:/bin"}


def probe(lean_dir, imp, name, body, *extra):
    f = Path(lean_dir) / f"Probe_{name}.lean"
    f.write_text(f"import {imp}\n" + body)
    p = subprocess.run([str(Path.home() / ".elan/bin/lean"), str(f)], capture_output=True, text=True, cwd=lean_dir,
                       env=lean_env(lean_dir, *extra), timeout=600)
    return p.returncode, (p.stdout + p.stderr).strip()[:600]


# 1. pipeline
shutil.rmtree(RUN, ignore_errors=True)
rcs = [cli("export", "--mode", "statement", "--manifest", ROOT / "fixtures/stmt/opq/manifest.json",
           "--roots", ",".join(ROOTS), "--out", RUN)[0]]
rcs.append(cli("translate", "--input", RUN / "source.ndjson", "--out", RUN)[0])
rcs.append(cli("validate", "--run", RUN)[0])
rcs.append(cli("tasks", "--run", RUN)[0])
v = json.loads((RUN / "validate.json").read_text())
rt = json.loads((RUN / "roundtrip.json").read_text())
R, rep = results(RUN)
src = {d["name"]: d for d in map(json.loads, open(RUN / "source.ndjson")) if d.get("kind") == "constant"}
OUT["pipeline"] = {"exit_codes": rcs, "validation": v.get("status"), "by_validation": v.get("by_validation"),
                   "roundtrip": rt.get("status"),
                   "rows": {n: {k: r.get(k) for k in ("status", "target", "target_kind", "pending_hypotheses")}
                            for n, r in sorted(R.items()) if n.startswith("SF.")}}
check(rcs == [0, 0, 0, 0] and v.get("status") == "STATEMENT_VALIDATED" and rt.get("status") == "OK",
      "fixture: export (round trip OK) / translate / validate / tasks")
check(all(src[n]["body_state"] == "opaque_data" and src[n]["body"] is not None and src[n]["native"]["body_kind"] == "opaque"
          for n in ("SF.Opq.pick", "SF.Opq.bounded", "SF.Opq.nat_eqP")),
      "the opaque data bodies are exported (opaque_data, native opacity kept), proof subterms extracted")
check(src["SF.Opq.bounded"]["obligations"] == [OBL] and len(src["SF.Opq.nat_eqP"]["obligations"]) == 5,
      "bounded has 1 extracted obligation, nat_eqP 5 (proof subterms under binders)")
check(R["SF.Opq.pick"]["status"] == "TRANSLATED_AND_CHECKED" and R["SF.Opq.pick"]["target"] == "Rocq.SF.Opq.pick"
      and R["SF.Opq.pick"]["target_kind"] == "opaque", "pick: an accepted opaque constant under its own name")
check(R["SF.Opq.pick_succ"]["status"] == "TRANSLATED_AND_CHECKED" and R["SF.Opq.pick_succ_pos"]["status"] == "STATEMENT_KERNEL_CHECKED",
      "its dependents are accepted (no opaque-value hypothesis)")
check(R["SF.Opq.bounded"]["status"] == "PENDING_KERNEL_CHECKED" and R["SF.Opq.bounded"]["pending_hypotheses"] == [OBL]
      and R["SF.Opq.bounded"]["target_kind"] == "opaque"
      and R["SF.Opq.bval"]["pending_hypotheses"] == [OBL] and R["SF.Opq.bval_le"]["pending_hypotheses"] == [OBL],
      "bounded is pending on its obligation (a proof), and so are bval and bval_le")
check(R["SF.Opq.nat_eqP"]["target_kind"] == "opaque" and R["SF.Opq.eq_dec_nat"]["status"] == "PENDING_KERNEL_CHECKED",
      "nat_eqP (reflect-valued, by induction) is an opaque constant; eq_dec_nat computes with it, pending on its obligations")
T = tasks()
OUT["tasks"] = {n: t["kind"] for n, t in sorted(T.items())}
check(not [t for t in T.values() if t["kind"] == "opaque_value"] and T[OBL]["kind"] == "obligation",
      "no opaque-value task; the body's proof subterms are ordinary obligation tasks")

# 2. opacity: the Lean constant does not unfold
rc, out = probe(RUN / "lean", "Rocq2LeanOut", "opaque_rfl", "example : Rocq.SF.Opq.pick = 3 := rfl\n")
rc2, out2 = probe(RUN / "lean", "Rocq2LeanOut", "opaque_kernel", "example : Rocq.SF.Opq.pick = 3 := by decide +kernel\n")
OUT["opacity"] = {"rfl": [rc, out[:300]], "kernel_decide": [rc2, out2[:300]]}
check(rc != 0 and rc2 != 0, "opacity kept: pick = 3 holds neither by rfl nor by kernel reduction (as Rocq never unfolds Qed)")


# 3. negative controls
def mutate(label, fn):
    rep2 = copy.deepcopy(rep)
    row = next(x for x in rep2["results"] if x["source"] == "SF.Opq.pick")
    fn(row)
    _, kernel_ok, rc, cons, aud = forge_run(RUN, label, rep2, check_cmd="validate")
    probs = [p["message"][:300] for p in aud.get("problems", []) if p["message"].startswith("SF.Opq.pick:")]
    OUT.setdefault("negative", {})[label] = {"kernel": kernel_ok, "validate_exit": rc, "audit_problems": probs[:3]}
    return kernel_ok, rc, probs


k, rc, probs = mutate("opaque-value-changed", lambda r: r.update(
    target_value={"k": "app", "f": {"k": "const", "n": "Nat.succ", "u": []}, "a": r["target_value"]}))
check(k and rc == 2 and probs, "a different opaque value (4 for 3): kernel-accepted, rejected by the structural audit")
k, rc, probs = mutate("opaque-as-def", lambda r: r.update(target_kind="def"))
check(k and rc == 2 and any("emitted as def" in p for p in probs),
      "opaque data emitted as a transparent def: kernel-accepted, rejected by the audit (opacity)")

# 4. assembly with the synthetic obligation proof
f = RUN / "submissions" / f"{T[OBL]['task_id']}.lean"
f.parent.mkdir(exist_ok=True)
f.write_text((P / "opq_bounded_obligation.lean").read_text().replace("@TASK@", T[OBL]["task_id"]))
rc, out = cli("check-proof", "--run", RUN, "--task", T[OBL]["task_id"], "--file", f)
res = json.loads((RUN / "proofs" / T[OBL]["task_id"] / "result.json").read_text())
check(rc == 0 and res["status"] == "LEAN_PROOF_KERNEL_VERIFIED", "check-proof accepts the synthetic obligation proof")
rc, out = cli("assemble", "--run", RUN)
ds = sorted((RUN / "assembly").glob("*/assembly.json"), key=lambda p: p.stat().st_mtime_ns)
asm = json.loads(ds[-1].read_text()) if ds else None
A = {r["source"]: r for r in json.loads((Path(asm["assembly_dir"]) / "assembly_report.json").read_text())["results"]} if asm else {}
OUT["assembly"] = {"exit": rc, "status": asm and asm["status"], "summary": asm and asm["summary"],
                   "rows": {n: {k: r.get(k) for k in ("status", "target", "target_kind", "assembly", "proof_state")}
                            for n, r in sorted(A.items()) if n.startswith("SF.")}}
check(rc == 0 and asm and asm["status"] == "ASSEMBLY_VALIDATED", "assembly: ASSEMBLY_VALIDATED (consumer and audit)")
check(A["SF.Opq.bounded"]["assembly"] == "ASSEMBLED" and A["SF.Opq.bounded"]["target"] == "Rocq.SF.Opq.bounded"
      and A["SF.Opq.bounded"]["target_kind"] == "opaque" and A["SF.Opq.bval"]["assembly"] == "ASSEMBLED",
      "bounded is assembled as the opaque constant Rocq.SF.Opq.bounded; bval as Rocq.SF.Opq.bval")
check(A["SF.Opq.nat_eqP"]["assembly"] == "PENDING" and A["SF.Opq.eq_dec_nat"]["assembly"] == "PENDING",
      "nat_eqP and eq_dec_nat (obligations not proved) stay pending")
rc, out = probe(Path(asm["assembly_dir"]) / "lean", "Rocq2LeanAssembled", "assembled_opaque",
                "open Lean in\n#eval show MetaM Unit from do\n  let ci ← getConstInfo `Rocq.SF.Opq.bounded\n"
                "  unless ci matches .opaqueInfo _ do throwError \"not opaque\"\n", RUN / "lean", Path(asm["assembly_dir"]) / "templates")
check(rc == 0, "the assembled Rocq.SF.Opq.bounded is an opaque constant in the assembled library")

(ROOT / "reports" / "statement_only").mkdir(parents=True, exist_ok=True)
(ROOT / "reports" / "statement_only" / "test_opaque.json").write_text(json.dumps(OUT, indent=1) + "\n")
finish("test-opaque")

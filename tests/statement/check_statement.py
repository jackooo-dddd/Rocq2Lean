#!/usr/bin/env python3
"""Statement-only pipeline tests (docs/STATEMENT_ONLY_DESIGN.md), through the real CLI.

1. Pipelines: `export --mode statement`, `translate`, `validate` on the FinishTime roots (Prosa) and on
   the statement fixture (fixtures/stmt/a): STATEMENT_VALIDATED, every claimed row audited.
2. Mode separation: `verify` refuses a statement run.
3. Negative controls (statement mutations): type-correct mutations of translated statements (a
   dropped hypothesis, swapped hypotheses, swapped arguments, a negated conclusion, a universal
   quantifier made existential) are accepted by Lean's kernel (replay) and rejected by validation
   through the structural audit.
4. Negative control (irrelevant proof change): fixtures/stmt/b has the same statements and
   definitions as fixtures/stmt/a with different proofs (also of the proof inside a definition); the
   statement closure, the exported declaration records and every generated proposition and
   definition are byte-identical.
5. Determinism: translating the same export twice gives identical targets and statuses.

Writes reports/statement_only/test_statement.json.
"""
import copy
import json
import shutil
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from lib import ROOT, check, cli, finish, forge_run, results  # noqa: E402

OUT = {}
FT_ROOTS = ["prosa.analysis.definitions.finish_time." + n for n in
            ("finish_time", "finished_at_finish_time", "earliest_finish_time", "response_time", "completes_at_finish_time")]
FX_ROOTS = ["SF.Stmt." + n for n in ("double", "double_succ", "double_even", "half_sig", "zero_of", "zero_of_le", "le_trans_alt")]


def pipeline(name, man, roots, validate=True):
    run = ROOT / "runs" / name
    shutil.rmtree(run, ignore_errors=True)
    rcs = [cli("export", "--mode", "statement", "--manifest", man, "--roots", ",".join(roots), "--out", run)[0]]
    rcs.append(cli("translate", "--input", run / "source.ndjson", "--out", run)[0] if rcs[0] == 0 else None)
    if validate:
        rcs.append(cli("validate", "--run", run)[0] if rcs[1] == 0 else None)
    v = json.loads((run / "validate.json").read_text()) if (run / "validate.json").exists() else {}
    OUT.setdefault("pipelines", {})[name] = {"exit_codes": rcs, "validation": v.get("status"),
                                             "by_validation": v.get("by_validation"), "roots": v.get("roots")}
    return run, rcs, v


# ---------- Lean expression JSON helpers (mutations) ----------

def bvars(e, depth=0, acc=None):
    acc = set() if acc is None else acc
    if isinstance(e, dict):
        if e.get("k") == "bvar" and e["i"] >= depth:
            acc.add(e["i"] - depth)
        for k, v in e.items():
            if k == "b" and e.get("k") in ("forall", "lam", "let"):
                bvars(v, depth + 1, acc)
            elif isinstance(v, (dict, list)):
                bvars(v, depth, acc)
    elif isinstance(e, list):
        for v in e:
            bvars(v, depth, acc)
    return acc


def shift(e, d, cut=0):
    """Add d to every bvar >= cut (free at this level)."""
    if isinstance(e, list):
        return [shift(v, d, cut) for v in e]
    if not isinstance(e, dict):
        return e
    if e.get("k") == "bvar":
        return dict(e, i=e["i"] + d) if e["i"] >= cut else e
    return {k: (shift(v, d, cut + 1) if k == "b" and e.get("k") in ("forall", "lam", "let") else shift(v, d, cut))
            for k, v in e.items()}


def swap01(e, depth=0):
    """Exchange bvar depth and depth+1 (the two innermost enclosing binders at the top)."""
    if isinstance(e, list):
        return [swap01(v, depth) for v in e]
    if not isinstance(e, dict):
        return e
    if e.get("k") == "bvar" and e["i"] in (depth, depth + 1):
        return dict(e, i=depth + 1 if e["i"] == depth else depth)
    return {k: (swap01(v, depth + 1) if k == "b" and e.get("k") in ("forall", "lam", "let") else swap01(v, depth))
            for k, v in e.items()}


def peel(e, n):
    for _ in range(n):
        e = e["b"]
    return e


def foralls(e):
    """The chain of top-level foralls: [(node, depth)]."""
    out, d = [], 0
    while e.get("k") == "forall":
        out.append((e, d))
        e, d = e["b"], d + 1
    return out, e


def mut_drop_hyp(stmt):
    """∀ (h : H), C with C independent of h  ↦  C (the hypothesis removed: a stronger statement)."""
    fs, _ = foralls(stmt)
    for node, _ in reversed(fs):
        if 0 not in bvars(node["b"]):
            new = shift(node["b"], -1, 1)
            node.clear()
            node.update(new)
            return True
    return False


def mut_swap_hyps(stmt):
    """∀ (a : A) (b : B), C with B independent of a, A ≠ B  ↦  ∀ (b : B) (a : A), C."""
    fs, _ = foralls(stmt)
    for node, _ in fs:
        inner = node["b"]
        if inner.get("k") != "forall" or 0 in bvars(inner["t"]):
            continue
        A, B = node["t"], shift(inner["t"], -1, 0)
        if A == B:
            continue
        new = {"k": "forall", "n": inner["n"], "t": B,
               "b": {"k": "forall", "n": node["n"], "t": shift(A, 1, 0), "b": swap01(inner["b"])}}
        node.clear()
        node.update(new)
        return True
    return False


def mut_swap_args(stmt):
    """f … x … y … ↦ f … y … x … for two distinct bound variables of the same closed binder type."""
    types = []

    def go(e, ctx):
        if isinstance(e, dict):
            if e.get("k") == "app":
                spine, h = [], e
                while h.get("k") == "app":
                    spine.append(h)
                    h = h["f"]
                args = [x["a"] for x in spine]
                for i in range(len(args)):
                    for j in range(i + 1, len(args)):
                        a, b = args[i], args[j]
                        if a.get("k") == b.get("k") == "bvar" and a["i"] != b["i"] and a["i"] < len(ctx) and b["i"] < len(ctx):
                            ta, tb = ctx[len(ctx) - 1 - a["i"]], ctx[len(ctx) - 1 - b["i"]]
                            if ta == tb and not bvars(ta):
                                spine[i]["a"], spine[j]["a"] = b, a
                                return True
            for k, v in e.items():
                if k == "b" and e.get("k") in ("forall", "lam"):
                    if go(v, ctx + [e["t"]]):
                        return True
                elif isinstance(v, (dict, list)) and go(v, ctx):
                    return True
        elif isinstance(e, list):
            return any(go(v, ctx) for v in e)
        return False
    return go(stmt, types)


def mut_negate(stmt):
    """The conclusion C ↦ C → False."""
    fs, concl = foralls(stmt)
    node = fs[-1][0]["b"] if fs else stmt
    new = {"k": "forall", "n": "h", "t": copy.deepcopy(node), "b": {"k": "const", "n": "False", "u": []}}
    node.clear()
    node.update(new)
    return True


def mut_exists(stmt, level):
    """The innermost ∀ (x : A), B (B a proposition) ↦ ∃ x : A, B (Exists.{level})."""
    fs, _ = foralls(stmt)
    if not fs:
        return False
    node = fs[-1][0]
    new = {"k": "app", "f": {"k": "app", "f": {"k": "const", "n": "Exists", "u": [level]}, "a": node["t"]},
           "a": {"k": "lam", "n": node["n"], "t": node["t"], "b": node["b"]}}
    node.clear()
    node.update(new)
    return True


def mutate(run, decl, label, fn):
    R, rep = results(run)
    rep = copy.deepcopy(rep)
    row = next(x for x in rep["results"] if x["source"] == decl)
    k = len(row.get("pending_hypotheses") or [])
    stmt = peel(row["target_value"], k)
    if not fn(stmt):
        OUT.setdefault("mutations", []).append({"mutation": label, "declaration": decl, "applicable": False})
        return None
    _, kernel_ok, rc, cons, aud = forge_run(run, label, rep, check_cmd="validate")
    struct = [p for p in aud.get("problems", []) if p["message"].startswith(f"{decl}:")]
    rec = {"mutation": label, "declaration": decl, "applicable": True, "kernel": "ACCEPTED" if kernel_ok else "REJECTED",
           "validate_exit": rc, "detectors": sorted({p["detector"] for p in struct}),
           "consumer": cons.get("status")}
    OUT.setdefault("mutations", []).append(rec)
    return rec


# 1. pipelines
ft, rcs, v = pipeline("st-finishtime", ROOT / "fixtures" / "m6" / "manifest.json", FT_ROOTS)
check(rcs == [0, 0, 0] and v.get("status") == "STATEMENT_VALIDATED", f"FinishTime statement pipeline validated ({rcs})")
check(all(r["validation"] in ("DEFINITION_AUDITED_PENDING", "STATEMENT_AUDITED_PENDING", "DEFINITION_AUDITED", "STATEMENT_AUDITED")
          for r in v.get("roots", [])), "every FinishTime root is translated and audited (possibly pending)")
# A′: eqnP, iffP and idP are opaque data translated with their bodies (opaque constants), so the roots
# wait for proof tasks only -- their bodies' obligations, the lemmas idP's body uses and finish_time's
# obligation -- plus the value of find_ex_minn, whose body recurses on a proof (guard deferred) and
# keeps the interface (local hypotheses are never extracted as obligations)
FT_PRE = {"Corelib.ssr.ssrbool.is_true_true", "Corelib.ssr.ssrbool.not_false_is_true",
          "mathcomp.boot.ssrnat.eqnP__rocq2lean_obligation_1", "mathcomp.boot.ssrnat.eqnP__rocq2lean_obligation_2",
          "Corelib.ssr.ssrbool.iffP__rocq2lean_obligation_1", "Corelib.ssr.ssrbool.iffP__rocq2lean_obligation_2",
          "prosa.analysis.definitions.finish_time.finish_time__rocq2lean_obligation_1", "mathcomp.boot.ssrnat.find_ex_minn"}
check(all(set(r["pending_prerequisites"]) == FT_PRE for r in v.get("roots", [])),
      "FinishTime roots wait exactly for proof tasks (eqnP's, iffP's and finish_time's obligations, two lemmas) "
      "and the value of opaque find_ex_minn (kept as an interface: its body recurses on a proof)")
fsrc = {d["name"]: d for d in map(json.loads, open(ft / "source.ndjson")) if d.get("kind") == "constant"}
check(fsrc["mathcomp.boot.ssrnat.eqnP"]["body_state"] == "opaque_data"
      and fsrc["mathcomp.boot.ssrnat.find_ex_minn"]["body_state"] == "opaque_interface"
      and fsrc["mathcomp.boot.ssrnat.find_ex_minn"].get("opaque_body_refused", "").startswith("termination deferred"),
      "A′: eqnP's body is exported; find_ex_minn's is refused (termination deferred), with the reason")
fa, rcs, v = pipeline("st-fixture-a", ROOT / "fixtures" / "stmt" / "a" / "manifest.json", FX_ROOTS)
check(rcs == [0, 0, 0] and v.get("status") == "STATEMENT_VALIDATED", f"fixture A statement pipeline validated ({rcs})")
RA, _ = results(fa)
check(RA["SF.Stmt.double_succ"]["status"] == "STATEMENT_KERNEL_CHECKED" and RA["SF.Stmt.double_succ"]["target"] == "Rocq.SF.Stmt.double_succ.statement",
      "a lemma is translated as its statement only (Rocq.<name>.statement : Prop)")
check(RA["SF.Stmt.half_sig"]["status"] == "PENDING_KERNEL_CHECKED"
      and RA["SF.Stmt.half_sig"]["pending_hypotheses"] == ["SF.Stmt.half_sig__rocq2lean_obligation_1"],
      "the proof inside half_sig is an extracted obligation; half_sig is pending on it")
src = {d["name"]: d for d in map(json.loads, open(fa / "source.ndjson")) if d.get("kind") in ("constant", "inductive")}
check(all(src[n]["body"] is None for n in src if src[n].get("body_state") in ("statement_only", "obligation")),
      "no proof body is exported for a statement or an obligation")

# 2. mode separation
rc, out = cli("verify", "--run", fa)
check(rc == 2 and "validate" in out, "verify refuses a statement-mode run")

# 3. statement mutations (kernel-accepted, audit-rejected)
for decl, label, fn in [
        ("prosa.analysis.definitions.finish_time.finished_at_finish_time", "swap-hyps", mut_swap_hyps),
        ("prosa.analysis.definitions.finish_time.completes_at_finish_time", "negate", mut_negate)]:
    rec = mutate(ft, decl, label, fn)
    check(rec is not None and rec["kernel"] == "ACCEPTED" and rec["validate_exit"] == 2 and "structure" in rec["detectors"],
          f"statement mutation {label} on {decl.rsplit('.', 1)[1]}: kernel-accepted, rejected by the structural audit")
for decl, label, fn in [
        ("SF.Stmt.double_succ", "fx-negate", mut_negate),
        ("SF.Stmt.le_trans_alt", "fx-drop-hyp", mut_drop_hyp),
        ("SF.Stmt.le_trans_alt", "fx-swap-args", mut_swap_args),
        ("SF.Stmt.double_even", "fx-exists", lambda s: mut_exists(s, {"k": "succ", "l": {"k": "zero"}}))]:
    rec = mutate(fa, decl, label, fn)
    check(rec is not None and rec["kernel"] == "ACCEPTED" and rec["validate_exit"] == 2 and "structure" in rec["detectors"],
          f"statement mutation {label} on {decl}: kernel-accepted, rejected by the structural audit")

# 4. irrelevant proof change
fb, rcs, v = pipeline("st-fixture-b", ROOT / "fixtures" / "stmt" / "b" / "manifest.json", FX_ROOTS)
check(rcs == [0, 0, 0] and v.get("status") == "STATEMENT_VALIDATED", f"fixture B (other proofs) validated ({rcs})")
ca, cb = (json.loads((r / "contract.json").read_text()) for r in (fa, fb))
check(ca["required_closure"] == cb["required_closure"] and ca["exported"] == cb["exported"],
      "statement closure unchanged by the proof change")
la = {json.loads(l)["name"]: l for l in open(fa / "source.ndjson") if '"kind":"constant"' in l[:20] or '"kind":"inductive"' in l[:20]}
lb = {json.loads(l)["name"]: l for l in open(fb / "source.ndjson") if '"kind":"constant"' in l[:20] or '"kind":"inductive"' in l[:20]}
diff = sorted(n for n in set(la) | set(lb) if la.get(n) != lb.get(n))
check(not diff, f"exported declaration records byte-identical ({len(la)} records; differing: {diff})")
RB, _ = results(fb)
tdiff = sorted(n for n in set(RA) | set(RB)
               if {k: RA.get(n, {}).get(k) for k in ("status", "target", "target_type", "target_value", "target_ctors", "pending_hypotheses")}
               != {k: RB.get(n, {}).get(k) for k in ("status", "target", "target_type", "target_value", "target_ctors", "pending_hypotheses")})
check(not tdiff, f"generated propositions and definitions byte-identical (differing: {tdiff})")
OUT["irrelevant_proof_change"] = {"records": len(la), "differing_records": diff, "differing_targets": tdiff}

# 5. determinism (translate the same export again)
d2 = ROOT / "runs" / "st-fixture-a-again"
shutil.rmtree(d2, ignore_errors=True)
rc, _ = cli("translate", "--input", fa / "source.ndjson", "--out", d2)
R2, _ = results(d2)
same = all({k: RA[n].get(k) for k in ("status", "target", "target_type", "target_value", "pending_hypotheses")}
           == {k: R2[n].get(k) for k in ("status", "target", "target_type", "target_value", "pending_hypotheses")} for n in RA)
check(rc == 0 and same and set(RA) == set(R2), "translation is deterministic (same export, same targets)")

# 6. proof tasks (stated, never proved here) and the proof checker (negative submissions only)
rc, out = cli("tasks", "--run", fa)
tasks = [json.loads(l) for l in open(fa / "PROOF_TASKS.jsonl")] if (fa / "PROOF_TASKS.jsonl").exists() else []
leaf_rows = [n for n, r in RA.items() if r["status"] in ("STATEMENT_KERNEL_CHECKED", "STATEMENT_PENDING_KERNEL_CHECKED")]
check(rc == 0 and sorted(t["source"]["kernel_name"] for t in tasks) == sorted(leaf_rows),
      f"one proof task per proof-task statement ({len(tasks)})")
ids = [t["task_id"] for t in tasks]
rc2, _ = cli("tasks", "--run", fa)
check(rc2 == 0 and [json.loads(l)["task_id"] for l in open(fa / "PROOF_TASKS.jsonl")] == ids, "task ids are stable")
kinds = {t["source"]["kernel_name"]: t["kind"] for t in tasks}
check(kinds.get("SF.Stmt.half_sig__rocq2lean_obligation_1") == "obligation" and kinds.get("SF.Stmt.double_succ") == "theorem_statement",
      "task kinds: theorem statements and extracted obligations")
check(all(t["status"] == "PROOF_PENDING" and t["lean"]["reserved_name"] == f"RocqProofTemplates.T{t['task_id']}.proof"
          and t["lean"]["final_name"] == "Rocq." + t["source"]["kernel_name"] for t in tasks),
      "every task is PROOF_PENDING with its template name (Rocq.<name> reserved for assembly)")
t0 = next(t for t in tasks if t["source"]["kernel_name"] == "SF.Stmt.double_succ")
OUT["tasks_fixture"] = {"count": len(tasks), "example": t0}
TN = t0["lean"]["reserved_name"]
negs = {
    "sorry": f"import Rocq2LeanOut\ntheorem {TN} : Rocq.SF.Stmt.double_succ.statement := sorry\n",
    "wrong-statement": f"import Rocq2LeanOut\ntheorem {TN} : True := trivial\n",
    "custom-axiom": f"import Rocq2LeanOut\naxiom cheat : Rocq.SF.Stmt.double_succ.statement\n"
                    f"theorem {TN} : Rocq.SF.Stmt.double_succ.statement := cheat\n",
    "declared-axiom": f"import Rocq2LeanOut\naxiom {TN} : Rocq.SF.Stmt.double_succ.statement\n",
    "missing": "import Rocq2LeanOut\ntheorem other : True := trivial\n",
    "not-compiling": f"import Rocq2LeanOut\ntheorem {TN} : Rocq.SF.Stmt.double_succ.statement := by exact 0\n",
}
OUT["check_proof_negatives"] = {}
for label, text in negs.items():
    f = fa / f"neg-{label}.lean"
    f.write_text(text)
    rc, out = cli("check-proof", "--run", fa, "--task", t0["task_id"], "--file", f)
    res = json.loads((fa / "proofs" / t0["task_id"] / "result.json").read_text())
    OUT["check_proof_negatives"][label] = {"exit": rc, "status": res.get("status"), "problems": res.get("problems")}
    check(rc == 2 and res.get("status") == "PROOF_REJECTED", f"check-proof rejects a submission: {label}")

(ROOT / "reports" / "statement_only").mkdir(parents=True, exist_ok=True)
(ROOT / "reports" / "statement_only" / "test_statement.json").write_text(json.dumps(OUT, indent=1) + "\n")
finish("test-statement")

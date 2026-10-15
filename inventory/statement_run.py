"""Corpus-scale statement-only run (measurement): merge the statement-mode chunk exports of both
families (`INVENTORY_EXPORT_MODE=statement inventory/export.py`) into one IR, translate it with the
unchanged `rocq2lean translate`, and summarize.

The merged IR keeps every distinct declaration once (all copies of a kernel name must be
byte-identical: the statement preparation does not depend on the request), in dependency order; the
universe lines are the union of the chunks' (each declaration's closure lies in the chunk that
exported it). A contract is built for the merged IR (tools/contract.py, with the pinned protection
binding), so the translation runs under interface protection, and the fresh-process consumer and the
independent audit check every claimed row (`check`). What the corpus run does not have, unlike a CLI
run, is a per-run source snapshot and round trip: the chunk exports were made by the inventory driver
(their statement preparation is re-derived by the CLI round trip on the tested runs, not here).

    python3 -I inventory/statement_run.py merge|translate|check|summary
"""
import hashlib
import json
import os
import subprocess
import sys
from collections import Counter, defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
W = ROOT / ".work" / "inventory"
# (STATEMENT_EXPORT: the chunk directories' prefix, default export-statement; see inventory/export.py
# INVENTORY_EXPORT_TAG)
EXPORT = os.environ.get("STATEMENT_EXPORT", "export-statement")
RUN = Path(os.environ["STATEMENT_RUN"]).resolve() if os.environ.get("STATEMENT_RUN") else ROOT / "runs" / "st-corpus"
OUT = ROOT / "reports" / "statement_only"


def merge():
    store, digest, inconsistent = {}, {}, {}
    terms, header, libs, levels, cons, flevels, rels = {}, None, {}, {}, {}, {}, {}
    roots_req = []
    mode = Counter()
    refused = {}
    for fam in ("modern", "classic"):
        for rp in sorted((W / f"{EXPORT}-{fam}").glob("chunk-*/result.json")):
            r = json.loads(rp.read_text())
            for x in r["irs"]:
                with open(ROOT / x["ir"]) as fh:
                    for k, line in enumerate(fh):
                        if k < 5:
                            o = json.loads(line)
                            if o["kind"] == "header":
                                header = header or o
                                m = o.get("mode") or {}
                                refused.update((m.get("extraction_refused") or {}) if isinstance(m, dict) else {})
                            elif o["kind"] == "roots":
                                for e in o["roots"]:
                                    terms.setdefault(e["name"], e["term"])
                                    roots_req.append((e["requested"], e["name"]))
                            elif o["kind"] == "libraries":
                                for l in o["libraries"]:
                                    libs[l["dirpath"]] = l
                            elif o["kind"] == "universes":
                                for l in o["levels"]:
                                    levels[json.dumps(l, sort_keys=True)] = l
                                for c in o["constraints"]:
                                    cons[json.dumps(c, sort_keys=True)] = c
                            elif o["kind"] == "universe_facts":
                                for l in o["levels"]:
                                    flevels[l] = None
                                for rr in o["relations"]:
                                    rels[json.dumps(rr, sort_keys=True)] = rr
                            continue
                        if not (line.startswith('{"kind":"constant"') or line.startswith('{"kind":"inductive"')):
                            continue
                        i = line.index('"name":"') + 8
                        n = line[i:line.index('"', i)]
                        h = hashlib.sha256(line.encode()).hexdigest()
                        if n not in digest:
                            digest[n] = h
                            store[n] = line if line.endswith("\n") else line + "\n"
                        elif digest[n] != h:
                            inconsistent.setdefault(n, [digest[n]])
                            if h not in inconsistent[n]:
                                inconsistent[n].append(h)
    # protected roots present (requested directly or covered by another chunk's closure)
    prot = json.loads((ROOT / "reports/prosa_inventory/protected_interface.json").read_text())["protected"]
    rl = []
    for n in prot:
        if n not in store:
            continue
        d = json.loads(store[n])
        t = terms.get(n)
        if t is None:
            if d["universes"]["k"] != "monomorphic":
                continue
            t = {"k": "const", "c": n, "u": []} if d["kind"] == "constant" else {"k": "ind", "ind": {"mind": n, "i": 0}, "u": []}
        rl.append({"requested": n.replace("/", "."), "name": n, "term": t})
    deps = {n: sorted(set((json.loads(l)["deps"].get("type", [])) + (json.loads(l)["deps"].get("body", [])))) for n, l in store.items()}
    order, seen = [], set()
    for r in sorted(store):
        st = [(r, False)]
        while st:
            n, done = st.pop()
            if done:
                order.append(n)
                continue
            if n in seen or n not in store:
                continue
            seen.add(n)
            st.append((n, True))
            st += [(m, False) for m in reversed(deps[n]) if m not in seen]
    RUN.mkdir(parents=True, exist_ok=True)
    hdr = dict(header, mode={"name": "statement", "merged_from_chunks": True, "extraction_refused": dict(sorted(refused.items()))})
    with open(RUN / "source.ndjson", "w") as fh:
        j = lambda o: json.dumps(o, separators=(",", ":")) + "\n"
        fh.write(j(hdr))
        fh.write(j({"kind": "roots", "roots": rl}))
        fh.write(j({"kind": "libraries", "libraries": [libs[k] for k in sorted(libs)]}))
        fh.write(j({"kind": "universes", "levels": [levels[k] for k in sorted(levels)], "constraints": [cons[k] for k in sorted(cons)]}))
        fh.write(j({"kind": "universe_facts", "levels": sorted(flevels), "relations": [rels[k] for k in sorted(rels)],
                    "source": "union of the statement-mode chunk exports' native facts"}))
        for n in order:
            fh.write(store[n])
        fh.write(j({"kind": "footer", "declarations": len(order)}))
    (RUN / "merge.json").write_text(json.dumps({"declarations": len(order), "roots": len(rl), "inconsistent_copies": inconsistent,
                                                "extraction_refused": refused}, indent=1) + "\n")
    print(f"merged {len(order)} declarations, {len(rl)} roots, {len(inconsistent)} inconsistent copies, {len(refused)} extraction refusals")


def translate():
    sys.path.insert(0, str(ROOT / "tools"))
    import contract
    import protection
    con = contract.build(str(RUN / "source.ndjson"), [r["requested"] for r in json.loads(open(RUN / "source.ndjson").readlines()[1])["roots"]])
    con["protection"] = protection.binding(con["exported"])
    (RUN / "contract.json").write_text(json.dumps(con, indent=1) + "\n")
    p = subprocess.run([sys.executable, "-I", str(ROOT / "tools" / "rocq2lean.py"), "translate",
                        "--input", str(RUN / "source.ndjson"), "--out", str(RUN)], capture_output=True, text=True)
    (RUN / "translate.out").write_text(p.stdout + p.stderr)
    print("translate exit", p.returncode)


def check():
    """Fresh-process consumer and independent audit of every claimed row (as `validate` runs them)."""
    lean = RUN / "lean"
    (lean / "Rocq2LeanConsumer.lean").write_text(
        f'import Rocq2LeanOut\nimport Rocq2Lean.Verify\n#rocq2lean_verify "{RUN / "contract.json"}" '
        f'"{RUN / "translation_report.json"}" "{RUN / "consumer_result.json"}"\n')
    env = dict(os.environ, PATH=f"{Path.home()}/.elan/bin:" + os.environ["PATH"])
    lp = subprocess.run(["lake", "-d", str(ROOT), "env", "printenv", "LEAN_PATH"], capture_output=True, text=True, env=env).stdout.strip()
    env["LEAN_PATH"] = f"{lp}:{lean}"
    sys.path.insert(0, str(ROOT / "tools"))
    import rocq2lean as R0
    p = subprocess.run(["lean", *R0.native_args(), "Rocq2LeanConsumer.lean"], cwd=lean, capture_output=True, text=True, env=env)
    (RUN / "consumer.out").write_text(p.stdout + p.stderr)
    p2 = subprocess.run([sys.executable, "-I", str(ROOT / "tools" / "audit.py"), str(RUN / "source.ndjson"), str(RUN / "contract.json"),
                         str(RUN / "translation_report.json"), str(RUN / "audit.json"), str(RUN / "consumer_result.json")],
                        capture_output=True, text=True)
    (RUN / "audit.out").write_text(p2.stdout + p2.stderr)
    c = json.loads((RUN / "consumer_result.json").read_text()) if (RUN / "consumer_result.json").exists() else {}
    a = json.loads((RUN / "audit.json").read_text()) if (RUN / "audit.json").exists() else {}
    print("consumer", p.returncode, c.get("status"), {k: v for k, v in (c.get("detectors") or {}).items() if v != "OK"})
    print("audit", p2.returncode, a.get("status"), a.get("coverage"))


def instances():
    """CLI parity (tools/rocq2lean.py `_validate_finish`): every accepted row with an R2B-P level is
    re-checked by Rocq's kernel at its instance (`Rocq2Lean CheckInstance`), in the common source
    environment (all modules of both families, as the union universe check); a pending row with an
    R2B-P level is not validated (the translator refuses it). Writes RUN/source_instances.json."""
    sys.path.insert(0, str(ROOT / "tools"))
    sys.path.insert(0, str(ROOT / "inventory"))
    import rocq2lean as R
    import statement_provenance as P
    rep = json.loads((RUN / "translation_report.json").read_text())
    rows = [r for r in rep["results"] if r.get("status") in ("TRANSLATED_AND_CHECKED", "STATEMENT_KERNEL_CHECKED") and r.get("r2bp_levels")]
    pend = [r["source"] for r in rep["results"] if r.get("status") in ("PENDING_KERNEL_CHECKED", "STATEMENT_PENDING_KERNEL_CHECKED")
            and r.get("r2bp_levels")]
    levels = json.loads(open(RUN / "source.ndjson").readlines()[4])["levels"]
    back = {"u_" + l.replace(".", "_"): l for l in levels}
    cmds, problems = [], []
    for r in rows:
        subst = []
        for x in r["r2bp_levels"]:
            sg = x["sigma"]
            if sg == {"k": "zero"}:
                subst.append(f"{x['level']}=Set")
            elif sg.get("k") == "param" and sg["n"] in back:
                subst.append(f"{x['level']}={back[sg['n']]}")
            else:
                problems.append(f"{r['source']}: solution {sg} of {x['level']} denotes no Rocq level")
        cmds.append(f'Rocq2Lean CheckInstance "{r["source"]}" "{";".join(subst)}".')
    got = {}
    if cmds:
        allreq = sorted({m for _, d, _, x in P.chunks() for m in P.requires(d, x)})
        lp = json.loads((P.W / f"{P.EXPORT}-classic" / "chunk-0000" / "result.json").read_text())["exporter"]["load_paths"]
        v = RUN / "SourceInstances.v"
        v.write_text("\n".join(["From Rocq2LeanExport Require Import Loader."] + [f"Require {m}." for m in allreq] + cmds) + "\n")
        p = subprocess.run(["rocq", "compile", "-I", str(R.EXPORTER / "src"), "-Q", str(R.EXPORTER / "theories"), "Rocq2LeanExport",
                            *lp, str(v)], capture_output=True, text=True, env=R.opam_env())
        (RUN / "source_instances.log").write_text(p.stdout + p.stderr)
        for line in (p.stdout + p.stderr).splitlines():
            if line.startswith("INSTANCE "):
                _, key, res = line.split(" ", 2)
                got[key] = res
    bad = [f"{r['source']}: {got.get(r['source'], 'not checked')}" for r in rows if got.get(r["source"]) != "INSTANCE_OK"]
    res = {"schema": "rocq2lean-source-instances/1", "checked": {r["source"]: got.get(r["source"]) for r in rows},
           "pending_with_r2bp": pend, "problems": problems + bad,
           "status": "OK" if not (problems or bad or pend) else "REJECTED"}
    (RUN / "source_instances.json").write_text(json.dumps(res, indent=1) + "\n")
    print("source instances", res["status"], len(rows), "checked;", "pending R2B-P:", pend, (problems + bad)[:5])


def summary():
    """reports/statement_only/TRANSLATION_RESULTS.json: outcomes by family and for the protected
    interface, audited (consumer + audit) where they ran; failure mechanisms; prerequisites ranked by
    how many pending declarations need them."""
    rep = json.loads((RUN / "translation_report.json").read_text())
    audit = json.loads((RUN / "audit.json").read_text()) if (RUN / "audit.json").exists() else {}
    cons = json.loads((RUN / "consumer_result.json").read_text()) if (RUN / "consumer_result.json").exists() else {}
    verdict = {v["source"]: v["verdict"] for v in audit.get("verdicts", [])}
    decls = {}
    for l in open(ROOT / "reports/prosa_inventory/declarations.jsonl"):
        d = json.loads(l)
        decls[d["name"]] = d
    ir = {}
    with open(RUN / "source.ndjson") as fh:
        for line in fh:
            d = json.loads(line)
            if d.get("kind") in ("constant", "inductive"):
                ir[d["name"]] = {"body_state": d.get("body_state"), "kind": d["kind"]}
    fam = lambda n: decls.get(n, {}).get("family", "external")
    lib = lambda n: fam(n) if fam(n) != "external" else n.split(".")[0]
    res = rep["results"]
    leaf = lambda n: ir.get(n, {}).get("body_state") in ("statement_only", "obligation", "opaque_interface")

    def outcome(r):
        st = r["status"]
        v = verdict.get(r["source"])
        if st in ("TRANSLATED_AND_CHECKED", "BOOTSTRAP_RESOLVED", "STATEMENT_KERNEL_CHECKED"):
            base = "STATEMENT" if leaf(r["source"]) else "DEFINITION"
            return f"{base}_AUDITED" if v == "MATCH" else f"{base}_KERNEL_CHECKED_AUDIT_{v}"
        if st in ("PENDING_KERNEL_CHECKED", "STATEMENT_PENDING_KERNEL_CHECKED"):
            base = "STATEMENT" if leaf(r["source"]) else "DEFINITION"
            return f"{base}_AUDITED_PENDING" if v == "MATCH" else f"{base}_PENDING_AUDIT_{v}"
        return st
    by = defaultdict(Counter)
    for r in res:
        by[lib(r["source"])][outcome(r)] += 1
    prot = set(json.loads((ROOT / "reports/prosa_inventory/protected_interface.json").read_text())["protected"])
    pby = defaultdict(Counter)
    for r in res:
        if r["source"] in prot:
            pby[fam(r["source"])][outcome(r)] += 1
    missing_prot = sorted(prot - {r["source"] for r in res})
    ok = ("TRANSLATED_AND_CHECKED", "BOOTSTRAP_RESOLVED", "STATEMENT_KERNEL_CHECKED", "STATEMENT_PENDING_KERNEL_CHECKED",
          "PENDING_KERNEL_CHECKED", "BLOCKED_DEPENDENCY", "OBLIGATIONS_PENDING")
    direct = [r for r in res if r["status"] not in ok]
    mech = Counter((r["status"], (r.get("message") or "").split("[")[0].split(":")[0][:90]) for r in direct)
    # prerequisites ranked by the pending declarations (assembly) needing them
    need = defaultdict(set)
    for r in res:
        for h in r.get("pending_hypotheses") or []:
            need[h].add(r["source"])
    # blocked declarations: transitive count of what each direct failure blocks
    rdeps = defaultdict(set)
    for r in res:
        for b in r.get("blocked_by") or []:
            rdeps[b].add(r["source"])
    def blocked_by_failure(n):
        seen, st = set(), [n]
        while st:
            x = st.pop()
            for y in rdeps.get(x, ()):
                if y not in seen:
                    seen.add(y)
                    st.append(y)
        return seen
    fails = []
    for r in direct:
        b = blocked_by_failure(r["source"])
        fails.append({"declaration": r["source"], "family": fam(r["source"]), "status": r["status"],
                      "message": (r.get("message") or "")[:400],
                      "blocks": len(b), "blocks_protected": sum(1 for x in b if x in prot)})
    fails.sort(key=lambda x: (-x["blocks_protected"], -x["blocks"], x["declaration"]))
    out = {"schema": "rocq2lean-statement-results/1", "run": str(RUN.relative_to(ROOT)), "report_status": rep.get("status"),
           "checks": {"consumer": cons.get("status"), "consumer_failed_detectors": {k: v for k, v in (cons.get("detectors") or {}).items() if v != "OK"},
                      "audit": audit.get("status"), "audit_problems": len(audit.get("problems", [])),
                      "audit_problem_examples": audit.get("problems", [])[:20],
                      "note": "no per-run source snapshot/round trip for the merged corpus IR (see inventory/statement_run.py)"},
           "declarations": len(res), "by_library": {k: dict(v) for k, v in sorted(by.items())},
           "protected_interface": {"total": len(prot), "absent_from_export": len(missing_prot),
                                   "by_family": {k: dict(v) for k, v in sorted(pby.items())}},
           "failure_mechanisms": [{"status": s_, "message": m, "count": c} for (s_, m), c in mech.most_common()],
           "direct_failures": fails,
           "prerequisites_by_need": [{"prerequisite": h, "kind": ir.get(h, {}).get("body_state"), "family": fam(h),
                                      "pending_declarations_needing_it": len(xs),
                                      "protected_needing_it": sum(1 for x in xs if x in prot)}
                                     for h, xs in sorted(need.items(), key=lambda kv: (-len(kv[1]), kv[0]))[:100]]}
    OUT.mkdir(parents=True, exist_ok=True)
    (OUT / "TRANSLATION_RESULTS.json").write_text(json.dumps(out, indent=1) + "\n")
    print(json.dumps({k: out[k] for k in ("declarations", "checks", "protected_interface")}, indent=1)[:3000])
    for m in out["failure_mechanisms"][:30]:
        print(m)
    for f in fails[:15]:
        print(f["declaration"], f["status"], f["blocks"], f["blocks_protected"], f["message"][:150])
    for x in out["prerequisites_by_need"][:15]:
        print(x)


def tasks():
    """reports/statement_only/PROOF_TASKS.jsonl: the proof tasks of the corpus run (rocq2lean's task
    builder), with the corpus consumer and audit as evidence (both must be OK)."""
    sys.path.insert(0, str(ROOT / "tools"))
    import rocq2lean
    c = json.loads((RUN / "consumer_result.json").read_text())
    a = json.loads((RUN / "audit.json").read_text())
    if c.get("status") != "OK" or a.get("status") != "OK":
        sys.exit("corpus consumer/audit not OK: no tasks")
    sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
    ev = {"run": str(RUN.relative_to(ROOT)), "consumer_sha256": sha(RUN / "consumer_result.json"),
          "audit_sha256": sha(RUN / "audit.json"), "report_sha256": sha(RUN / "translation_report.json"),
          "ir_sha256": sha(RUN / "source.ndjson")}
    recs = rocq2lean.build_tasks(RUN, ev, OUT / "PROOF_TASKS.jsonl")
    print(len(recs))


def subset(roots, out):
    """Debugging aid: the closure of `roots` cut out of the merged corpus IR (all universe lines
    kept), as a translate-only input."""
    lines = open(RUN / "source.ndjson").readlines()
    recs = {}
    for l in lines[5:-1]:
        d = json.loads(l)
        recs[d["name"]] = (l, sorted(set(d["deps"].get("type", [])) | set(d["deps"].get("body", []))))
    keep, st = set(), list(roots)
    while st:
        n = st.pop()
        if n in keep or n not in recs:
            continue
        keep.add(n)
        st += recs[n][1]
    rl = [r for r in json.loads(lines[1])["roots"] if r["name"] in roots]
    out = Path(out)
    out.parent.mkdir(parents=True, exist_ok=True)
    with open(out, "w") as fh:
        fh.write(lines[0])
        fh.write(json.dumps({"kind": "roots", "roots": rl}, separators=(",", ":")) + "\n")
        fh.writelines(lines[2:5])
        n = 0
        for l in lines[5:-1]:
            if json.loads(l)["name"] in keep:
                fh.write(l)
                n += 1
        fh.write(json.dumps({"kind": "footer", "declarations": n}, separators=(",", ":")) + "\n")
    print(f"{n} declarations for {len(rl)} roots -> {out}")


def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def assemble_dry():
    """Assembly of the corpus with *no* submitted proofs (docs/ASSEMBLY.md): every validated row must
    be reproduced identically against the imported library (no REUSE_MISMATCH), every pending row
    carried over, and the assembly consumer and audit must pass. Evidence that assembly is a no-op on
    the corpus until proofs exist; it adds no coverage."""
    sys.path.insert(0, str(ROOT / "tools"))
    import rocq2lean as R
    A = RUN / "assembly-dry"
    A.mkdir(parents=True, exist_ok=True)
    (A / "lean").mkdir(exist_ok=True)
    proofs = A / "proofs.json"
    proofs.write_text(json.dumps({"schema": "rocq2lean-assembly-proofs/1", "allowed_axioms": R.DEFAULT_ALLOWED_AXIOMS,
                                  "proofs": []}, indent=1) + "\n")
    src, con, rep, out = RUN / "source.ndjson", RUN / "contract.json", RUN / "translation_report.json", A / "assembly_report.json"
    mod = A / "lean" / "Rocq2LeanAssembled.lean"
    mod.write_text(f'import Rocq2Lean\nimport Rocq2LeanOut\n#rocq2lean_assemble "{src}" "{sha(src)}" "{con}" "{sha(con)}" '
                   f'"{rep}" "{sha(rep)}" "{proofs}" "{sha(proofs)}" "{out}"\n')
    lp = subprocess.run(["lake", "-d", str(ROOT), "env", "printenv", "LEAN_PATH"], capture_output=True, text=True,
                        env=R.lean_env()).stdout.strip()
    env = dict(R.lean_env(), LEAN_PATH=":".join([lp, str(RUN / "lean"), str(A / "lean")]))
    p = subprocess.run([f"{R.HOME}/.elan/bin/lean", f"--root={A / 'lean'}", mod.name, "-o", "Rocq2LeanAssembled.olean"],
                       cwd=A / "lean", env=env, capture_output=True, text=True)
    (A / "assemble.out").write_text(p.stdout + p.stderr)
    print("assemble exit", p.returncode)
    cres = A / "consumer_result.json"
    (A / "lean" / "Consumer.lean").write_text(f'import Rocq2LeanAssembled\nimport Rocq2Lean.Verify\n'
                                              f'#rocq2lean_verify "{con}" "{out}" "{cres}" "{proofs}"\n')
    p2 = subprocess.run([f"{R.HOME}/.elan/bin/lean", *R.native_args(), "Consumer.lean"], cwd=A / "lean", env=env, capture_output=True, text=True)
    (A / "consumer.out").write_text(p2.stdout + p2.stderr)
    p3 = subprocess.run([sys.executable, "-I", str(ROOT / "tools" / "audit.py"), str(src), str(con), str(out),
                         str(A / "audit.json"), str(cres), "--assembly", str(proofs), "--validated", str(rep)],
                        capture_output=True, text=True)
    (A / "audit.out").write_text(p3.stdout + p3.stderr)
    r = json.loads(out.read_text()) if out.exists() else {}
    c = json.loads(cres.read_text()) if cres.exists() else {}
    a = json.loads((A / "audit.json").read_text()) if (A / "audit.json").exists() else {}
    res = {"assemble_exit": p.returncode, "assembly_status": r.get("status"), "summary": r.get("assembly"),
           "consumer": c.get("status"), "consumer_failed": [d for d, v in (c.get("detectors") or {}).items() if v != "OK"],
           "audit": a.get("status"), "audit_problems": len(a.get("problems", []))}
    (A / "result.json").write_text(json.dumps(res, indent=1) + "\n")
    print(json.dumps(res, indent=1))


if __name__ == "__main__":
    if sys.argv[1] == "subset":
        subset(sys.argv[2].split(","), sys.argv[3])
        sys.exit(0)
    {"merge": merge, "translate": translate, "check": check, "summary": summary, "tasks": tasks,
     "assemble-dry": assemble_dry, "instances": instances}[sys.argv[1]]()

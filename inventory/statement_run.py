"""Corpus-scale statement-only run (measurement): merge the statement-mode chunk exports of both
families (`INVENTORY_EXPORT_MODE=statement inventory/export.py`) into one IR, translate it with the
unchanged `rocq2lean translate`, and summarize.

The merged IR keeps every distinct declaration once (all copies of a kernel name must be
byte-identical: the statement preparation does not depend on the request), in dependency order; the
universe lines are the union of the chunks' (each declaration's closure lies in the chunk that
exported it). This is a translate-only measurement (no contract, so no protection binding and no
validation verdict); validated runs go through the full CLI (`export --mode statement`, `translate`,
`validate`).

    python3 -I inventory/statement_run.py merge|translate|summary
"""
import hashlib
import json
import subprocess
import sys
from collections import Counter, defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
W = ROOT / ".work" / "inventory"
RUN = ROOT / "runs" / "st-corpus"
OUT = ROOT / "reports" / "statement_only"


def merge():
    store, digest, inconsistent = {}, {}, {}
    terms, header, libs, levels, cons, flevels, rels = {}, None, {}, {}, {}, {}, {}
    roots_req = []
    mode = Counter()
    refused = {}
    for fam in ("modern", "classic"):
        for rp in sorted((W / f"export-statement-{fam}").glob("chunk-*/result.json")):
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
    p = subprocess.run([sys.executable, "-I", str(ROOT / "tools" / "rocq2lean.py"), "translate",
                        "--input", str(RUN / "source.ndjson"), "--out", str(RUN)], capture_output=True, text=True)
    (RUN / "translate.out").write_text(p.stdout + p.stderr)
    print("translate exit", p.returncode)


def summary():
    rep = json.loads((RUN / "translation_report.json").read_text())
    decls = {}
    for l in open(ROOT / "reports/prosa_inventory/declarations.jsonl"):
        d = json.loads(l)
        decls[d["name"]] = d
    fam = lambda n: decls.get(n, {}).get("family", "external")
    res = rep["results"]
    by = defaultdict(Counter)
    for r in res:
        by[fam(r["source"])][r["status"]] += 1
    prot = set(json.loads((ROOT / "reports/prosa_inventory/protected_interface.json").read_text())["protected"])
    pby = defaultdict(Counter)
    for r in res:
        if r["source"] in prot:
            pby[fam(r["source"])][r["status"]] += 1
    direct = [r for r in res if r["status"] not in ("TRANSLATED_AND_CHECKED", "BOOTSTRAP_RESOLVED", "STATEMENT_KERNEL_CHECKED",
                                                     "STATEMENT_PENDING_KERNEL_CHECKED", "PENDING_KERNEL_CHECKED",
                                                     "BLOCKED_DEPENDENCY", "OBLIGATIONS_PENDING")]
    mech = Counter((r["status"], (r.get("message") or "").split("[")[0][:110]) for r in direct)
    hyps = Counter(h for r in res for h in r.get("pending_hypotheses") or [])
    out = {"schema": "rocq2lean-statement-results/1", "run": str(RUN.relative_to(ROOT)), "report_status": rep.get("status"),
           "declarations": len(res), "by_family": {k: dict(v) for k, v in by.items()},
           "protected_by_family": {k: dict(v) for k, v in pby.items()},
           "direct_failures": [{"declaration": r["source"], "family": fam(r["source"]), "status": r["status"],
                                "message": (r.get("message") or "")[:400]} for r in direct],
           "failure_mechanisms": [{"status": s, "message": m, "count": c} for (s, m), c in mech.most_common()],
           "most_needed_prerequisites": [{"leaf": h, "pending_declarations_using_it": c} for h, c in hyps.most_common(40)]}
    OUT.mkdir(parents=True, exist_ok=True)
    (OUT / "TRANSLATION_RESULTS.json").write_text(json.dumps(out, indent=1) + "\n")
    print(json.dumps({k: out[k] for k in ("declarations", "by_family", "protected_by_family")}, indent=1))
    for m in out["failure_mechanisms"][:25]:
        print(m)
    print(out["most_needed_prerequisites"][:15])


if __name__ == "__main__":
    {"merge": merge, "translate": translate, "summary": summary}[sys.argv[1]]()

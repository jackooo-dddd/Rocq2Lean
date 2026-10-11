"""Bounded diagnostic translation probes (no promotion, no verification).

`probe.py build <fam>` writes runs/inv-probe-<fam>/source.ndjson: the closure of every in-scope root of
the family with no known blocker, assembled from the census store. Declarations are in dependency
order; the universe lines are the union of those of the chunk exports (each declaration's whole
closure lies in the export that produced it, so the pairwise native facts it needs are present).
`probe.py translate <fam>` runs the unchanged `rocq2lean translate` on it (translate-only: no
contract, no round trip, no verify) in a systemd scope with a memory limit.

`probe.py confirm <fam>` re-runs every declaration that failed directly in the probe as its own root
through the full CLI (export with its round trip, then translate) in runs/inv-confirm-<n>. Only these
confirmation runs are translation evidence (inventory/coverage.py, inventory/evidence_blockers.py);
the probe itself only selects what to confirm.

    python3 -I inventory/probe.py build|translate|confirm modern|classic
"""
import hashlib
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
# run-directory tag (environment INVENTORY_PROBE_TAG, e.g. "-p0"): probes and confirmations of a later
# implementation get their own directories, so earlier ones stay as historical records
import os
TAG = os.environ.get("INVENTORY_PROBE_TAG", "")
W = ROOT / ".work" / "inventory"
OUT = ROOT / "reports" / "prosa_inventory"
sys.path.insert(0, str(ROOT / "tools"))
OK = ("TRANSLATED_AND_CHECKED", "BOOTSTRAP_RESOLVED", "BLOCKED_DEPENDENCY")


def jl(p):
    return [json.loads(l) for l in open(p)]


def build(fam):
    cov = {r["id"]: r for r in jl(OUT / "coverage.jsonl")}
    dec = {r["id"]: r for r in jl(OUT / "declarations.jsonl")}
    roots = sorted(i for i, r in cov.items() if r["family"] == fam and r["known_blocker"] == "NO_KNOWN_BLOCKER"
                   and dec[i]["role"] != "alias_reexport")
    store = {}
    for f in ("modern", "classic"):
        with open(W / f"ir-{f}.ndjson") as fh:
            for line in fh:
                i = line.index('"name":"') + 8
                store.setdefault(line[i:line.index('"', i)], line)
    deps = {}
    for n, line in store.items():
        d = json.loads(line)["deps"]
        deps[n] = sorted(set(d.get("type", []) + d.get("body", [])))
    order, seen = [], set()
    for r in roots:                                   # iterative post-order: dependencies first
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
    terms, header, libs, levels, cons, flevels, rels, src = {}, None, {}, {}, {}, {}, {}, None
    for rp in sorted(W.glob("export-*/chunk-*/result.json")):
        for x in json.loads(rp.read_text())["irs"]:
            with open(ROOT / x["ir"]) as fh:
                for k in range(5):
                    o = json.loads(fh.readline())
                    if o["kind"] == "header":
                        header = header or o
                    elif o["kind"] == "roots":
                        for e in o["roots"]:
                            terms.setdefault(e["name"], e["term"])
                    elif o["kind"] == "libraries":
                        for l in o["libraries"]:
                            libs[l["dirpath"]] = l
                    elif o["kind"] == "universes":
                        for l in o["levels"]:
                            levels[json.dumps(l, sort_keys=True)] = l
                        for c in o["constraints"]:
                            cons[json.dumps(c, sort_keys=True)] = c
                    elif o["kind"] == "universe_facts":
                        src = o["source"]
                        for l in o["levels"]:
                            flevels[l] = None
                        for r in o["relations"]:
                            rels[json.dumps(r, sort_keys=True)] = r
    rl = []
    for r in roots:
        d = json.loads(store[r])
        if r in terms:
            t = terms[r]
        elif d["universes"]["k"] == "monomorphic":
            t = {"k": "const", "c": r, "u": []} if d["kind"] == "constant" else {"k": "ind", "ind": {"mind": r, "i": 0}, "u": []}
        else:
            continue                                  # a polymorphic root needs its exported instance
        rl.append({"requested": dec[r]["requested"], "name": r, "term": t})
    run = ROOT / "runs" / f"inv-probe{TAG}-{fam}"
    run.mkdir(parents=True, exist_ok=True)
    with open(run / "source.ndjson", "w") as fh:
        fh.write(json.dumps(header, separators=(",", ":")) + "\n")
        fh.write(json.dumps({"kind": "roots", "roots": rl}, separators=(",", ":")) + "\n")
        fh.write(json.dumps({"kind": "libraries", "libraries": [libs[k] for k in sorted(libs)]}, separators=(",", ":")) + "\n")
        fh.write(json.dumps({"kind": "universes", "levels": [levels[k] for k in sorted(levels)],
                             "constraints": [cons[k] for k in sorted(cons)]}, separators=(",", ":")) + "\n")
        fh.write(json.dumps({"kind": "universe_facts", "levels": sorted(flevels), "relations": [rels[k] for k in sorted(rels)],
                             "source": f"union of the census chunk exports' facts ({src})"}, separators=(",", ":")) + "\n")
        for n in order:
            fh.write(store[n] if store[n].endswith("\n") else store[n] + "\n")
        fh.write(json.dumps({"kind": "footer", "declarations": len(order)}, separators=(",", ":")) + "\n")
    (run / "probe.json").write_text(json.dumps({"family": fam, "roots": len(rl), "roots_skipped_polymorphic": len(roots) - len(rl),
                                                "declarations": len(order), "kind": "diagnostic translate-only probe"}, indent=1) + "\n")
    print(f"{fam}: probe of {len(rl)} roots, closure {len(order)}")


def translate(fam):
    run = ROOT / "runs" / f"inv-probe{TAG}-{fam}"
    p = subprocess.run(["systemd-run", "--user", "--scope", "-q", "-p", "MemoryMax=24G", "-p", "MemorySwapMax=0",
                        sys.executable, "-I", str(ROOT / "tools" / "rocq2lean.py"), "translate",
                        "--input", str(run / "source.ndjson"), "--out", str(run)], capture_output=True, text=True)
    (run / "probe-translate.out").write_text(p.stdout + p.stderr)
    rep = json.loads((run / "translation_report.json").read_text())
    from collections import Counter
    print(fam, "exit", p.returncode, Counter(r["status"] for r in rep["results"]))
    fails = {r["source"]: (r["status"], (r.get("message") or "")[:300]) for r in rep["results"] if r["status"] not in OK}
    (run / "direct_failures.json").write_text(json.dumps(fails, indent=1, sort_keys=True) + "\n")
    for n, v in sorted(fails.items()):
        print(" ", n, v)


def confirm_one(n, status, exp):
    import rocq2lean
    # the library (file) of a kernel name: before the first "/" (module path) or the last "."
    lib = n.split("/")[0] if "/" in n else n.rsplit(".", 1)[0]
    d = ROOT / "runs" / f"inv-confirm{TAG}-{hashlib.sha256(n.encode()).hexdigest()[:12]}"
    man = d.with_suffix(".manifest.json")
    man.write_text(json.dumps({"name": f"inv-confirm {n}", "load_paths": [exp[i:i + 3] for i in range(0, len(exp), 3)],
                               "files": [], "requires": [lib]}, indent=1) + "\n")
    res = {"declaration": n, "probe_status": status, "run": d.name}
    try:
        rocq2lean.export(str(man), [n.replace("/", ".")], str(d))
        res["export"] = 0
        p = subprocess.run([sys.executable, "-I", str(ROOT / "tools" / "rocq2lean.py"), "translate",
                            "--input", str(d / "source.ndjson"), "--out", str(d)], capture_output=True, text=True)
        res["translate"] = p.returncode
        rep = json.loads((d / "translation_report.json").read_text())
        st = {r["source"]: r for r in rep["results"]}
        res["status"] = st.get(n, {}).get("status")
        res["message"] = (st.get(n, {}).get("message") or "")[:300]
        res["other_direct_failures"] = sorted(k for k, r in st.items() if k != n and r["status"] not in OK)
    except Exception as e:                       # Rejected or tool failure: recorded, never dropped
        res["export"] = f"{type(e).__name__}: {e.args}"[:400]
    return res


def confirm(fam, workers=3):
    """Confirm each new direct probe failure as its own root through the full CLI. Failures of
    declarations that a current run already translated are recorded as probe artifacts instead."""
    from concurrent.futures import ThreadPoolExecutor
    run = ROOT / "runs" / f"inv-probe{TAG}-{fam}"
    fails = json.loads((run / "direct_failures.json").read_text())
    translated = json.loads((W / "extra_blockers.json").read_text()).get("translated_in_current_runs", {})
    exp = json.loads((W / f"export-{fam}" / "summary.json").read_text())["exporter"]["load_paths"]
    out = run / "confirmations.jsonl"
    done = {r["declaration"] for r in map(json.loads, open(out)) if not str(r.get("export", 0)).startswith(("Rejected", "Exception"))} if out.exists() else set()
    todo = []
    for n in sorted(fails):
        if n in done:
            continue
        if n in translated:
            with open(out, "a") as fh:
                fh.write(json.dumps({"declaration": n, "probe_status": fails[n][0], "status": "PROBE_ARTIFACT",
                                     "translated_in": translated[n]}) + "\n")
        else:
            todo.append(n)
    with ThreadPoolExecutor(workers) as ex:
        for res in ex.map(lambda n: confirm_one(n, fails[n][0], exp), todo):
            print(json.dumps(res)[:400], flush=True)
            with open(out, "a") as fh:
                fh.write(json.dumps(res) + "\n")


if __name__ == "__main__":
    {"build": build, "translate": translate, "confirm": confirm}[sys.argv[1]](sys.argv[2])

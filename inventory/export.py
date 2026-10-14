"""Export every enumerated declaration of a family, in bounded chunks.

The pinned exporter (`Rocq2Lean Export`, the command behind `rocq2lean export`) writes elaborated
types and bodies, body states, universes, typing flags and type/body dependencies of each requested
root's whole closure. It quotes one closure per root, so memory grows with the number of roots (0.1 to
1 GB per root on Prosa); all 2,707 modern roots at once exceeded 40 GB.

Every enumerated entry must end up in the store, either as a requested root or inside the closure of
one (its record is the same: the exporter's declaration records do not depend on the request).
Modules are visited dependents-first (longest import chain first, later declarations of a file first)
and a root already present in an exported closure is not requested again. Chunks of at most CHUNK
roots run in systemd scopes with a hard memory limit; after a chunk needed splitting, the next chunks
use the largest part size that succeeded (doubling again after clean chunks). Which chunk exports a declaration depends on
scheduling; the merged store does not (inventory/merge.py sorts it and checks that all copies are
byte-identical).

The census does not use `rocq2lean export`'s independent round trip (minutes per chunk): nothing here is
translated or trusted for translation. The merged store is classified afterwards by the current
preflight classifier (inventory/graph.py, calling tools/preflight.py unchanged).

Failure handling, per chunk:
  * ROCQ2LEAN_UNQUOTABLE (sort-polymorphic dependency): the exporter names the blocked roots and their
    dependency paths; they are recorded and the chunk is re-run without them.
  * `Stack overflow` at the default 8 MB stack (the CLI's): the part is recorded in
    stack_overflow_default and re-run once with a 4 GB stack (census data; a resource limit of the CLI).
  * any other failure: the part is split in halves down to single roots; a single root killed at the
    memory limit is retried once with BIG_MEMORY; a single root that still fails is recorded as failed
    with the log tail.
Resumable: completed chunks (result.json with the same exporter digest) are reloaded, their roots and
closures count as done, and scheduling continues after them.

    python3 -I inventory/export.py modern|classic [workers]
"""
import hashlib
import json
import os
import resource
import subprocess
import sys
import time
from concurrent.futures import ProcessPoolExecutor
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CFG = json.loads((ROOT / "inventory" / "config.json").read_text())
W = ROOT / ".work" / "inventory"
X = lambda p: Path(os.path.expanduser(p)) if p.startswith("~") else ROOT / p
EXP = ROOT / "rocq" / "exporter"
CHUNK = int(os.environ.get("INVENTORY_EXPORT_CHUNK", "24"))
MEMORY_MAX = os.environ.get("INVENTORY_EXPORT_MEMORY", "12G")
BIG_MEMORY = "24G"
TIMEOUT = 1800
BIG_STACK = 4 << 30
sys.path.insert(0, str(ROOT / "tools"))


def sha(b):
    return hashlib.sha256(b).hexdigest()


# statement-only mode (docs/STATEMENT_ONLY_DESIGN.md): `Rocq2Lean ExportStatements` of the protected
# roots, in their own chunk directories (export-statement-<fam>)
MODE = os.environ.get("INVENTORY_EXPORT_MODE", "proof")
SUFFIX = ("" if MODE == "proof" else f"-{MODE}") + (f"-{os.environ['INVENTORY_EXPORT_TAG']}" if os.environ.get("INVENTORY_EXPORT_TAG") else "")
# (INVENTORY_EXPORT_TAG: a separate set of chunk directories, e.g. a re-export with a changed exporter
# next to the earlier one, whose evidence other manifests still bind)
COMMAND = {"proof": "Export", "statement": "ExportStatements"}[MODE]


def load_paths(fam):
    mw, cb = X(CFG["modern"]["working"]), X(CFG["classic"]["working"])
    lp = ["-R", str(mw), "prosa", "-R", str(ROOT / ".work" / "coqeal-ce3d1d6"), "CoqEAL"]
    if fam == "classic":
        lp += ["-R", str(cb / "classic"), "prosa.classic", "-Q", str(cb / "compat"), "Compat"]
    return lp


def module_order(fam):
    """Modules dependents-first: longest chain of in-family imports first, then by name."""
    sys.path.insert(0, str(ROOT / "inventory"))
    import graph
    g, _, _ = graph.rocq_dep(fam)
    mods = json.loads((W / "modules.json").read_text())["modules"]
    by_file = {v["file"]: m for m, v in mods.items() if v["family"] == fam}
    tree = X(CFG[fam]["working"])
    deps = {}
    for f, vos in g.items():
        if f in by_file:
            deps[by_file[f]] = [by_file[os.path.relpath(v, tree)[:-1]] for v in vos
                                if os.path.relpath(v, tree)[:-1] in by_file]
    depth = {}

    def dp(m, seen=()):
        if m not in depth:
            depth[m] = 1 + max((dp(x, seen + (m,)) for x in deps.get(m, []) if x not in seen), default=0)
        return depth[m]

    order = sorted(by_file.values(), key=lambda m: (-dp(m), m))
    return [(m, n.split("#")[0]) for m in order for n in [e[1] for e in reversed(mods[m]["entries"])]]


def norm(n):
    return n.replace("/", ".")


def big_stack():
    resource.setrlimit(resource.RLIMIT_STACK, (BIG_STACK, BIG_STACK))


def run_export(fam, d, items, env, tag, stack=None, memory=MEMORY_MAX):
    d.mkdir(parents=True, exist_ok=True)
    ir = d / f"source-{tag}.ndjson"
    for p in (ir, ir.with_name(ir.name + ".blockers.json")):
        if p.exists():
            p.unlink()
    reqs = sorted({m for m, _ in items})
    v = d / f"Export_{tag}.v"
    v.write_text("From Rocq2LeanExport Require Import Loader.\n" + "".join(f"Require {m}.\n" for m in reqs)
                 + f'Rocq2Lean {COMMAND} "{ir}" {" ".join(r for _, r in items)}.\n')
    cmd = ["systemd-run", "--user", "--scope", "-q", "-p", f"MemoryMax={memory}", "-p", "MemorySwapMax=0",
           "rocq", "compile", "-I", str(EXP / "src"), "-Q", str(EXP / "theories"), "Rocq2LeanExport",
           *load_paths(fam), str(v)]
    t = time.time()
    try:
        p = subprocess.run(cmd, capture_output=True, text=True, env=env, timeout=TIMEOUT, cwd=d, preexec_fn=stack)
        rc, log = p.returncode, (p.stdout + p.stderr)
    except subprocess.TimeoutExpired as e:
        rc, log = "timeout", f"timeout after {TIMEOUT}s"
    (d / f"export-{tag}.log").write_text(f"$ {'(stack ' + str(BIG_STACK) + ') ' if stack else ''}{' '.join(cmd)}\n{log}\n[exit {rc}, {time.time() - t:.1f}s]\n")
    blockers = ir.with_name(ir.name + ".blockers.json")
    if rc == 0 and ir.exists():
        return "ok", ir, None
    if blockers.exists():
        return "unquotable", None, json.loads(blockers.read_text())
    return "failed", None, {"exit": rc, "log_tail": log[-1500:],
                            "resource_limit": rc in (-9, 137, "timeout") or "Killed" in log or "Out of memory" in log}


def do_chunk(fam, i, items, env, exporter_digest):
    d = W / f"export{SUFFIX}-{fam}" / f"chunk-{i:04d}"
    res = {"exporter": exporter_digest, "chunk": i, "roots": [r for _, r in items], "modules": sorted({m for m, _ in items}),
           "irs": [], "unquotable": {}, "failed": {}, "stack_overflow_default": [], "big_memory": [], "memory_kills": 0}
    queue, n = [items], 0
    while queue:
        part = queue.pop(0)
        tag = f"{n:02d}"
        n += 1
        st, ir, info = run_export(fam, d, part, env, tag)
        stack = None
        if st == "failed" and "Stack overflow" in info["log_tail"]:
            # the default 8 MB stack of the CLI is a resource limit: record it, then census with a big stack
            res["stack_overflow_default"].append({"tag": tag, "roots": [r for _, r in part]})
            tag, n, stack = f"{n:02d}", n + 1, big_stack
            st, ir, info = run_export(fam, d, part, env, tag, stack=stack)
        if st == "failed" and len(part) == 1 and info["resource_limit"]:
            res["big_memory"].append({"tag": tag, "roots": [part[0][1]]})
            tag, n = f"{n:02d}", n + 1
            st, ir, info = run_export(fam, d, part, env, tag, stack=stack, memory=BIG_MEMORY)
        if st == "ok":
            names = []
            with open(ir) as fh:
                for line in fh:
                    if line.startswith('{"kind":"constant"') or line.startswith('{"kind":"inductive"'):
                        j = line.index('"name":"') + 8
                        names.append(line[j:line.index('"', j)])
            res["irs"].append({"tag": tag, "ir": str(ir.relative_to(ROOT)), "ir_sha256": sha(ir.read_bytes()),
                               "roots": [r for _, r in part], "declarations": names})
        elif st == "unquotable":
            blocked = {b["requested"]: b["path"] for b in info["roots"]}
            for r, pth in blocked.items():
                res["unquotable"][r] = {"reason": info["reason"], "path": pth}
            rest = [x for x in part if x[1] not in blocked]
            if rest and len(rest) < len(part):
                queue.append(rest)
            elif rest:
                for _, r in rest:
                    res["failed"][r] = {"exit": "unquotable-without-names", "log_tail": json.dumps(info)[-800:]}
        elif len(part) > 1:
            res["memory_kills"] += bool(info.get("resource_limit"))
            h = len(part) // 2
            queue += [part[:h], part[h:]]
        else:
            res["failed"][part[0][1]] = info
    (d / "result.json").write_text(json.dumps(res, indent=1, sort_keys=True) + "\n")
    return res


def main(fam, workers=2):
    import rocq2lean
    from concurrent.futures import FIRST_COMPLETED, wait
    env = rocq2lean.opam_env()
    base = W / f"export{SUFFIX}-{fam}"
    base.mkdir(parents=True, exist_ok=True)
    plugin = rocq2lean.build_exporter(base / "plugin-build.log")
    exporter_digest = {"plugin_sha256": sha(Path(plugin).read_bytes()), "load_paths": load_paths(fam), "mode": MODE}
    order = module_order(fam)
    if MODE == "statement":
        prot = {norm(n) for n in json.loads((ROOT / "reports/prosa_inventory/protected_interface.json").read_text())["protected"]}
        order = [(m, r) for m, r in order if norm(r) in prot]
    (base / "order.json").write_text(json.dumps(order) + "\n")
    covered, handled, results = set(), set(), []

    def absorb(r):
        results.append(r)
        handled.update(r["roots"])
        for x in r["irs"]:
            covered.update(norm(n) for n in x["declarations"])

    for rp in sorted(base.glob("chunk-*/result.json")):
        r = json.loads(rp.read_text())
        if r.get("exporter") == exporter_digest:
            absorb(r)
    nxt = max((r["chunk"] for r in results), default=-1) + 1
    t = time.time()
    pos = 0

    size = CHUNK

    def next_chunk():
        nonlocal pos
        items = []
        while pos < len(order) and len(items) < size:
            m, r = order[pos]
            pos += 1
            if r not in handled and norm(r) not in covered:
                items.append((m, r))
                handled.add(r)
        return items

    with ProcessPoolExecutor(workers) as ex:
        running = set()
        while True:
            while len(running) < workers:
                items = next_chunk()
                if not items:
                    break
                running.add(ex.submit(do_chunk, fam, nxt, items, env, exporter_digest))
                nxt += 1
            if not running:
                break
            done, running = wait(running, return_when=FIRST_COMPLETED)
            for f in done:
                r = f.result()
                absorb(r)
                # adaptive chunk size: after memory kills, the largest part that succeeded; else grow back
                ok = max((len(x["roots"]) for x in r["irs"]), default=1)
                size = max(2, ok) if r.get("memory_kills") else min(CHUNK, size * 2)
                left = sum(1 for _, x in order if x not in handled and norm(x) not in covered)
                print(f"{fam} chunk {r['chunk']}: {len(r['roots'])} roots, {len(r['irs'])} IR, {len(r['unquotable'])} unquotable, "
                      f"{len(r['failed'])} failed; covered {len(covered)}, roots left {left}  [{time.time() - t:.0f}s]", flush=True)
    roots = {r for _, r in order}
    summary = {"family": fam, "chunk_size": CHUNK, "memory_max": MEMORY_MAX, "big_memory": BIG_MEMORY, "timeout_s": TIMEOUT,
               "exporter": exporter_digest, "chunks": len(results), "roots": len(roots),
               "requested": sum(len(r["roots"]) for r in results),
               "covered_by_closures": sum(1 for x in roots if norm(x) in covered),
               "unquotable": sum(len(r["unquotable"]) for r in results),
               "failed": sum(len(r["failed"]) for r in results),
               # a requested root that is neither unquotable nor failed was exported (possibly under its
               # canonical kernel name: a module alias); inventory/merge.py maps every entry to its identity
               "not_reached": sorted(x for x in roots if norm(x) not in covered and not any(x in r["roots"] for r in results))}
    (base / "summary.json").write_text(json.dumps(summary, indent=1) + "\n")
    print(json.dumps(summary)[:2000])


if __name__ == "__main__":
    main(sys.argv[1], int(sys.argv[2]) if len(sys.argv) > 2 else 2)

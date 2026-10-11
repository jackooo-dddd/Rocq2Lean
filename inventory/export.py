"""Export every enumerated declaration of a family, in bounded chunks.

Every enumerated entry is a root. The pinned exporter (`Rocq2Lean Export`, the command behind
`rocq2lean export`) writes elaborated types and bodies, body states, universes, typing flags and
type/body dependencies of each root's whole closure. It quotes one closure per root, so memory grows
with the number of roots (about 0.1 GB per root measured on Prosa); roots are therefore exported in
chunks of at most CHUNK roots, each in a systemd scope with a hard memory limit.

The census does not use `rocq2lean export`'s independent round trip (minutes per chunk): nothing here is
translated or trusted for translation. The merged store is classified afterwards by the current
preflight classifier (inventory/graph.py, calling tools/preflight.py unchanged).

Failure handling, per chunk:
  * ROCQ2LEAN_UNQUOTABLE (sort-polymorphic dependency): the exporter names the blocked roots and their
    dependency paths; they are recorded and the chunk is re-run without them.
  * any other failure (resource limit, error): the chunk is split in halves down to single roots; a
    single root that still fails is recorded as EXPORT_FAILED with the log tail.
Resumable: a chunk whose result.json matches its roots and the exporter digest is not redone.

    python3 -I inventory/export.py modern|classic [workers]
"""
import hashlib
import json
import os
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
CHUNK = 50
MEMORY_MAX = "9G"
TIMEOUT = 1800
sys.path.insert(0, str(ROOT / "tools"))


def sha(b):
    return hashlib.sha256(b).hexdigest()


def load_paths(fam):
    mw, cb = X(CFG["modern"]["working"]), X(CFG["classic"]["working"])
    lp = ["-R", str(mw), "prosa", "-R", str(ROOT / ".work" / "coqeal-ce3d1d6"), "CoqEAL"]
    if fam == "classic":
        lp += ["-R", str(cb / "classic"), "prosa.classic", "-Q", str(cb / "compat"), "Compat"]
    return lp


def plan(fam):
    mods = json.loads((W / "modules.json").read_text())["modules"]
    chunks, cur = [], []
    for m in sorted(m for m, v in mods.items() if v["family"] == fam):
        roots = sorted({n.split("#")[0] for _, n in mods[m]["entries"]})
        for r in roots:
            if len(cur) == CHUNK:
                chunks.append(cur)
                cur = []
            cur.append((m, r))
        # a module boundary closes a chunk once it is half full (keeps chunks module-aligned)
        if len(cur) >= CHUNK // 2:
            chunks.append(cur)
            cur = []
    if cur:
        chunks.append(cur)
    return chunks


def run_export(fam, d, items, env, tag):
    d.mkdir(parents=True, exist_ok=True)
    ir = d / f"source-{tag}.ndjson"
    for p in (ir, ir.with_name(ir.name + ".blockers.json")):
        if p.exists():
            p.unlink()
    reqs = sorted({m for m, _ in items})
    v = d / f"Export_{tag}.v"
    v.write_text("From Rocq2LeanExport Require Import Loader.\n" + "".join(f"Require {m}.\n" for m in reqs)
                 + f'Rocq2Lean Export "{ir}" {" ".join(r for _, r in items)}.\n')
    cmd = ["systemd-run", "--user", "--scope", "-q", "-p", f"MemoryMax={MEMORY_MAX}", "-p", "MemorySwapMax=0",
           "rocq", "compile", "-I", str(EXP / "src"), "-Q", str(EXP / "theories"), "Rocq2LeanExport",
           *load_paths(fam), str(v)]
    t = time.time()
    try:
        p = subprocess.run(cmd, capture_output=True, text=True, env=env, timeout=TIMEOUT, cwd=d)
        rc, log = p.returncode, (p.stdout + p.stderr)
    except subprocess.TimeoutExpired as e:
        rc, log = "timeout", f"timeout after {TIMEOUT}s"
    (d / f"export-{tag}.log").write_text(f"$ {' '.join(cmd)}\n{log}\n[exit {rc}, {time.time() - t:.1f}s]\n")
    blockers = ir.with_name(ir.name + ".blockers.json")
    if rc == 0 and ir.exists():
        return "ok", ir, None
    if blockers.exists():
        return "unquotable", None, json.loads(blockers.read_text())
    return "failed", None, {"exit": rc, "log_tail": log[-1500:],
                            "resource_limit": rc in (-9, 137, "timeout") or "Killed" in log or "Out of memory" in log}


def do_chunk(fam, i, items, env, exporter_digest):
    d = W / f"export-{fam}" / f"chunk-{i:03d}"
    key = sha(json.dumps([items, exporter_digest]).encode())
    res_p = d / "result.json"
    if res_p.exists():
        r = json.loads(res_p.read_text())
        if r.get("key") == key:
            return r
    res = {"key": key, "chunk": i, "roots": [r for _, r in items], "modules": sorted({m for m, _ in items}),
           "irs": [], "unquotable": {}, "failed": {}}
    queue, n = [items], 0
    while queue:
        part = queue.pop(0)
        tag = f"{n:02d}"
        n += 1
        st, ir, info = run_export(fam, d, part, env, tag)
        if st == "ok":
            res["irs"].append({"tag": tag, "ir": str(ir.relative_to(ROOT)), "ir_sha256": sha(ir.read_bytes()),
                               "roots": [r for _, r in part]})
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
            h = len(part) // 2
            queue += [part[:h], part[h:]]
        else:
            res["failed"][part[0][1]] = info
    res_p.write_text(json.dumps(res, indent=1, sort_keys=True) + "\n")
    return res


def main(fam, workers=2):
    import rocq2lean
    env = rocq2lean.opam_env()
    log = W / f"export-{fam}" / "plugin-build.log"
    log.parent.mkdir(parents=True, exist_ok=True)
    plugin = rocq2lean.build_exporter(log)
    exporter_digest = {"plugin_sha256": sha(Path(plugin).read_bytes()), "load_paths": load_paths(fam)}
    chunks = plan(fam)
    t = time.time()
    with ProcessPoolExecutor(workers) as ex:
        futs = [ex.submit(do_chunk, fam, i, c, env, exporter_digest) for i, c in enumerate(chunks)]
        results = []
        for i, f in enumerate(futs):
            r = f.result()
            results.append(r)
            print(f"{fam} chunk {i + 1}/{len(chunks)}: {len(r['roots'])} roots, {len(r['irs'])} IR, "
                  f"{len(r['unquotable'])} unquotable, {len(r['failed'])} failed  [{time.time() - t:.0f}s]", flush=True)
    summary = {"family": fam, "chunk_size": CHUNK, "memory_max": MEMORY_MAX, "timeout_s": TIMEOUT,
               "exporter": exporter_digest, "chunks": len(results),
               "roots": sum(len(r["roots"]) for r in results),
               "unquotable": sum(len(r["unquotable"]) for r in results),
               "failed": sum(len(r["failed"]) for r in results)}
    (W / f"export-{fam}" / "summary.json").write_text(json.dumps(summary, indent=1) + "\n")
    print(json.dumps(summary))


if __name__ == "__main__":
    main(sys.argv[1], int(sys.argv[2]) if len(sys.argv) > 2 else 2)

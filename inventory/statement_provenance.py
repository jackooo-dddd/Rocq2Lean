"""Corpus provenance for the merged statement-mode run (docs/ASSEMBLY.md does not cover this;
see reports/statement_only/PROVENANCE.md).

The corpus IR (`runs/st-corpus*/source.ndjson`) is merged from 36 chunk exports made by the inventory
driver (`inventory/export.py`, statement mode), which — unlike `rocq2lean export` — wrote no source
snapshot and ran no Rocq round trip. This tool supplies that evidence *retrospectively*, labelled as
current revalidation evidence (it did not exist at export time), and binds it into a corpus manifest:

    snapshot   one snapshot per chunk: chunk IR digest (and the digest the export recorded), the
               export request (Export_XX.v), load paths, the exporter plugin used at export vs now,
               every library .vo and its .v source (digest now; whether its mtime precedes the export),
               toolchain lock and fingerprint, implementation tree
    roundtrip  the CLI's fresh-process Rocq round trip (tools/roundtrip.py: structural RtEq, opacity,
               dependency edges, native metadata, statement-preparation re-derivation, every
               ordered universe pair) on each chunk IR, in its own export context
    union      global consistency of the merged universe facts: one Rocq process loading every
               module of both families (the common source context, Classic load paths ⊇ modern) checks
               that every merged fact holds there (`Rocq2Lean CheckRelation`; `le` is entailed by a
               native `lt`), so a single environment satisfies the union
    manifest   the corpus manifest: chunks (IR, snapshot, round trip), merge re-derivation (every
               merged record is byte-identical to its chunk copies; merged universe line = union of the
               chunks'), root coverage (all protected declarations), union check, tools, outputs
               (translation report, consumer, audit) — every entry by SHA-256
    check      recompute everything the manifest binds; any missing or altered evidence is rejected

    python3 -I inventory/statement_provenance.py snapshot|roundtrip|union|manifest|check [RUN] [--jobs N]
"""
import hashlib
import json
import os
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import rocq2lean as R  # noqa: E402

W = ROOT / ".work" / "inventory"
EXPORT = os.environ.get("STATEMENT_EXPORT", "export-statement")      # chunk directories' prefix
PV = ROOT / ".work" / os.environ.get("STATEMENT_PROVENANCE", "provenance")   # evidence directory
OUT = ROOT / "reports" / "statement_only" / "provenance"
EVIDENCE = ("retrospective revalidation: created after the chunk exports, from the files present now; "
            "it is not a record that existed at export time")


def sha(p):
    return R.sha256_file(p)


def chunks(export=None):
    """(family, chunk dir, result, ir record) for every chunk IR of the statement exports."""
    out = []
    for fam in ("modern", "classic"):
        for rp in sorted((W / f"{export or EXPORT}-{fam}").glob("chunk-*/result.json")):
            r = json.loads(rp.read_text())
            for x in r["irs"]:
                out.append((fam, rp.parent, r, x))
    return out


def cid(fam, d, x):
    return f"{fam}-{d.name}-{x['tag']}"


def requires(d, x):
    return [l.split()[1].rstrip(".") for l in open(d / f"Export_{x['tag']}.v") if l.startswith("Require ")]


def snapshot():
    OUT.mkdir(parents=True, exist_ok=True)
    (PV / "snapshots").mkdir(parents=True, exist_ok=True)
    lock, fp, impl = R.lock_sha(), R.toolchain_fingerprint(), R.impl_tree_sha256()
    plugin_now = sha(R.EXPORTER / "src" / "rocq2lean_export_plugin.cmxs")
    idx = {}
    for fam, d, r, x in chunks():
        ir = ROOT / x["ir"]
        export_time = ir.stat().st_mtime
        with open(ir) as fh:
            for i, line in enumerate(fh):
                if i == 2:
                    libs = json.loads(line)["libraries"]
                    break
        lib_rec = []
        for l in libs:
            vo = Path(l["vo"]) if l["vo"] else None
            v = vo.with_suffix(".v") if vo else None
            lib_rec.append({"dirpath": l["dirpath"], "vo": l["vo"], "vo_sha256": sha(vo) if vo and vo.exists() else None,
                            "vo_mtime_before_export": bool(vo and vo.exists() and vo.stat().st_mtime <= export_time),
                            "v": str(v) if v and v.exists() else None, "v_sha256": sha(v) if v and v.exists() else None})
        snap = {"schema": "rocq2lean-chunk-snapshot/1", "evidence": EVIDENCE, "created": time.strftime("%Y-%m-%dT%H:%M:%S%z"),
                "chunk": cid(fam, d, x), "family": fam, "ir": str(ir), "ir_sha256": sha(ir),
                "ir_sha256_recorded_at_export": x["ir_sha256"], "ir_matches_export_record": sha(ir) == x["ir_sha256"],
                "request": {"file": str(d / f"Export_{x['tag']}.v"), "sha256": sha(d / f"Export_{x['tag']}.v"),
                            "roots": x["roots"], "requires": requires(d, x)},
                "load_paths": r["exporter"]["load_paths"],
                "exporter_plugin_sha256_at_export": r["exporter"]["plugin_sha256"],
                "exporter_plugin_sha256_now": plugin_now,
                "libraries": lib_rec, "toolchains_lock_sha256": lock, "toolchain_fingerprint": fp["digest"],
                "impl_tree_sha256": impl}
        p = PV / "snapshots" / f"{snap['chunk']}.json"
        p.write_text(json.dumps(snap, indent=1) + "\n")
        idx[snap["chunk"]] = {"snapshot": str(p), "sha256": sha(p), "ir_matches_export_record": snap["ir_matches_export_record"],
                              "libraries": len(lib_rec), "libraries_missing": sum(1 for l in lib_rec if l["vo_sha256"] is None),
                              "libraries_newer_than_export": sum(1 for l in lib_rec if l["vo_sha256"] and not l["vo_mtime_before_export"])}
    (PV / "snapshots.json").write_text(json.dumps(idx, indent=1) + "\n")
    print(f"{len(idx)} chunk snapshots; IR mismatches {sum(1 for v in idx.values() if not v['ir_matches_export_record'])}; "
          f"missing libraries {sum(v['libraries_missing'] for v in idx.values())}; "
          f"libraries newer than their export {sum(v['libraries_newer_than_export'] for v in idx.values())}")


def rt_tools():
    """What a round trip depends on: the round-trip tool, the exporter plugin (its Rocq commands) and
    RtEq.v (the implementation tree changes with any edit; the round trip does not depend on it)."""
    return {"roundtrip_py": sha(ROOT / "tools" / "roundtrip.py"),
            "exporter_plugin": sha(R.EXPORTER / "src" / "rocq2lean_export_plugin.cmxs"),
            "rteq_v": sha(ROOT / "rocq" / "roundtrip" / "RtEq.v")}


def _roundtrip_one(item):
    fam, d, r, x = item
    c = cid(fam, d, x)
    out = PV / "roundtrip" / c
    done = out / "result.json"
    if done.exists():
        prev = json.loads(done.read_text())
        if prev.get("ir_sha256") == sha(ROOT / x["ir"]) and prev.get("tools") == rt_tools():
            return c, prev
    out.mkdir(parents=True, exist_ok=True)
    t = time.time()
    p = subprocess.run([sys.executable, "-I", str(ROOT / "tools" / "roundtrip.py"), str(ROOT / x["ir"]), str(out),
                        *r["exporter"]["load_paths"], "--", *requires(d, x)], env=R.opam_env(), capture_output=True, text=True)
    rt = json.loads((out / "roundtrip.json").read_text()) if (out / "roundtrip.json").exists() else {}
    res = {"chunk": c, "status": rt.get("status", "NOT_RUN"), "exit": p.returncode, "seconds": round(time.time() - t, 1),
           "checked": rt.get("checked"), "problems": (rt.get("problems") or [])[:20],
           "roundtrip_json": str(out / "roundtrip.json"), "roundtrip_sha256": sha(out / "roundtrip.json") if rt else None,
           "ir_sha256": sha(ROOT / x["ir"]), "tools": rt_tools(), "evidence": EVIDENCE}
    done.write_text(json.dumps(res, indent=1) + "\n")
    print(f"{c}: {res['status']} ({res['checked']} decls, {res['seconds']} s)", flush=True)
    return c, res


RT_BASE = OUT / "ROUNDTRIP_TOOLS_BASE.json"
EXPORTER_SOURCES = ["rocq/exporter/src/*.ml", "rocq/exporter/src/*.mli", "rocq/exporter/src/*.mlg",
                    "rocq/exporter/src/*.mllib", "rocq/exporter/theories/*.v", "rocq/exporter/_RocqProject"]


def reuse_section(pv=None):
    """Whether the chunk evidence (round trips made with the tools they record) applies to the current
    implementation. Applicable when the round-trip tool and RtEq.v are unchanged and the exporter
    plugin's sources differ from those of the plugin the round trips used only by added lines (new
    commands; the export, statement preparation and round-trip commands are unchanged). The chunk IRs
    themselves are bound by digest (unchanged inputs); the union check depends only on them and on
    the Rocq libraries (snapshots). The base (`ROUNDTRIP_TOOLS_BASE.json`) records which commit's
    exporter sources built the round trips' plugin."""
    cur = rt_tools()
    rts = json.loads((Path(pv or PV) / "roundtrip.json").read_text())
    used = {json.dumps(v["tools"], sort_keys=True) for v in rts.values()}
    out = {"round_trip_tools": None, "current_tools": cur, "problems": []}
    if len(used) != 1:
        out.update(status="NOT_APPLICABLE", problems=["chunk round trips used different tools"])
        return out
    used = json.loads(used.pop())
    out["round_trip_tools"] = used
    if used == cur:
        out["status"] = "SAME_TOOLS"
        return out
    for k in ("roundtrip_py", "rteq_v"):
        if used[k] != cur[k]:
            out["problems"].append(f"{k} changed since the round trips")
    if used["exporter_plugin"] != cur["exporter_plugin"]:
        base = json.loads(RT_BASE.read_text()) if RT_BASE.exists() else {}
        if base.get("exporter_plugin_sha256") != used["exporter_plugin"]:
            out["problems"].append("no record of the sources of the round trips' exporter plugin")
        else:
            g = lambda *a: subprocess.run(["git", "-C", str(ROOT), *a], capture_output=True, text=True).stdout
            num = g("diff", "--numstat", base["exporter_sources_commit"], "--", *EXPORTER_SOURCES)
            diff = g("diff", base["exporter_sources_commit"], "--", *EXPORTER_SOURCES)
            files = []
            for line in num.splitlines():
                a_, r_, f_ = line.split("\t")
                files.append({"file": f_, "added": int(a_), "removed": int(r_)})
            out["exporter_source_diff"] = {"base_commit": base["exporter_sources_commit"], "files": files,
                                           "added": sum(f["added"] for f in files), "removed": sum(f["removed"] for f in files),
                                           "diff_sha256": hashlib.sha256(diff.encode()).hexdigest()}
            if any(f["removed"] for f in files):
                out["problems"].append("exporter sources changed (lines removed or modified) since the round trips' plugin")
    out["status"] = "APPLICABLE" if not out["problems"] else "NOT_APPLICABLE"
    return out


def roundtrip(jobs=3, only=None):
    items = [it for it in chunks() if only is None or cid(it[0], it[1], it[3]) in only]
    # largest chunks first (they bound the wall time)
    items.sort(key=lambda it: -os.path.getsize(ROOT / it[3]["ir"]))
    with ThreadPoolExecutor(jobs) as ex:
        list(ex.map(_roundtrip_one, items))
    # the index covers every chunk round trip done so far (batches may be run separately)
    res = {}
    for rp in sorted((PV / "roundtrip").glob("*/result.json")):
        x = json.loads(rp.read_text())
        res[x["chunk"]] = x
    (PV / "roundtrip.json").write_text(json.dumps(res, indent=1) + "\n")
    bad = [c for c, v in res.items() if v["status"] != "OK"]
    print(f"{len(res)} chunk round trips; not OK: {bad}")


def union(run, jobs=4):
    """Every merged universe fact must hold in one environment loading all modules of both families."""
    run = Path(run)
    with open(run / "source.ndjson") as fh:
        for i, line in enumerate(fh):
            if i == 4:
                facts = json.loads(line)
                break
    rels = facts["relations"]
    allreq = sorted({m for _, d, _, x in chunks() for m in requires(d, x)})
    lp = json.loads((W / f"{EXPORT}-classic" / "chunk-0000" / "result.json").read_text())["exporter"]["load_paths"]
    for _, _, r, _ in chunks():               # every chunk's load paths are among the Classic ones
        for i in range(0, len(r["exporter"]["load_paths"]), 3):
            if r["exporter"]["load_paths"][i:i + 3] != lp[i:i + 3] and r["exporter"]["load_paths"][i:i + 3] not in [lp[j:j + 3] for j in range(0, len(lp), 3)]:
                raise SystemExit(f"load path {r['exporter']['load_paths'][i:i + 3]} not in the common context")
    plugin = R.EXPORTER
    out = PV / "union"
    out.mkdir(parents=True, exist_ok=True)
    parts = [rels[k::jobs] for k in range(jobs)]

    def one(k):
        tsv, res_f = out / f"union_{k}.tsv", out / f"union_{k}.out"
        tsv.write_text("".join(f'{x["l"]}\t{x["r"]}\t{x["rel"]}\n' for x in parts[k]))
        v = ["From Rocq2LeanExport Require Import Loader.", *[f"Require {m}." for m in allreq],
             f'Rocq2Lean CheckRelations "{tsv}" "{res_f}".']
        f = out / f"Union_{k}.v"
        f.write_text("\n".join(v) + "\n")
        t = time.time()
        p = subprocess.run(["rocq", "compile", "-I", str(plugin / "src"), "-Q", str(plugin / "theories"), "Rocq2LeanExport",
                            *lp, str(f)], capture_output=True, text=True, env=R.opam_env())
        (out / f"union_{k}.log").write_text(p.stdout + p.stderr)
        ok = mism = unknown = 0
        entailed, bad = 0, []
        for line in (res_f.read_text().splitlines() if res_f.exists() else []):
            if line.startswith("UREL_OK"):
                ok += 1
            elif line.startswith("UREL_MISMATCH"):
                a, b = line.split()[1:3]
                want = line.split("expected=")[1].split()[0]
                native = line.split("native=")[1].split()[0]
                if want == "le" and native == "lt":
                    entailed += 1          # the union graph is stronger: le holds
                else:
                    bad.append(line)
            elif line.startswith("UREL_UNKNOWN"):
                unknown += 1
                bad.append(line)
        return {"part": k, "facts": len(parts[k]), "exact": ok, "entailed_by_stronger": entailed, "violated_or_unknown": len(bad),
                "examples": bad[:10], "exit": p.returncode, "seconds": round(time.time() - t, 1)}

    with ThreadPoolExecutor(jobs) as ex:
        res = list(ex.map(one, range(jobs)))
    from collections import defaultdict
    both = defaultdict(set)
    for x in rels:
        both[(x["l"], x["r"])].add(x["rel"])
    summary = {"schema": "rocq2lean-union-universes/1", "evidence": EVIDENCE, "ir": str(run / "source.ndjson"),
               "ir_sha256": sha(run / "source.ndjson"), "levels": len(facts["levels"]), "facts": len(rels),
               "pairs_with_le_and_lt": sum(1 for v in both.values() if len(v) > 1),
               "common_context": {"load_paths": lp, "requires": len(allreq)},
               "parts": res,
               "status": "OK" if all(p["exit"] == 0 and p["violated_or_unknown"] == 0 and p["exact"] + p["entailed_by_stronger"] == p["facts"]
                                     for p in res) else "INCONSISTENT"}
    (PV / "union.json").write_text(json.dumps(summary, indent=1) + "\n")
    print(json.dumps({k: v for k, v in summary.items() if k != "parts"}), [(p["exact"], p["entailed_by_stronger"], p["violated_or_unknown"], p["seconds"]) for p in res])


def _merge_rederive(run, export=None):
    """Re-derive the merge from the chunk IRs: every merged declaration record byte-identical to each
    chunk copy; merged universe facts = union of the chunks' relations; merged levels = union."""
    store, problems = {}, []
    rels, flevels = set(), set()
    for fam, d, r, x in chunks(export):
        with open(ROOT / x["ir"]) as fh:
            for i, line in enumerate(fh):
                if i == 4:
                    u = json.loads(line)
                    flevels.update(u["levels"])
                    rels.update(json.dumps(z, sort_keys=True) for z in u["relations"])
                    continue
                if not (line.startswith('{"kind":"constant"') or line.startswith('{"kind":"inductive"')):
                    continue
                j = line.index('"name":"') + 8
                n = line[j:line.index('"', j)]
                h = hashlib.sha256(line.rstrip("\n").encode()).hexdigest()
                if store.setdefault(n, h) != h:
                    problems.append(f"{n}: chunk copies differ")
    merged, mrels, mlev = {}, set(), set()
    with open(Path(run) / "source.ndjson") as fh:
        for i, line in enumerate(fh):
            if i == 4:
                u = json.loads(line)
                mlev = set(u["levels"])
                mrels = {json.dumps(z, sort_keys=True) for z in u["relations"]}
                continue
            if line.startswith('{"kind":"constant"') or line.startswith('{"kind":"inductive"'):
                j = line.index('"name":"') + 8
                merged[line[j:line.index('"', j)]] = hashlib.sha256(line.rstrip("\n").encode()).hexdigest()
    for n, h in merged.items():
        if store.get(n) != h:
            problems.append(f"{n}: merged record is not a chunk copy")
    if set(merged) != set(store):
        problems.append(f"merged declarations differ from the chunks' ({len(merged)} vs {len(store)})")
    if mrels != rels or mlev != flevels:
        problems.append("merged universe facts are not the union of the chunks'")
    return {"declarations": len(merged), "chunk_declarations": len(store), "universe_relations": len(mrels), "problems": problems[:20],
            "status": "OK" if not problems else "MISMATCH"}


def manifest(run):
    run = Path(run).resolve()
    snaps = json.loads((PV / "snapshots.json").read_text())
    rts = json.loads((PV / "roundtrip.json").read_text())
    uni = json.loads((PV / "union.json").read_text())
    prot = json.loads((ROOT / "reports/prosa_inventory/protected_interface.json").read_text())["protected"]
    with open(run / "source.ndjson") as fh:
        fh.readline()
        roots = [r["name"] for r in json.loads(fh.readline())["roots"]]
    chunk_entries = {}
    for fam, d, r, x in chunks():
        c = cid(fam, d, x)
        chunk_entries[c] = {"ir": str(ROOT / x["ir"]), "ir_sha256": sha(ROOT / x["ir"]),
                            "snapshot": snaps[c]["snapshot"], "snapshot_sha256": snaps[c]["sha256"],
                            "roundtrip": rts[c]["roundtrip_json"], "roundtrip_sha256": rts[c]["roundtrip_sha256"],
                            "roundtrip_status": rts[c]["status"]}
    m = {"schema": "rocq2lean-corpus-manifest/1", "evidence": EVIDENCE, "created": time.strftime("%Y-%m-%dT%H:%M:%S%z"),
         "run": str(run), "chunks": chunk_entries,
         "merge": _merge_rederive(run),
         "root_coverage": {"protected": len(prot), "in_merged_roots": len(set(prot) & set(roots)),
                           "missing": sorted(set(prot) - set(roots))[:20]},
         "union_universes": {"file": str(PV / "union.json"), "sha256": sha(PV / "union.json"), "status": uni["status"]},
         "files": {k: {"path": str(run / k), "sha256": sha(run / k)} for k in
                   ("source.ndjson", "contract.json", "translation_report.json", "translation_manifest.json",
                    "consumer_result.json", "audit.json", "conversion_deps/joined.json", "conversion_deps/result.json",
                    "source_instances.json")
                   if (run / k).exists()},
         "reuse": reuse_section(),
         # (only a validated run is bound: its fresh-process consumer and independent audit are OK)
         "checks": {k: (json.loads((run / f).read_text()).get("status") if (run / f).exists() else None)
                    for k, f in (("consumer", "consumer_result.json"), ("audit", "audit.json"),
                                 ("source_instances", "source_instances.json"))},
         "provenance_dir": str(PV), "export_dirs": EXPORT,
         "tools": {"impl_tree_sha256": R.impl_tree_sha256(), "translator_build_sha256": R.lean_build_sha256(),
                   "toolchains_lock_sha256": R.lock_sha(), "toolchain_fingerprint": R.toolchain_fingerprint()["digest"],
                   "exporter_plugin_sha256": sha(R.EXPORTER / "src" / "rocq2lean_export_plugin.cmxs")}}
    ok = (all(v["roundtrip_status"] == "OK" for v in chunk_entries.values()) and m["merge"]["status"] == "OK"
          and m["root_coverage"]["in_merged_roots"] == len(prot) and uni["status"] == "OK"
          and all(v["ir_matches_export_record"] for v in snaps.values())
          and m["reuse"]["status"] in ("SAME_TOOLS", "APPLICABLE")
          and m["checks"]["consumer"] == "OK" and m["checks"]["audit"] == "OK"
          and m["checks"]["source_instances"] == "OK")
    m["status"] = "CORPUS_PROVENANCE_BOUND" if ok else "CORPUS_PROVENANCE_INCOMPLETE"
    OUT.mkdir(parents=True, exist_ok=True)
    (OUT / "CORPUS_MANIFEST.json").write_text(json.dumps(m, indent=1) + "\n")
    print(m["status"], json.dumps(m["merge"]), m["root_coverage"]["in_merged_roots"], uni["status"])
    return m


def check(manifest_path=None):
    """Recompute every digest the manifest binds (chunk IRs, snapshots, round trips and their status,
    the union check, the run's files) and re-derive the merge; any missing or altered evidence fails."""
    mp = Path(manifest_path or OUT / "CORPUS_MANIFEST.json")
    m = json.loads(mp.read_text())
    problems = []

    def bound(path, want, what):
        p = Path(path) if path else None
        if p is None or not p.exists():
            problems.append(f"{what}: missing ({path})")
        elif sha(p) != want:
            problems.append(f"{what}: altered ({path})")

    if m.get("status") != "CORPUS_PROVENANCE_BOUND":
        problems.append(f"manifest status {m.get('status')}")
    for k, f in (("consumer", "consumer_result.json"), ("audit", "audit.json"), ("source_instances", "source_instances.json")):
        if k in (m.get("checks") or {}) and Path(m["run"], f).exists() and json.loads(Path(m["run"], f).read_text()).get("status") != "OK":
            problems.append(f"the run's {k} is not OK")
    for c, e in m["chunks"].items():
        bound(e["ir"], e["ir_sha256"], f"chunk {c} IR")
        bound(e["snapshot"], e["snapshot_sha256"], f"chunk {c} snapshot")
        bound(e["roundtrip"], e["roundtrip_sha256"], f"chunk {c} round trip")
        if e["roundtrip"] and Path(e["roundtrip"]).exists() and json.loads(Path(e["roundtrip"]).read_text()).get("status") != "OK":
            problems.append(f"chunk {c}: round trip not OK")
    bound(m["union_universes"]["file"], m["union_universes"]["sha256"], "union universe check")
    for k, e in m["files"].items():
        bound(e["path"], e["sha256"], f"run file {k}")
    # the chunk evidence must still apply to the implementation the check runs with
    ru = reuse_section(m.get("provenance_dir"))
    if ru["status"] not in ("SAME_TOOLS", "APPLICABLE"):
        problems += [f"chunk evidence not applicable to the current tools: {p}" for p in ru["problems"]]
    if "reuse" in m and m["reuse"].get("status") not in ("SAME_TOOLS", "APPLICABLE"):
        problems.append(f"manifest reuse status {m['reuse'].get('status')}")
    if not problems:
        mr = _merge_rederive(m["run"], m.get("export_dirs"))
        if mr["status"] != "OK":
            problems += mr["problems"]
    res = {"manifest": str(mp), "status": "OK" if not problems else "PROVENANCE_REJECTED", "problems": problems[:30]}
    print(json.dumps(res, indent=1))
    return res


if __name__ == "__main__":
    cmd = sys.argv[1]
    jobs = int(sys.argv[sys.argv.index("--jobs") + 1]) if "--jobs" in sys.argv else 3
    pos = [a for a in sys.argv[2:] if not a.startswith("--") and not a.isdigit()]
    if cmd == "snapshot":
        snapshot()
    elif cmd == "roundtrip":
        roundtrip(jobs, set(pos) or None)
    elif cmd == "union":
        union(pos[0] if pos else ROOT / "runs" / "st-corpus", jobs)
    elif cmd == "manifest":
        manifest(pos[0] if pos else ROOT / "runs" / "st-corpus")
    elif cmd == "check":
        sys.exit(0 if check(pos[0] if pos else None)["status"] == "OK" else 1)

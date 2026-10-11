"""Resolve and lock the inventory's source scope: reports/prosa_inventory/scope.lock.json.

Modern Prosa v0.6 (commit 414e667, the sha512-checked release archive of that commit) and Classic
Prosa (ProsaBuddy f692cb7, prosaworkspace/classic), with RTS f23ca67 as the read-only provenance
authority. Every identity claim below is checked here, from the raw trees, on every run.
"""
import csv
import hashlib
import json
import re
import os
import subprocess
import sys
import tarfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CFG = json.loads((ROOT / "inventory" / "config.json").read_text())
OUT = ROOT / "reports" / "prosa_inventory"
X = lambda p: Path(os.path.expanduser(p)) if p.startswith("~") else ROOT / p


def sha256(b):
    return hashlib.sha256(b).hexdigest()


def tree_hashes(d, suffix=".v"):
    out = {}
    for p in sorted(Path(d).rglob(f"*{suffix}")):
        out[str(p.relative_to(d))] = sha256(p.read_bytes())
    return out


def git(repo, *a, binary=False):
    p = subprocess.run(["git", "-C", str(repo), *a], capture_output=True, check=True)
    return p.stdout if binary else p.stdout.decode()


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    rts = X(CFG["rts"]["snapshot"])
    rts_commit = (rts.parent / (rts.name + ".COMMIT")).read_text().strip()
    assert rts_commit == CFG["rts"]["commit"], f"RTS snapshot is {rts_commit}"
    auth = {f: sha256((rts / f).read_bytes()) for f in CFG["rts"]["authority_files"]}

    # ---- modern: release archive -> pristine tree; reconcile with RTS's per-file hashes of 414e667
    m = CFG["modern"]
    arch = X(m["release_archive"])
    assert hashlib.sha512(arch.read_bytes()).hexdigest() == m["release_sha512"], "release archive checksum"
    pristine = tree_hashes(X(m["pristine"]))
    rts_inv = {r["file"]: r for r in csv.DictReader(open(rts / "Prosa-Shunqi/Validation/planning/v06_dependency/file_inventory.csv"))}
    scope_rts = json.loads((rts / "Prosa-Shunqi/Validation/planning/v06_dependency/scope_manifest.json").read_text())
    assert scope_rts["authoritative_source"]["commit"] == m["commit"]
    rec = {"rts_files": len(rts_inv), "release_files": len(pristine),
           "identical": sorted(f for f in rts_inv if pristine.get(f) == rts_inv[f]["sha256"]),
           "differing": sorted(f for f in rts_inv if f in pristine and pristine[f] != rts_inv[f]["sha256"]),
           "missing_in_release": sorted(f for f in rts_inv if f not in pristine),
           "extra_in_release": sorted(f for f in pristine if f not in rts_inv)}
    rec["identical"] = len(rec["identical"])
    working = tree_hashes(X(m["working"]))
    patches = sorted((ROOT / "compat" / "prosa-0.6" / "patches").glob("*.patch"))
    modern = {**{k: m[k] for k in ("project", "version", "commit", "git_tree", "logical_root")},
              "release_archive": {"path": m["release_archive"], "sha512": m["release_sha512"],
                                  "url": "https://gitlab.mpi-sws.org/RT-PROOFS/rt-proofs/-/archive/v0.6/rt-proofs-v0.6.tar.gz"},
              "reference_snapshot": m["pristine"], "working_snapshot": m["working"],
              "reconciliation_with_rts": rec,
              "build_groups": {"main": sum(1 for r in rts_inv.values() if r["build_group"] == "main"),
                               "refinements": sum(1 for r in rts_inv.values() if r["build_group"] == "refinements")},
              "compatibility_patches": [{"file": str(p.relative_to(ROOT)), "sha256": sha256(p.read_bytes())} for p in patches],
              "working_files_changed_by_patches": sorted(f for f in pristine if working.get(f) != pristine[f])}

    # ---- classic: ProsaBuddy f692cb7, prosaworkspace/classic, extracted pristine from the commit
    c = CFG["classic"]
    pb = X(c["checkout"])
    assert git(pb, "rev-parse", c["commit"] + "^{tree}").strip() == c["git_tree"], "ProsaBuddy tree"
    pr = X(c["pristine"])
    if not pr.exists():
        pr.mkdir(parents=True)
        tar = subprocess.run(["git", "-C", str(pb), "archive", c["commit"], c["directory"]], capture_output=True, check=True).stdout
        subprocess.run(["tar", "-x", "-C", str(pr), "--strip-components=1"], input=tar, check=True)
    cls = {"classic/" + k: v for k, v in tree_hashes(pr / "classic").items()}   # keys: classic/<path>
    # the case-study plan's 49 files, cross-checked by hash
    fo = list(csv.DictReader(open(rts / "Prosa-Shunqi/classic-prosa/casestudy-translation/file_order.csv")))
    cross = {"plan_files": len(fo), "hash_identical": sum(1 for r in fo if cls.get(r["source"]) == r["sha256"]),
             "not_in_tree": [r["source"] for r in fo if r["source"] not in cls]}
    # ProsaBuddy's util is a symlink into its bundled rt-proofs-v0.6: compare that bundle with v0.6
    bundle = {}
    for f in git(pb, "ls-tree", "-r", "--name-only", c["commit"], "prosaworkspace/rt-proofs-v0.6").split():
        if f.endswith(".v") and "/classic/" not in f:
            bundle[f.replace("prosaworkspace/rt-proofs-v0.6/", "")] = sha256(git(pb, "show", f"{c['commit']}:{f}", binary=True))
    util_imports = set()
    for p in (pr / "classic").rglob("*.v"):
        for line in p.read_text(errors="replace").splitlines():
            if "Require" in line:
                for tok in re.findall(r"\bprosa\.util\.[A-Za-z0-9_.]*[A-Za-z0-9_]", line):
                    util_imports.add(tok)
    prelude = rts / "Prosa-Shunqi/classic-prosa/rocq93-port/Rocq90Compat.v"
    rpatch = rts / "Prosa-Shunqi/classic-prosa/rocq93-port/prosabuddy-classic-rocq93.patch"
    classic = {"repository": c["repository"], "commit": c["commit"], "git_tree": c["git_tree"],
               "directory": c["directory"], "logical_root": c["logical_root"], "files": len(cls),
               "reference_snapshot": c["pristine"],
               "case_study_plan_cross_check": cross,
               "v06_bundle_vs_official": {"files": len(bundle),
                                          "identical": sum(1 for f, h in bundle.items() if pristine.get(f) == h),
                                          "differing": sorted(f for f, h in bundle.items() if pristine.get(f) != h)},
               "v06_util_imported": sorted(util_imports),
               "v06_util_imported_identical": bool(util_imports) and all(bundle.get(m.replace("prosa.", "").replace(".", "/") + ".v") ==
                                                  pristine.get(m.replace("prosa.", "").replace(".", "/") + ".v") for m in util_imports),
               "v06_util_imported_patched_in_working_snapshot": sorted(
                   m for m in util_imports if m.replace("prosa.", "").replace(".", "/") + ".v" in modern["working_files_changed_by_patches"]),
               "build_configuration": {"load_paths": "classic/ as prosa.classic; prosa.util from the modern working snapshot (the M6 "
                                                     "compatibility patches apply; see v06_util_imported_patched_in_working_snapshot)",
                                       "prelude": {"file": str(prelude.relative_to(rts)), "sha256": sha256(prelude.read_bytes()),
                                                   "role": "restores two Rocq 9.0 defaults (ssreflect rewrite goal order, intuition solver); no source edit"},
                                       "not_applied": {"file": str(rpatch.relative_to(rts)), "sha256": sha256(rpatch.read_bytes()),
                                                       "reason": "edits a proof script; recorded as a proposed minimal change for any file that needs it"}},
               "excluded_copies": [
                   {"path": "prosabuddy prosaworkspace/rt-proofs-v0.6/classic/", "reason": "second ProsaBuddy copy, not used by its case-study build (RTS README: differs in proof scripts of ranks 36 and 47)"},
                   {"path": "RTS Prosa-Shunqi/classic-prosa/classic/", "reason": "2022 classic-prosa branch head, kept by RTS for reference only"},
                   {"path": "RTS_Papers case studies, Prosa v0.4 release", "reason": "out of scope by instruction"}]}
    lock = {"schema": "rocq2lean-prosa-scope/1",
            "scope": "complete Prosa v0.6 + complete Classic Prosa (ProsaBuddy port), with the dependencies their declarations reach",
            "rts": {"repository": CFG["rts"]["repository"], "commit": rts_commit,
                    "snapshot": "git archive of the pinned commit (read-only)", "authority_files": auth},
            "rocq2lean": {"commit": git(ROOT, "rev-parse", "HEAD").strip(),
                          "toolchains_lock_sha256": sha256((ROOT / "toolchains.lock.json").read_bytes())},
            "toolchain": json.loads((ROOT / "toolchains.lock.json").read_text()),
            "modern": modern, "classic": classic}
    (OUT / "scope.lock.json").write_text(json.dumps(lock, indent=1) + "\n")
    print(f"modern: {rec['identical']}/{rec['rts_files']} files identical to RTS (414e667); classic: {len(cls)} files, "
          f"plan {cross['hash_identical']}/{cross['plan_files']}; bundle identical {classic['v06_bundle_vs_official']['identical']}"
          f"/{len(bundle)}; util imported identical: {classic['v06_util_imported_identical']}")


if __name__ == "__main__":
    main()

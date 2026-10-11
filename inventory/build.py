"""Build coverage, per file, without changing the translator's environment (switch from the lock).

Modern: the working snapshot (.work/prosa-0.6-rocq93, built by scripts/setup-prosa --full); a file
without its .vo is compiled once here to record why (e.g. CoqEAL refinements: package not installed).
Classic: an isolated copy of the .v sources of ProsaBuddy f692cb7 classic/ (its committed Rocq 9.0
build products are dropped) in .work/classic-f692cb7-build, compiled as
prosa.classic with the v0.6 util of the modern working snapshot and the RTS prelude Rocq90Compat.v
(-ri Compat.Rocq90Compat: two Rocq 9.0 defaults, no source edit). `make -k`: every file gets its own
outcome. Writes .work/inventory/build.json and per-file logs; a failed file keeps an unknown
declaration count downstream.
"""
import json
import os
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CFG = json.loads((ROOT / "inventory" / "config.json").read_text())
W = ROOT / ".work" / "inventory"
LOG = W / "logs"
SW = json.loads((ROOT / "toolchains.lock.json").read_text())["rocq"]["opam_switch"]
X = lambda p: Path(os.path.expanduser(p)) if p.startswith("~") else ROOT / p
ENV = dict(os.environ, PATH=f"{Path.home()}/.local/bin:" + os.environ["PATH"])


def rocq(args, cwd, log):
    p = subprocess.run(["opam", "exec", f"--switch={SW}", "--", *args], cwd=cwd, capture_output=True, text=True, env=ENV)
    log.write_text(f"$ {' '.join(map(str, args))}  (cwd={cwd})\n{p.stdout}{p.stderr}[exit {p.returncode}]\n")
    return p.returncode, p.stdout + p.stderr


def classify(out):
    if "Cannot find a physical path bound to logical path" in out or "Unable to locate library" in out:
        lib = next((l for l in out.splitlines() if "library" in l.lower()), "")
        return "MISSING_LIBRARY", lib.strip()[:200]
    return "COMPILE_ERROR", next((l for l in out.splitlines() if l.startswith("Error")), out.strip()[-200:])[:300]


def git_blob(data):
    import hashlib
    return hashlib.sha1(b"blob %d\0" % len(data) + data).hexdigest()


def proof_lines(text):
    """Line numbers (1-based) strictly inside Proof ... Qed/Defined/Admitted blocks."""
    inside, out = False, set()
    for i, l in enumerate(text.splitlines(), 1):
        s = l.strip()
        if inside and (s.startswith(("Qed.", "Defined.", "Admitted.", "Abort.")) or s in ("Qed.", "Defined.")):
            inside = False
            continue
        if inside:
            out.add(i)
        if s.startswith("Proof"):
            inside = True
    return out


def apply_authorized_patches(cb):
    """Apply the explicitly authorized compatibility patches to the isolated build copy, exactly.
    Each patch: git blob identity checked, `patch -F0 --dry-run` first (no fuzz, no offset beyond
    exact context), every changed line must lie inside a proof block of the original file (no
    definition, statement or assumption edited), before/after hashes recorded in .patches.json.
    Idempotent: a file whose hash is already the recorded post-patch hash is not patched again."""
    import hashlib
    import re
    rec_p = cb / ".patches.json"
    rec = json.loads(rec_p.read_text()) if rec_p.exists() else []
    done = {r["git_blob"] for r in rec}
    for ap in CFG["classic"].get("authorized_patches", []):
        if ap["git_blob"] in done:
            continue
        pf = X(CFG["rts"]["snapshot"]) / ap["path"]
        data = pf.read_bytes()
        if git_blob(data) != ap["git_blob"]:
            raise SystemExit(f"authorized patch identity mismatch: {pf} is {git_blob(data)}, expected {ap['git_blob']}")
        txt = data.decode()
        targets = re.findall(r"^\+\+\+ b/(\S+)", txt, re.M)
        entry = {"git_blob": ap["git_blob"], "source": ap["source"], "authorization": ap["authorization"], "files": []}
        for t in targets:
            f = cb / t
            before = f.read_bytes()
            orig_lines = proof_lines(before.decode())
            for h in re.finditer(r"^@@ -(\d+),(\d+) \+\d+,\d+ @@", txt, re.M):
                start = int(h.group(1))
                body = txt[h.end():].split("\n@@", 1)[0].splitlines()[1:]
                ln = start
                for l in body:
                    if l.startswith("-"):
                        if ln not in orig_lines:
                            raise SystemExit(f"authorized patch edits {t}:{ln} outside a proof block")
                        ln += 1
                    elif l.startswith(" "):
                        ln += 1
            entry["files"].append({"file": t, "sha256_before": hashlib.sha256(before).hexdigest()})
        dry = subprocess.run(["patch", f"-p{ap['strip']}", "-F0", "--dry-run", "--no-backup-if-mismatch", "-i", str(pf)],
                             cwd=cb, capture_output=True, text=True)
        if dry.returncode != 0 or "offset" in dry.stdout or "fuzz" in dry.stdout:
            raise SystemExit(f"authorized patch does not apply exactly: {dry.stdout}{dry.stderr}")
        app = subprocess.run(["patch", f"-p{ap['strip']}", "-F0", "--no-backup-if-mismatch", "-i", str(pf)],
                             cwd=cb, capture_output=True, text=True)
        if app.returncode != 0:
            raise SystemExit(f"authorized patch failed: {app.stdout}{app.stderr}")
        for fe in entry["files"]:
            fe["sha256_after"] = hashlib.sha256((cb / fe["file"]).read_bytes()).hexdigest()
        entry["patch_output"] = app.stdout.strip()
        entry["changed_lines_inside_proof_blocks"] = True
        rec.append(entry)
        rec_p.write_text(json.dumps(rec, indent=1) + "\n")
        (cb / ".built").unlink(missing_ok=True)
        (cb / ".patched_rebuild").write_text("")
    return rec


def main():
    W.mkdir(parents=True, exist_ok=True)
    LOG.mkdir(parents=True, exist_ok=True)
    res = {"switch": SW, "modern": {}, "classic": {}}
    # ---- modern; the refinements need CoqEAL: its five modules that Prosa imports (hrel, param,
    # refinements, pos, binnat), compiled unchanged from coq-community/coqeal ce3d1d6 (sha256-checked,
    # RTS Validation/tooling/coqeal/coqeal_2.1.2.json) into .work/coqeal-ce3d1d6; nothing installed
    mw = X(CFG["modern"]["working"])
    ce = ROOT / ".work" / "coqeal-ce3d1d6"
    rec = json.loads((X(CFG["rts"]["snapshot"]) / "Prosa-Shunqi/Validation/tooling/coqeal/coqeal_2.1.2.json").read_text())
    ceal = {"commit": (ce / "COMMIT").read_text().strip() if (ce / "COMMIT").exists() else None, "files": {}}
    if ceal["commit"] == rec["commit"]:
        import hashlib
        for f in rec["files"]:
            p = ce / f["path"]
            ok = hashlib.sha256(p.read_bytes()).hexdigest() == f["sha256"]
            if ok and not p.with_suffix(".vo").exists():
                rc, out = rocq(["rocq", "compile", "-R", "..", "CoqEAL", p.name], p.parent, LOG / f"coqeal-{p.stem}.log")
                ok = rc == 0
            ceal["files"][f["path"]] = "COMPILED" if ok and p.with_suffix(".vo").exists() else "FAILED"
    res["coqeal"] = ceal
    lp_ceal = ["-R", str(ce), "CoqEAL"] if ceal["files"] and all(v == "COMPILED" for v in ceal["files"].values()) else []
    pending = [v for v in sorted(mw.rglob("*.v")) if not v.with_suffix(".vo").exists()]
    out_of = {}
    while pending:                      # dependency order: retry while some file still compiles
        progress = False
        for v in list(pending):
            rel = str(v.relative_to(mw))
            rc, out = rocq(["rocq", "compile", "-R", ".", "prosa", *lp_ceal, "-w", "-notation-overriden,-parsing", rel], mw,
                           LOG / ("modern-" + rel.replace("/", "_") + ".log"))
            out_of[rel] = (rc, out)
            if rc == 0:
                pending.remove(v)
                progress = True
        if not progress:
            break
    for v in sorted(mw.rglob("*.v")):
        rel = str(v.relative_to(mw))
        if v.with_suffix(".vo").exists():
            res["modern"][rel] = {"build": "COMPILED", **({"extra_load_path": "CoqEAL ce3d1d6"} if rel in out_of else {})}
            continue
        st, why = classify(out_of[rel][1])
        res["modern"][rel] = {"build": st, "reason": why, "log": str((LOG / ("modern-" + rel.replace("/", "_") + ".log")).relative_to(ROOT))}
    # ---- classic: isolated copy, compiled with the prelude
    cp, cb = X(CFG["classic"]["pristine"]), X(CFG["classic"]["working"])
    if not (cb / ".built").exists():
        shutil.rmtree(cb, ignore_errors=True)
        # sources only: ProsaBuddy's commit also contains its own build products (Rocq 9.0 .vo, .glob,
        # .aux, …), which must neither be reused nor count as compiled here
        shutil.copytree(cp, cb, ignore=shutil.ignore_patterns("*.vo", "*.vos", "*.vok", "*.glob", "*.aux", ".*.aux",
                                                              "*.d", "Makefile*", "*.conf"))
        stale = [str(p) for p in cb.rglob("*") if p.suffix in (".vo", ".vos", ".vok", ".glob")]
        assert not stale, stale[:3]
        comp = cb / "compat"
        comp.mkdir()
        shutil.copy(X(CFG["rts"]["snapshot"]) / "Prosa-Shunqi/classic-prosa/rocq93-port/Rocq90Compat.v", comp)
        rc, out = rocq(["rocq", "compile", "-Q", ".", "Compat", "Rocq90Compat.v"], comp, LOG / "classic-prelude.log")
        assert rc == 0, out
        files = sorted(str(p.relative_to(cb / "classic")) for p in (cb / "classic").rglob("*.v"))
        (cb / "classic" / "_CoqProject").write_text(
            f"-R . prosa.classic\n-R {mw} prosa\n-Q {comp} Compat\n"
            '-arg "-w -notation-overriden,-parsing,-projection-no-head-constant,-ambiguous-paths"\n'
            '-arg "-ri Compat.Rocq90Compat"\n' + "\n".join(files) + "\n")
        rocq(["rocq", "makefile", "-f", "_CoqProject", "-o", "Makefile"], cb / "classic", LOG / "classic-makefile.log")
        j = os.environ.get("JOBS", "16")
        rocq(["make", "-k", f"-j{j}"], cb / "classic", LOG / "classic-make.log")
        (cb / ".built").write_text("")
    patches = apply_authorized_patches(cb)
    if (cb / ".patched_rebuild").exists():
        # rebuild after the authorized patch: make rebuilds the patched file and its dependents only;
        # the pre-patch make log is kept (classic-make.log), the post-patch one is separate
        j = os.environ.get("JOBS", "16")
        rocq(["make", "-k", f"-j{j}"], cb / "classic", LOG / "classic-make-postpatch.log")
        (cb / ".patched_rebuild").unlink()
        (cb / ".built").write_text("")
    mlog = (LOG / "classic-make.log").read_text()
    if (LOG / "classic-make-postpatch.log").exists():
        mlog = (LOG / "classic-make-postpatch.log").read_text()
    for v in sorted((cb / "classic").rglob("*.v")):
        rel = str(v.relative_to(cb / "classic"))
        if v.with_suffix(".vo").exists():
            res["classic"]["classic/" + rel] = {"build": "COMPILED"}
            continue
        # first error mentioning this file in the make log, else UPSTREAM (a dependency failed)
        lines = mlog.splitlines()
        # an error of this file: its `File "./rel", line …` line directly followed by `Error: …`
        hit = [i for i, l in enumerate(lines) if f'File "./{rel}"' in l and i + 1 < len(lines) and lines[i + 1].startswith("Error")]
        if hit:
            seg = "\n".join(lines[hit[0]:hit[0] + 4])
            st, why = classify(seg)
            why = lines[hit[0]].strip() + " " + " ".join(x.strip() for x in lines[hit[0] + 1:hit[0] + 4])
        else:
            st, why = "NOT_BUILT_DEPENDENCY_FAILED", "a file it requires did not compile"
        res["classic"]["classic/" + rel] = {"build": st, "reason": why[:400], "log": str((LOG / "classic-make.log").relative_to(ROOT))}
    patched = {fe["file"]: fe | {"patch": p["source"], "git_blob": p["git_blob"]} for p in patches for fe in p["files"]}
    for f, x in res["classic"].items():
        if f in patched:
            x["compatibility_patch"] = patched[f]
            x["provenance"] = "proof terms from the compatibility-patched build (authorized RTS patch), not the historical environment"
    res["classic_authorized_patches"] = patches
    # a documented minimal change (not applied) for each failing Classic file, where one is known
    prop = "Prosa-Shunqi/classic-prosa/rocq93-port/prosabuddy-classic-rocq93.patch"
    ptxt = (X(CFG["rts"]["snapshot"]) / prop).read_text()
    for f, x in res["classic"].items():
        if x["build"] == "COMPILE_ERROR" and f in ptxt and f not in patched:
            x["proposed_change"] = {"source": f"RTS {prop}", "kind": "proof script (one hunk), statement unchanged",
                                    "applied": False}
    (W / "build.json").write_text(json.dumps(res, indent=1) + "\n")
    for fam in ("modern", "classic"):
        from collections import Counter
        print(fam, dict(Counter(x["build"] for x in res[fam].values())))


if __name__ == "__main__":
    main()

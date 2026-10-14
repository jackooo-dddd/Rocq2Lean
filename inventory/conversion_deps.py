"""Conversion dependence on termination-lowered definitions (Task B, docs/TERMINATION.md).

A definition lowered with a termination obligation (`Acc.rec` over its call relation) does not
unfold definitionally in Lean while its obligation is a hypothesis (and, after assembly, only as far
as the supplied proof reduces). A declaration whose Lean translation needs that unfolding — a type
that is only correct up to computing the recursion, `t3 : T3 := 0` — must be identified, from the
source: Rocq re-runs the statement preparation of every constant that reaches a lowered definition
(dependency closure of the merged IR), once in the prepared environment and once with the lowered
definitions' bodies removed (`Rocq2Lean CheckConversionDeps`); refused only in the second = needs
the unfolding (CONV_NEEDS). The result is joined with the translation outcome of each declaration.

    python3 -I inventory/conversion_deps.py RUN [--jobs N]

Writes RUN/conversion_deps/ and reports/statement_only/termination/CONVERSION_DEPENDENCE.json.
"""
import json
import subprocess
import sys
import time
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
sys.path.insert(0, str(ROOT / "inventory"))
import rocq2lean as R  # noqa: E402
import statement_provenance as P  # noqa: E402

OUT = ROOT / "reports" / "statement_only" / "termination"


def main(run, jobs=2):
    run = Path(run).resolve()
    rep = json.loads((run / "translation_report.json").read_text())
    rows = {r["source"]: r for r in rep["results"]}
    lowered = sorted({r["synthesized_from"] for r in rep["results"] if r.get("synthetic_kind") == "termination"})
    decls, deps = {}, {}
    with open(run / "source.ndjson") as fh:
        for line in fh:
            d = json.loads(line)
            if d.get("kind") in ("constant", "inductive"):
                decls[d["name"]] = d
                dd = d.get("deps") or {}
                deps[d["name"]] = set(dd.get("type", [])) | set(dd.get("body", []))
    # every declaration whose dependency closure reaches a lowered definition
    memo = {}

    def reaches(n, stack=()):
        if n in memo:
            return memo[n]
        if n in stack:
            return False
        r = any(m in lowered or reaches(m, stack + (n,)) for m in deps.get(n, ()))
        memo[n] = r
        return r

    dependents = sorted(n for n in decls if n not in lowered and reaches(n))
    # an extracted obligation exists only in the prepared environment: it is checked through its
    # parent definition (re-preparing the parent re-checks its obligations' statements), and gets the
    # parent's verdict
    parent = {n: decls[n]["native"]["obligation"]["of"] for n in dependents
              if decls[n].get("body_state") == "obligation" and ((decls[n].get("native") or {}).get("obligation") or {}).get("of")}
    consts = sorted({parent.get(n, n) for n in dependents if decls[n]["kind"] == "constant"})
    out = run / "conversion_deps"
    out.mkdir(exist_ok=True)
    allreq = sorted({m for _, d, _, x in P.chunks() for m in P.requires(d, x)})
    lp = json.loads((P.W / f"{P.EXPORT}-classic" / "chunk-0000" / "result.json").read_text())["exporter"]["load_paths"]
    parts = [consts[k::jobs] for k in range(jobs)]

    def one(k):
        dfile, ofile = out / f"deps_{k}.txt", out / f"conv_{k}.txt"
        dfile.write_text("".join(n + "\n" for n in parts[k]))
        v = ["From Rocq2LeanExport Require Import Loader.", *[f"Require {m}." for m in allreq],
             f'Rocq2Lean CheckConversionDeps "{";".join(lowered)}" "{dfile}" "{ofile}".']
        f = out / f"Conv_{k}.v"
        f.write_text("\n".join(v) + "\n")
        t = time.time()
        p = subprocess.run(["rocq", "compile", "-I", str(R.EXPORTER / "src"), "-Q", str(R.EXPORTER / "theories"), "Rocq2LeanExport",
                            *lp, str(f)], capture_output=True, text=True, env=R.opam_env())
        (out / f"conv_{k}.log").write_text(p.stdout + p.stderr)
        return {"part": k, "exit": p.returncode, "seconds": round(time.time() - t, 1)}

    with ThreadPoolExecutor(jobs) as ex:
        procs = list(ex.map(one, range(jobs)))
    verdict = {}
    for k in range(jobs):
        f = out / f"conv_{k}.txt"
        for line in (f.read_text().splitlines() if f.exists() else []):
            tag, name = line.split(" ", 2)[:2]
            verdict[name] = (tag, line.split(" ", 2)[2] if line.count(" ") >= 2 else "")
    for o, par in parent.items():
        if par in verdict:
            tag, why = verdict[par]
            verdict[o] = (tag, f"through its parent {par}: {why}" if why else f"through its parent {par}")
    missing = [n for n in consts if n not in verdict]
    ok_st = ("TRANSLATED_AND_CHECKED", "PENDING_KERNEL_CHECKED", "STATEMENT_KERNEL_CHECKED", "STATEMENT_PENDING_KERNEL_CHECKED")
    joined = {}
    for n in dependents:
        v = verdict.get(n, ("INDUCTIVE_NOT_ANALYZED" if decls[n]["kind"] == "inductive" else "NOT_RUN", ""))
        joined[n] = {"rocq": v[0], "reason": v[1][:300], "lean": rows.get(n, {}).get("status"),
                     "lean_message": (rows.get(n, {}).get("message") or "")[:200]}
    needs = sorted(n for n, x in joined.items() if x["rocq"] == "CONV_NEEDS")
    # consistency with the translation: a dependent that needs the unfolding cannot be claimed; a
    # dependent refused directly by Lean's kernel should be explained by such a need
    claimed_needing = [n for n in needs if joined[n]["lean"] in ok_st]
    lean_direct = [n for n, x in joined.items() if x["lean"] in ("KERNEL_REJECTED", "TRANSLATION_FAILED")]
    unexplained = [n for n in lean_direct if joined[n]["rocq"] != "CONV_NEEDS"]
    res = {"schema": "rocq2lean-conversion-dependence/1", "run": str(run),
           "translation_report_sha256": R.sha256_file(run / "translation_report.json"),
           "lowered": lowered, "dependents": len(dependents), "constants_analyzed": len(consts) - len(missing),
           "not_analyzed": missing[:50], "processes": procs,
           "by_rocq_verdict": dict(Counter(x["rocq"] for x in joined.values())),
           "needs_unfolding": [{"declaration": n, **joined[n]} for n in needs],
           "claimed_although_needing_unfolding": claimed_needing,
           "lean_kernel_failures_among_dependents": lean_direct,
           "lean_kernel_failures_not_explained": unexplained,
           "status": "OK" if not claimed_needing and not missing else "INCONSISTENT"}
    (out / "joined.json").write_text(json.dumps(joined, indent=1) + "\n")
    OUT.mkdir(parents=True, exist_ok=True)
    (OUT / "CONVERSION_DEPENDENCE.json").write_text(json.dumps(res, indent=1) + "\n")
    print(json.dumps({k: res[k] for k in ("lowered", "dependents", "constants_analyzed", "by_rocq_verdict", "status")}))
    print("needs unfolding:", needs[:30])
    print("lean kernel failures not explained:", unexplained[:30])


if __name__ == "__main__":
    jobs = int(sys.argv[sys.argv.index("--jobs") + 1]) if "--jobs" in sys.argv else 2
    main(sys.argv[1], jobs)

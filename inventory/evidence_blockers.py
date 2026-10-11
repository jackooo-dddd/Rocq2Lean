"""Known blockers beyond preflight: direct translation failures recorded by existing runs, Rocq's
rejection of source instances, and the census export's own limits.

A run's direct failure counts for a declaration only when the run's implementation digest is the
current one and its elaborated record of the declaration is byte-identical to the inventory's
(the same rule as inventory/coverage.py). When another such run translated the same declaration,
the failure depends on the request (universe levels, statement specializations) and is reported
under "context_dependent" instead of as a blocker. BLOCKED_DEPENDENCY results are not blockers themselves:
the graph recomputes them for every root.

Writes .work/inventory/extra_blockers.json:
  {"declarations": {name: [{"reason", "category", "status", "source", "detail"}]},
   "export": {"unquotable": ..., "failed": ..., "stack_overflow_default": ...}}

    python3 -I inventory/evidence_blockers.py
"""
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
W = ROOT / ".work" / "inventory"
sys.path.insert(0, str(ROOT / "tools"))
sys.path.insert(0, str(ROOT / "inventory"))
from coverage import RUNS, run_evidence  # noqa: E402

NAME = re.compile(r"(?:Rocq\.)?[A-Za-z_][A-Za-z0-9_']*(?:[./][A-Za-z_][A-Za-z0-9_']*)+(?:\.\d+)?")


def normalize(msg):
    """The reusable mechanism of a translator message: drop names, levels and solver details."""
    m = re.split(r" \[(?:last tier|R3↓ attempt):", msg)[0].split("\n")[0]
    m = re.sub(r"\(some [^)]*\)", "…", m)
    m = NAME.sub("…", m)
    m = re.sub(r"\bu_[A-Za-z0-9_]+\b", "…", m)
    m = re.sub(r"\[u_residual_\d+\]|\[…\]", "[…]", m)
    m = re.sub(r"parameter \d+", "parameter N", m)
    m = re.sub(r"\(\(kernel\).*", "(kernel rejection)", m)
    return re.sub(r"\s+", " ", m).strip()


def category(status, reason):
    if status in ("UNIVERSE_REJECTED", "INSTANCE_REJECTED") or "quality Prop" in reason or "universe" in reason:
        return "universe_instance"
    if status == "KERNEL_REJECTED":
        return "incorrect_implementation"
    return "missing_rule"


def main():
    import rocq2lean
    impl = rocq2lean.impl_tree_sha256()
    merged = {f: json.loads((W / f"merge-{f}.json").read_text()) for f in ("modern", "classic")}
    inv = {**merged["classic"]["digests"], **merged["modern"]["digests"]}
    out, translated = {}, {}
    runs = []
    for run in RUNS:
        d = ROOT / "runs" / run
        if not (d / "source_snapshot.json").exists():
            continue
        ev, meta = run_evidence(run, impl, inv)
        runs.append(meta)
        for n, e in ev.items():
            if e.get("current_impl") and e.get("identical_source") and e.get("status") in ("TRANSLATED_AND_CHECKED", "BOOTSTRAP_RESOLVED"):
                translated.setdefault(n, []).append(run)
        rep = json.loads((d / "translation_report.json").read_text()) if (d / "translation_report.json").exists() else {"results": []}
        for r in rep["results"]:
            n, st = r.get("source"), r.get("status")
            if st in ("TRANSLATED_AND_CHECKED", "BOOTSTRAP_RESOLVED", "BLOCKED_DEPENDENCY") or not n:
                continue
            e = ev.get(n, {})
            if not (e.get("current_impl") and e.get("identical_source")):
                continue
            msg = r.get("message") or r.get("rule") or st
            out.setdefault(n, [])
            reason = f"{st}: {normalize(msg)}"
            if not any(x["reason"] == reason for x in out[n]):
                out[n].append({"reason": reason, "category": category(st, msg), "status": st,
                               "source": f"translation:{run}", "detail": msg[:600]})
        si = d / "source_instances.json"
        if si.exists():
            for n, v in json.loads(si.read_text()).get("checked", {}).items():
                e = ev.get(n, {})
                if v != "INSTANCE_OK" and e.get("current_impl") and e.get("identical_source"):
                    reason = f"{v}: R2B-P statement specialization rejected by Rocq's kernel"
                    out.setdefault(n, [])
                    if not any(x["reason"] == reason for x in out[n]):
                        out[n].append({"reason": reason, "category": "universe_instance", "status": v,
                                       "source": f"source_instances:{run}", "detail": f"{n}: {v}"})
    # a failure of a declaration that another current run translated (same elaborated record) depends
    # on the request (levels, specializations): reported as context-dependent, not as a blocker
    context = {}
    for n in list(out):
        if n in translated:
            context[n] = [dict(x, translated_in=sorted(translated[n])) for x in out.pop(n)]
    export = {f: {"unquotable": merged[f]["unquotable"], "failed": merged[f]["failed"],
                  "stack_overflow_default": merged[f].get("stack_overflow_default", [])} for f in merged}
    (W / "extra_blockers.json").write_text(json.dumps({"implementation": impl, "declarations": out, "context_dependent": context, "export": export,
                                                       "translated_in_current_runs": {n: sorted(v) for n, v in sorted(translated.items())},
                                                       "runs": runs}, indent=1, sort_keys=True) + "\n")
    for n, v in sorted(out.items()):
        print("blocker", n, [x["reason"] for x in v])
    for n, v in sorted(context.items()):
        print("context-dependent", n, [x["reason"] for x in v], v[0]["translated_in"])


if __name__ == "__main__":
    main()

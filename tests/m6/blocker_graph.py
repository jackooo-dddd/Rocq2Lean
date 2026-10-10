"""Complete blocker graph of a target in a run (types and proof bodies), for ordering the work.

    python3 -I tests/m6/blocker_graph.py RUN_DIR TARGET OUT.json

Over the target's required closure (dependencies through types and bodies):
* translation leaves: declarations the translator attempted and rejected (status other than
  TRANSLATED_AND_CHECKED / BOOTSTRAP_RESOLVED / BLOCKED_DEPENDENCY), with their message;
* static leaves: declarations not attempted (BLOCKED_DEPENDENCY) for which the preflight
  classifier (tools/preflight.py) reports blockers of their own: they will fail even after their
  dependencies are fixed;
* pending: declarations blocked only by dependencies, with no known blocker of their own.
Leaves are classified (missing feature / exporter or metadata defect / universe solving / kernel
rejection / audit / resource limit), and each leaf records how many closure declarations depend on
it and a dependency path from the target.
"""
import collections
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tools"))
import preflight as PF  # noqa: E402


def classify(status, message):
    m = message or ""
    if status == "UNSUPPORTED_FEATURE":
        return "missing_feature"
    if status == "EXPORT_VALIDATION_FAILED":
        return "exporter_or_metadata_defect"
    if status == "UNIVERSE_REJECTED" or (status == "KERNEL_REJECTED" and ("Type" in m or "universe" in m.lower())):
        return "universe_solving"
    if status == "KERNEL_REJECTED":
        return "kernel_rejection"
    if status == "AUDIT_REJECTED":
        return "audit"
    if status in ("TIMEOUT", "RESOURCE_LIMIT"):
        return "resource_limit"
    return "other:" + status


def main(run, target, out):
    run = Path(run)
    lines = [json.loads(l) for l in open(run / "source.ndjson")]
    decls = {d["name"]: d for d in lines if d.get("kind") in ("constant", "inductive")}
    rep = json.loads((run / "translation_report.json").read_text())
    st = {x["source"]: x for x in rep["results"]}
    deps = {n: [x for x in (d["deps"]["type"] + d["deps"].get("body", [])) if x != n] for n, d in decls.items()}
    closure, todo, parent = set(), [target], {target: None}
    while todo:
        n = todo.pop()
        if n in closure or n not in decls:
            continue
        closure.add(n)
        for m in deps[n]:
            if m not in parent:
                parent[m] = n
            todo.append(m)

    def path(n):
        p = []
        while n is not None:
            p.append(n)
            n = parent.get(n)
        return list(reversed(p))
    inds = PF.Inductives(decls)
    static = {n: PF.classify(decls[n], inds) for n in closure}
    leaves, pending = {}, []
    for n in sorted(closure):
        s = st.get(n, {}).get("status")
        if s in ("TRANSLATED_AND_CHECKED", "BOOTSTRAP_RESOLVED"):
            continue
        if s != "BLOCKED_DEPENDENCY":
            leaves[n] = {"kind": "translation", "status": s, "category": classify(s, st[n].get("message")),
                         "message": (st[n].get("message") or "")[:400]}
        elif static[n][0] != "CANDIDATE_SUPPORTED":
            reasons = sorted(static[n][1])
            leaves[n] = {"kind": "static", "status": "UNSUPPORTED_FEATURE (preflight)", "category": "missing_feature",
                         "message": "; ".join(reasons)}
        else:
            pending.append(n)
    # transitive dependents of each leaf within the closure
    rdeps = collections.defaultdict(set)
    for n in closure:
        for m in deps[n]:
            rdeps[m].add(n)

    def dependents(n):
        seen, todo = set(), [n]
        while todo:
            x = todo.pop()
            for y in rdeps[x]:
                if y not in seen:
                    seen.add(y)
                    todo.append(y)
        return seen
    for n, l in leaves.items():
        l["blocks"] = len(dependents(n))
        l["path_from_target"] = path(n)
    by_cat = collections.Counter(l["category"] for l in leaves.values())
    res = {"target": target, "run": str(run), "closure_size": len(closure),
           "accepted": sum(1 for n in closure if st.get(n, {}).get("status") in ("TRANSLATED_AND_CHECKED", "BOOTSTRAP_RESOLVED")),
           "leaves_by_category": dict(by_cat), "leaves": dict(sorted(leaves.items(), key=lambda kv: -kv[1]["blocks"])),
           "pending_only_by_dependencies": len(pending)}
    Path(out).write_text(json.dumps(res, indent=2) + "\n")
    print(f"{target}: closure {len(closure)}, accepted {res['accepted']}, leaves {len(leaves)} {dict(by_cat)}, "
          f"pending {len(pending)}")
    for n, l in list(res["leaves"].items())[:40]:
        print(f"  [{l['category']}] blocks {l['blocks']:4d}  {n}: {l['message'][:120]}")


if __name__ == "__main__":
    main(*sys.argv[1:4])

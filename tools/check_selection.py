#!/usr/bin/env python3
"""Check a selection against a full run (docs/INCREMENTAL.md §6).

    check_selection.py BASE_RUN FULL_RUN SELECTION [-o OUT.json]

FULL_RUN is a full run of the changed translator on the same export. The script replays the incremental
algorithm with the full run as the oracle: in export order, a declaration is translated if it is
selected, an inductive, or depends on a tainted declaration; a translated declaration whose rows differ
between BASE_RUN and FULL_RUN (messages and diagnostics aside) is changed, and it taints its dependents
(as does one translated because of a tainted dependency). A declaration whose rows differ but that would
have been replayed is a *miss*: the selection was not sound for this change. Exit status 1 if any.
"""
import argparse, json, sys


def rows(run):
    out, dec = {}, json.JSONDecoder()
    for l in open(f"{run}/translation_report.json"):
        if not l.startswith('{"'):
            continue
        try:
            r, _ = dec.raw_decode(l)
        except ValueError:
            continue
        if "results" in r or "source" not in r:
            continue
        r.pop("message", None)
        r.pop("universe_diagnostics", None)
        out[r["source"]] = json.dumps(r, sort_keys=True)
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("base")
    ap.add_argument("full")
    ap.add_argument("selection")
    ap.add_argument("-o", "--out")
    a = ap.parse_args()
    recs = [json.loads(l) for l in open(f"{a.base}/replay_records.jsonl") if l.strip()]
    deps = {}
    for l in open(f"{a.base}/source.ndjson"):
        d = json.loads(l)
        if d.get("kind") == "constant":
            deps[d["name"]] = d["deps"]["type"] + d["deps"]["body"]
        elif d.get("kind") == "inductive":
            deps[d["name"]] = [x for x in d["deps"]["type"] if x != d["name"]]
    sel = {l.strip() for l in open(a.selection) if l.strip()}
    rb, rf = rows(a.base), rows(a.full)
    timing = {d["source"]: d.get("time_ms", 0)
              for d in json.load(open(f"{a.base}/translation_timing.json"))["declarations"]}
    tainted, changed, misses, translated = set(), [], [], []
    for rc in recs:
        n = rc["decl"]
        srcs = [r["source"] for r in rc["rows"]]
        differs = any(rb.get(s) != rf.get(s) for s in srcs)
        dep_t = any(x in tainted for x in deps.get(n, []))
        if n in sel or rc["kind"] == "inductive" or dep_t:
            translated.append(n)
            if differs:
                changed.append(n)
                tainted.add(n)
            elif dep_t:
                tainted.add(n)
        elif differs:
            misses.append(n)
    res = {"selected": len(sel), "translated": len(translated),
           "translated_base_ms": sum(timing.get(n, 0) for n in translated),
           "changed": changed, "misses": misses}
    if a.out:
        json.dump(res, open(a.out, "w"), indent=1)
    print(json.dumps({k: (v if not isinstance(v, list) else len(v)) for k, v in res.items()}))
    for m in misses[:20]:
        print("MISS", m)
    sys.exit(1 if misses else 0)


if __name__ == "__main__":
    main()

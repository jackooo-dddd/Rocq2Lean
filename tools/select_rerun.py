#!/usr/bin/env python3
"""Select the declarations an incremental run translates again (docs/INCREMENTAL.md).

    select_rerun.py BASE_RUN_DIR [--flag F ...] [--failed] [--status S ...] [--names FILE] [--all-constants] -o OUT

A declaration is selected when any criterion holds:

* --flag F: one of its attempts in the base run had tier flag F (e.g. `un`: coherence by unification), i.e.
  the changed code can only run in attempts with that flag;
* --failed: its base row is not claimed (every failure, blocked rows included);
* --status S: its base row has status S;
* --names FILE: it is listed (one per line).

The selection only needs to cover the declarations the change can affect *directly*: the translator
translates again every declaration that depends, directly or through others, on one whose rows changed.
Inductives are always translated.
"""
import argparse, json, re, sys

CLAIMED = {"TRANSLATED_AND_CHECKED", "STATEMENT_KERNEL_CHECKED", "PENDING_KERNEL_CHECKED",
           "STATEMENT_PENDING_KERNEL_CHECKED", "BOOTSTRAP_RESOLVED"}

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("base")
    ap.add_argument("--flag", action="append", default=[])
    ap.add_argument("--failed", action="store_true")
    ap.add_argument("--status", action="append", default=[])
    ap.add_argument("--names")
    ap.add_argument("-o", "--out", required=True)
    a = ap.parse_args()
    decls = [json.loads(l) for l in open(f"{a.base}/replay_records.jsonl") if l.strip()]
    timing = {d["source"]: d for d in json.load(open(f"{a.base}/translation_timing.json"))["declarations"]}
    status = {}
    for d in decls:
        for r in d["rows"]:
            if r["source"] == d["decl"]:
                status[d["decl"]] = (timing.get(d["decl"]) or {}).get("status", "")
    names = set()
    if a.names:
        names = {l.strip() for l in open(a.names) if l.strip()}
    pick = []
    lab = re.compile(r"^[a-z]\[([^\]]*)\]")
    for d in decls:
        n = d["decl"]
        why = None
        if n in names: why = "listed"
        st = status.get(n, "")
        if a.failed and st not in CLAIMED: why = why or "failed"
        if st in a.status: why = why or "status"
        if a.flag:
            for t in (timing.get(n) or {}).get("tier_times", []):
                m = lab.match(t[0])
                if m and set(m.group(1).split(",")) & set(a.flag):
                    why = why or "flag"; break
        if why: pick.append(n)
    with open(a.out, "w") as f:
        for n in pick: f.write(n + "\n")
    print(f"selected {len(pick)} of {len(decls)} declarations", file=sys.stderr)

if __name__ == "__main__":
    main()

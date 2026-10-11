"""Merge the chunked exports of a family into one declaration store, checking consistency.

Every declaration is exported by every chunk whose closure reaches it. The exporter is deterministic,
so all copies of one kernel name must be byte-identical; a difference is recorded as an
inconsistency (and the first copy kept), never silently resolved. Reads only the IRs listed in each chunk's result.json.

Writes .work/inventory/ir-<fam>.ndjson (one line per distinct declaration, sorted by name) and
.work/inventory/merge-<fam>.json.

    python3 -I inventory/merge.py modern|classic
"""
import hashlib
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
W = ROOT / ".work" / "inventory"


def main(fam):
    d = W / f"export-{fam}"
    store, digests, inconsistent = {}, {}, {}
    requested, unquotable, failed, chunks, stack = {}, {}, {}, [], []
    for rp in sorted(d.glob("chunk-*/result.json")):
        r = json.loads(rp.read_text())
        chunks.append({"chunk": r["chunk"], "roots": len(r["roots"]), "irs": [x["ir"] for x in r["irs"]],
                       "unquotable": len(r["unquotable"]), "failed": len(r["failed"])})
        unquotable.update(r["unquotable"])
        failed.update(r["failed"])
        stack += [dict(x, chunk=r["chunk"]) for x in r.get("stack_overflow_default", [])]
        for x in r["irs"]:
            ir = ROOT / x["ir"]
            if hashlib.sha256(ir.read_bytes()).hexdigest() != x["ir_sha256"]:
                raise SystemExit(f"{ir}: changed since its chunk result was recorded")
            with open(ir) as fh:
                for line in fh:
                    k = line[:40]
                    if '"kind":"roots"' in k or '"kind": "roots"' in k:
                        for e in json.loads(line)["roots"]:
                            requested[e["requested"]] = e["name"]
                        continue
                    if not ('"constant"' in k or '"inductive"' in k):
                        continue
                    i = line.index('"name":"') + 8          # exporter output: compact JSON, kind then name
                    n = line[i:line.index('"', i)]
                    h = hashlib.sha256(line.encode()).hexdigest()
                    if n not in digests:
                        digests[n] = h
                        store[n] = line if line.endswith("\n") else line + "\n"
                    elif digests[n] != h:
                        inconsistent.setdefault(n, sorted({digests[n]}))
                        if h not in inconsistent[n]:
                            inconsistent[n].append(h)
    # enumerated entries that were not requested themselves are found in some closure (same record)
    mods = json.loads((W / "modules.json").read_text())["modules"]
    by_norm = {n.replace("/", "."): n for n in store}
    covered = {}
    for m, v in mods.items():
        if v["family"] != fam:
            continue
        for _, e in v["entries"]:
            r = e.split("#")[0]
            if r not in requested and r.replace("/", ".") in by_norm:
                covered[r] = by_norm[r.replace("/", ".")]
    requested_direct = dict(requested)
    requested.update(covered)
    # module aliases (`Module M := N.`, re-exports): the entry's name is not its kernel identity
    aliases = {r: n for r, n in requested.items() if r.replace("/", ".") != n.replace("/", ".")}
    with open(W / f"ir-{fam}.ndjson", "w") as fh:
        for n in sorted(store):
            fh.write(store[n])
    m = {"family": fam, "chunks": chunks, "declarations": len(store), "requested": requested,
         "requested_directly": sorted(requested_direct), "covered_by_closure": sorted(covered), "aliases": aliases,
         "unquotable": unquotable, "failed": failed, "stack_overflow_default": stack, "inconsistent_copies": inconsistent,
         "digests": digests}
    (W / f"merge-{fam}.json").write_text(json.dumps(m, sort_keys=True) + "\n")
    print(f"{fam}: {len(store)} distinct declarations, {len(requested_direct)} roots requested, {len(covered)} covered, {len(aliases)} aliases, {len(unquotable)} unquotable, "
          f"{len(failed)} failed, {len(inconsistent)} inconsistent copies")


if __name__ == "__main__":
    main(sys.argv[1])

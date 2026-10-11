"""Write the protected-interface manifest from the pinned inventory.

Protected: every Prosa v0.6 / Classic declaration whose role is `public_source` or
`generated_projection` (record and class fields), by kernel identity. Module-alias entries are not
declarations; their canonical declaration is protected through its own record. The manifest records
the digests of the scope lock and of declarations.jsonl it was derived from, so that a later
inventory change makes it stale (tools/protection.py refuses it).

    python3 -I inventory/protection_manifest.py          # write reports/prosa_inventory/protected_interface.json
    python3 -I inventory/protection_manifest.py --pin    # also pin its digest (tools/protected_interface.pin.json;
                                                         # an implementation change)
"""
import hashlib
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "reports" / "prosa_inventory"
sys.path.insert(0, str(ROOT / "tools"))
import protection  # noqa: E402


def main(pin=False):
    decl_p, lock_p = OUT / "declarations.jsonl", OUT / "scope.lock.json"
    names, by_fam = set(), {"modern": 0, "classic": 0}
    for line in open(decl_p):
        d = json.loads(line)
        if d["family"] in by_fam and d["role"] in ("public_source", "generated_projection"):
            names.add(d["name"])
            by_fam[d["family"]] += 1
    m = {"schema": protection.SCHEMA, "policy": protection.POLICY,
         "scope_lock_sha256": hashlib.sha256(lock_p.read_bytes()).hexdigest(),
         "declarations_sha256": hashlib.sha256(decl_p.read_bytes()).hexdigest(),
         "count": len(names), "by_family": by_fam, "protected": sorted(names)}
    mp = OUT / "protected_interface.json"
    mp.write_text(json.dumps(m, indent=1, sort_keys=True) + "\n")
    sha = hashlib.sha256(mp.read_bytes()).hexdigest()
    if pin:
        protection.PIN.write_text(json.dumps({"manifest": str(mp.relative_to(ROOT)), "sha256": sha}, indent=1) + "\n")
    print(f"protected interface: {len(names)} declarations {by_fam}; manifest sha256 {sha}{' (pinned)' if pin else ''}")


if __name__ == "__main__":
    main("--pin" in sys.argv[1:])

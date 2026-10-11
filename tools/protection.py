#!/usr/bin/env python3
"""P0 public-interface protection: the pinned protected set and its binding to an export.

The protected set is every public Prosa v0.6 / Classic declaration and record/class projection of
the pinned inventory (`reports/prosa_inventory/protected_interface.json`, written by
`inventory/protection_manifest.py`). Its SHA-256 is pinned in `tools/protected_interface.pin.json`
(part of the implementation tree). A protected declaration keeps its full source statement whether
it is a requested root or a dependency: no R2B-S result-sort lowering and no R2B-P specialization
of a statement level (policy below). Genuinely non-public dependencies keep the existing checked
specialization policy.

`load()` refuses the manifest when it is missing, when its digest differs from the pin (altered),
or when the inventory it was derived from changed (stale: the recorded digests of the scope lock
and of declarations.jsonl differ from the current files). `binding(names)` is the export's
contract field: the manifest digest, the policy and the protected names present in the export.
"""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PIN = ROOT / "tools" / "protected_interface.pin.json"
SCHEMA = "rocq2lean-protected-interface/1"
POLICY = {"refuse": ["R2B-S result-sort lowering", "R2B-P specialization of a statement level"],
          "applies_to": "every protected declaration, requested root or dependency",
          "unprotected_dependencies": "existing checked policy (R2B-P instances re-checked by Rocq at verify)"}


class ProtectionError(Exception):
    pass


def sha256_file(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def load():
    """(manifest, manifest_sha256); raises ProtectionError when missing, altered or stale."""
    if not PIN.exists():
        raise ProtectionError(f"protection pin missing: {PIN}")
    pin = json.loads(PIN.read_text())
    mp = ROOT / pin["manifest"]
    if not mp.exists():
        raise ProtectionError(f"protected-interface manifest missing: {mp}")
    got = sha256_file(mp)
    if got != pin["sha256"]:
        raise ProtectionError(f"protected-interface manifest altered: {mp} has SHA-256 {got}, pinned {pin['sha256']}")
    m = json.loads(mp.read_text())
    if m.get("schema") != SCHEMA or m.get("policy") != POLICY:
        raise ProtectionError("protected-interface manifest has an unknown schema or policy")
    for key, rel in (("scope_lock_sha256", "reports/prosa_inventory/scope.lock.json"),
                     ("declarations_sha256", "reports/prosa_inventory/declarations.jsonl")):
        f = ROOT / rel
        if not f.exists() or sha256_file(f) != m.get(key):
            raise ProtectionError(f"protected-interface manifest is stale: {rel} changed since the manifest was derived")
    names = m.get("protected")
    if not isinstance(names, list) or names != sorted(set(names)) or len(names) != m.get("count"):
        raise ProtectionError("protected-interface manifest is malformed (names not sorted/unique or count differs)")
    return m, got


def binding(exported_names):
    """Contract field for an export whose declarations are `exported_names`."""
    m, sha = load()
    prot = set(m["protected"])
    return {"schema": SCHEMA, "manifest_sha256": sha, "policy": POLICY,
            "protected": sorted(n for n in exported_names if n in prot)}

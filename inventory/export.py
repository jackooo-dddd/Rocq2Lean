"""Export every enumerated declaration of a family as roots, through the public CLI
(`rocq2lean export`): elaborated types and bodies, body states, universes, kinds, projections and
type/body dependencies of the whole closure, with Rocq2Lean's independent round trip.
Resumable: a family whose export exists for the same roots digest is not redone.

    python3 -I inventory/export.py modern|classic
"""
import hashlib
import json
import os
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CFG = json.loads((ROOT / "inventory" / "config.json").read_text())
W = ROOT / ".work" / "inventory"
X = lambda p: Path(os.path.expanduser(p)) if p.startswith("~") else ROOT / p


def main(fam):
    mods = json.loads((W / "modules.json").read_text())["modules"]
    sel = {m: v for m, v in mods.items() if v["family"] == fam}
    roots = sorted({n.split("#")[0] for v in sel.values() for kind, n in v["entries"]})
    digest = hashlib.sha256("\n".join(roots).encode()).hexdigest()
    run = W / f"export-{fam}"
    stamp = run / "ROOTS.sha256"
    if stamp.exists() and stamp.read_text().strip() == digest and (run / "source.ndjson").exists():
        print(f"{fam}: export current ({len(roots)} roots)")
        return
    mw, cb = X(CFG["modern"]["working"]), X(CFG["classic"]["working"])
    lp = [["-R", str(mw), "prosa"], ["-R", str(ROOT / ".work" / "coqeal-ce3d1d6"), "CoqEAL"]]
    if fam == "classic":
        lp += [["-R", str(cb / "classic"), "prosa.classic"], ["-Q", str(cb / "compat"), "Compat"]]
    man = W / f"manifest-{fam}.json"
    man.write_text(json.dumps({"name": f"inventory-{fam}", "load_paths": lp, "files": [],
                               "requires": sorted(sel)}, indent=1) + "\n")
    (W / f"roots-{fam}.txt").write_text("\n".join(roots) + "\n")
    # the CLI's export function, in-process (thousands of roots exceed the command-line limit);
    # the same code path as `rocq2lean export`, with its round trip and contract
    sys.path.insert(0, str(ROOT / "tools"))
    import rocq2lean
    rc, msg = 0, "ok"
    try:
        rocq2lean.export(str(man), roots, str(run))
    except rocq2lean.Rejected as e:
        rc, msg = 2, f"{e.args}"
    (W / f"export-{fam}.log").write_text(msg + "\n")
    if rc == 0:
        stamp.write_text(digest + "\n")
    print(f"{fam}: export exit {rc}, {len(roots)} roots; {msg[-400:]}")
    sys.exit(rc)


if __name__ == "__main__":
    main(sys.argv[1])

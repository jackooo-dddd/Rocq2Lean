"""Fresh holdouts for M6 completion, chosen deterministically AFTER the freeze tag (argument) and
committed before they are run once on the frozen implementation.

Pool: Prosa util modules whose proofs use lia (prosa.util.sum, div_mod, list) and MathComp
mathcomp.boot.div; never requested as roots during development (every fixed regression request in
fixtures/m6/regression and every earlier selection is excluded). Within a module, lemmas are
ordered by the sha256 of their full name and the first N are taken: reproducible, and not steerable
towards what is known to translate.

    python3 -I tests/m6/select_completion_holdouts.py <freeze-tag>
"""
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
TAG = sys.argv[1]
head = subprocess.run(["git", "-C", str(ROOT), "rev-parse", "HEAD"], capture_output=True, text=True).stdout.strip()
tagc = subprocess.run(["git", "-C", str(ROOT), "rev-parse", TAG + "^{commit}"], capture_output=True, text=True).stdout.strip()
assert tagc, f"no tag {TAG}"
LIB = subprocess.run(["opam", "var", "--switch=rocq930-mc", "lib"], capture_output=True, text=True).stdout.strip()
PROSA = ROOT / ".work" / "prosa-0.6-rocq93"
POOL = [("prosa.util.sum", PROSA / "util" / "sum.v", 6), ("prosa.util.div_mod", PROSA / "util" / "div_mod.v", 6),
        ("prosa.util.list", PROSA / "util" / "list.v", 6),
        ("mathcomp.boot.div", Path(LIB) / "coq" / "user-contrib" / "mathcomp" / "boot" / "div.v", 8)]
seen = set()
for f in (ROOT / "fixtures" / "m6" / "regression").glob("*.json"):
    seen |= set(json.loads(f.read_text())["roots"])
for f in (ROOT / "reports" / "m6").glob("*selection*.json"):
    for v in json.loads(f.read_text()).values():
        if isinstance(v, list):
            seen |= {x for x in v if isinstance(x, str)}
DECL = re.compile(r"^\s*(?:Lemma|Theorem|Corollary|Fact)\s+([A-Za-z_][A-Za-z0-9_']*)", re.M)
chosen = {}
for mod, path, n in POOL:
    names = [f"{mod}.{m}" for m in DECL.findall(path.read_text())]
    names = [x for x in dict.fromkeys(names) if x not in seen]
    chosen[mod] = sorted(names, key=lambda x: hashlib.sha256(x.encode()).hexdigest())[:n]
sel = {"freeze": TAG, "freeze_commit": tagc, "selected_at": head, "chosen_after_freeze": True,
       "method": "per module, never-requested lemmas ordered by sha256(full name), first N",
       "prosa_util": chosen["prosa.util.sum"] + chosen["prosa.util.div_mod"] + chosen["prosa.util.list"],
       "mathcomp_div": chosen["mathcomp.boot.div"]}
(ROOT / "reports" / "m6" / "holdout_completion_selection.json").write_text(json.dumps(sel, indent=1) + "\n")
reg = ROOT / "fixtures" / "m6" / "regression"
(ROOT / "fixtures" / "m6" / "holdout_util_manifest.json").write_text(json.dumps(
    {"name": "m6-holdout-util", "load_paths": [["-R", "../../.work/prosa-0.6-rocq93", "prosa"]], "files": [],
     "requires": ["prosa.util.sum", "prosa.util.div_mod", "prosa.util.list"]}) + "\n")
(ROOT / "fixtures" / "m6" / "mathcomp_div_manifest.json").write_text(json.dumps(
    {"name": "m6-mathcomp-div", "load_paths": [], "files": [], "requires": ["mathcomp.boot.div"]}) + "\n")
(reg / "holdout_completion_prosa.json").write_text(json.dumps(
    {"name": "holdout_completion_prosa", "manifest": "fixtures/m6/holdout_util_manifest.json", "roots": sel["prosa_util"]}, indent=1) + "\n")
(reg / "holdout_completion_mathcomp.json").write_text(json.dumps(
    {"name": "holdout_completion_mathcomp", "manifest": "fixtures/m6/mathcomp_div_manifest.json", "roots": sel["mathcomp_div"]}, indent=1) + "\n")
print(json.dumps(sel, indent=1))

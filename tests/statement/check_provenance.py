#!/usr/bin/env python3
"""Corpus provenance (inventory/statement_provenance.py, reports/statement_only/PROVENANCE.md).

1. The corpus manifest checks: every bound chunk IR, snapshot, round trip, the union universe check and
   the run's files are present and unchanged; the merge re-derives from the chunk IRs.
2. Negative controls on forged copies of the manifest (the evidence itself is never modified):
   a chunk IR replaced by an altered copy; a round trip missing; a merged record altered (manifest
   forged to bind the altered IR, so only the merge re-derivation can catch it); the union check
   missing. Each must be rejected.

Writes reports/statement_only/test_provenance.json.
"""
import json
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from lib import ROOT, check, finish  # noqa: E402

sys.path.insert(0, str(ROOT / "inventory"))
import statement_provenance as P  # noqa: E402

OUT = {}
M = ROOT / "reports" / "statement_only" / "provenance" / "CORPUS_MANIFEST.json"
m = json.loads(M.read_text())
res = P.check(M)
OUT["manifest_check"] = res
check(res["status"] == "OK", "corpus manifest: all bound evidence present and unchanged; merge re-derived")

tmp = Path(tempfile.mkdtemp(prefix="r2l-prov-"))


def forged(name, f):
    m2 = json.loads(json.dumps(m))
    f(m2)
    p = tmp / f"{name}.json"
    p.write_text(json.dumps(m2))
    r = P.check(p)
    OUT[name] = r
    return r


# a chunk IR altered (a copy; the bound digest no longer matches)
c0 = sorted(m["chunks"])[0]
alt = tmp / "altered_chunk.ndjson"
txt = Path(m["chunks"][c0]["ir"]).read_text()
alt.write_text(txt.replace('"kind":"constant"', '"kind":"constant" ', 1))
r = forged("altered_chunk_ir", lambda x: x["chunks"][c0].__setitem__("ir", str(alt)))
check(r["status"] == "PROVENANCE_REJECTED" and any("altered" in p for p in r["problems"]), "an altered chunk IR is rejected")

# a round trip missing
r = forged("missing_roundtrip", lambda x: x["chunks"][c0].__setitem__("roundtrip", str(tmp / "nowhere.json")))
check(r["status"] == "PROVENANCE_REJECTED" and any("missing" in p for p in r["problems"]), "a missing round trip is rejected")

# a merged record altered, with a forged manifest binding the altered merged IR
run2 = tmp / "run"
run2.mkdir()
src = Path(m["files"]["source.ndjson"]["path"])
lines = src.read_text().splitlines(keepends=True)
for i, l in enumerate(lines):
    if i > 5 and l.startswith('{"kind":"constant"') and '"body_state":"transparent"' in l:
        lines[i] = l.replace('"body_state":"transparent"', '"body_state":"transparent" ', 1)
        break
(run2 / "source.ndjson").write_text("".join(lines))


def forge_merge(x):
    x["run"] = str(run2)
    x["files"] = {"source.ndjson": {"path": str(run2 / "source.ndjson"), "sha256": P.sha(run2 / "source.ndjson")}}


r = forged("altered_merged_record", forge_merge)
check(r["status"] == "PROVENANCE_REJECTED" and any("merged record is not a chunk copy" in p for p in r["problems"]),
      "an altered merged record is rejected by the merge re-derivation, even under a forged manifest")

# the union universe check missing
r = forged("missing_union", lambda x: x["union_universes"].__setitem__("file", str(tmp / "nounion.json")))
check(r["status"] == "PROVENANCE_REJECTED", "a missing union universe check is rejected")

shutil.rmtree(tmp, ignore_errors=True)
(ROOT / "reports" / "statement_only" / "test_provenance.json").write_text(json.dumps(OUT, indent=1) + "\n")
finish("test-provenance")

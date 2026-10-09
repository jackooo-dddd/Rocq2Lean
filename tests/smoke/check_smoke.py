"""Smoke: fixed toolchains, checked kernel path, id_nat success and missing-body rejection."""
import json
import os
import shutil
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from lib import ROOT, check, cli, results, finish  # noqa: E402

rc, out = cli("doctor")
check(rc == 0, "doctor: Lean v4.33.1 and Rocq 9.3.0 match toolchains.lock.json")
env = dict(os.environ, PATH=f"{Path.home()}/.elan/bin:" + os.environ["PATH"])
p = subprocess.run(["lake", "-d", str(ROOT), "build", "Smoke"], capture_output=True, text=True, env=env)
check(p.returncode == 0 and "SMOKE_KERNEL_PATH_OK" in p.stdout + p.stderr,
      "checked insertion path accepts True.intro and rejects Nat.zero : False")

run = ROOT / "runs" / "smoke-idnat"
shutil.rmtree(run, ignore_errors=True)
man = ROOT / "fixtures" / "bootstrap" / "manifest.json"
rc, _ = cli("export", "--manifest", man, "--roots", "Fixtures.IdNat.id_nat_correct", "--out", run)
check(rc == 0, "id_nat export (MetaRocq frontend, round trip)")
rc, _ = cli("translate", "--input", run / "source.ndjson", "--out", run)
R, rep = results(run)
check(rc == 0 and R["Fixtures.IdNat.id_nat_correct"]["target_kind"] == "theorem",
      "id_nat_correct: original Qed proof translated and kernel-checked")
rc, _ = cli("verify", "--run", run)
check(rc == 0, "id_nat run VERIFIED")

# Delete the exported theorem body: must be rejected, never axiomatised.
neg = ROOT / "runs" / "smoke-idnat-nobody"
shutil.rmtree(neg, ignore_errors=True)
neg.mkdir(parents=True)
lines = [json.loads(l) for l in open(run / "source.ndjson")]
for d in lines:
    if d.get("name") == "Fixtures.IdNat.id_nat_correct":
        d["body"] = None
        d["body_state"] = "unavailable"
(neg / "source.ndjson").write_text("".join(json.dumps(d) + "\n" for d in lines))
rc, out = cli("translate", "--input", neg / "source.ndjson", "--out", neg)
R, rep = results(neg)
check(rc != 0 and R["Fixtures.IdNat.id_nat_correct"]["status"] == "BLOCKED_SOURCE_BODY",
      "deleted body rejected as BLOCKED_SOURCE_BODY (non-zero exit)")
check(not (neg / "lean" / "Rocq2LeanOut.olean").exists(), "no module produced for the rejected input")
finish("test-smoke")

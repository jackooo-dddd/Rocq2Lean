"""Artifact binding and stale-success invalidation (hardening P0)."""
import fcntl
import json
import os
import shutil
import signal
import subprocess
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from lib import CLI, ROOT, check, cli, finish  # noqa: E402

MAN = ROOT / "fixtures" / "m3" / "manifest.json"
BASE = ROOT / "runs" / "ai-base"


def fresh():
    shutil.rmtree(BASE, ignore_errors=True)
    assert cli("export", "--manifest", MAN, "--roots", "M3.M3Fix.addR_RS,M3.M3Proofs.mirror_mirror", "--out", BASE)[0] == 0
    assert cli("translate", "--input", BASE / "source.ndjson", "--out", BASE)[0] == 0
    rc, _ = cli("verify", "--run", BASE)
    assert rc == 0
    return json.loads((BASE / "verify.json").read_text())


def status():
    p = BASE / "verify.json"
    return json.loads(p.read_text())["status"] if p.exists() else "ABSENT"


def tamper_case(name, mutate, needle, restore=None):
    v = fresh()
    check(v["status"] == "VERIFIED", f"[{name}] positive control VERIFIED")
    mutate()
    try:
        rc, out = cli("verify", "--run", BASE)
    finally:
        if restore:
            restore()
    st = status()
    check(rc != 0 and st != "VERIFIED" and needle in out,
          f"[{name}] rejected, verify.json now {st}, reason contains '{needle}'" + ("" if needle in out else f" — {out[-250:]}"))


def append(path, data=b"\n"):
    with open(path, "ab") as f:
        f.write(data)


# Success followed by failure in the same directory: the old VERIFIED must not survive.
tamper_case("same-dir-failure", lambda: append(BASE / "lean" / "Rocq2LeanOut.olean"), "module_olean changed")
tamper_case("ir-changed-same-path", lambda: append(BASE / "source.ndjson"), "source IR changed since export")
tamper_case("report-changed", lambda: append(BASE / "translation_report.json"), "translation_report changed")
tamper_case("module-source-changed", lambda: append(BASE / "lean" / "Rocq2LeanOut.lean", b"-- edited\n"), "module_lean changed")
man_bytes = MAN.read_bytes()
tamper_case("manifest-changed", lambda: append(MAN, b" "), "source manifest changed", lambda: MAN.write_bytes(man_bytes))


def edit_request():
    c = json.loads((BASE / "contract.json").read_text())
    c["request"] = c["request"][:1]
    (BASE / "contract.json").write_text(json.dumps(c))
tamper_case("request-changed", edit_request, "coverage contract changed since export")
tamper_case("roundtrip-missing", lambda: (BASE / "roundtrip.json").unlink(), "missing round-trip result")


def roundtrip_flip():
    r = json.loads((BASE / "roundtrip.json").read_text()); r["status"] = "OK "
    (BASE / "roundtrip.json").write_text(json.dumps(r))
tamper_case("roundtrip-altered", roundtrip_flip, "source round trip not verified or changed")
victim = ROOT / "tools" / "preflight.py"
vb = victim.read_bytes()
tamper_case("implementation-changed", lambda: append(victim, b"# temporary edit\n"), "impl_tree changed",
            lambda: victim.write_bytes(vb))



# Toolchain binding: the snapshot / translation manifest record content digests of the Lean, Rocq and
# MetaRocq binaries; a run exported or translated under different binaries does not verify.
def forge_toolchain(fname, key):
    def f():
        d = json.loads((BASE / fname).read_text())
        if key == "toolchain_fingerprint":
            d[key]["digest"] = "0" * 64
        else:
            d[key] = "0" * 64
        (BASE / fname).write_text(json.dumps(d))
    return f
tamper_case("toolchain-at-export", forge_toolchain("source_snapshot.json", "toolchain_fingerprint"),
            "toolchain binaries (Lean, Rocq, MetaRocq) changed since export")
tamper_case("toolchain-at-translation", forge_toolchain("translation_manifest.json", "toolchain_sha256"),
            "toolchain changed since translation")
v = fresh()
fp = v.get("toolchain_fingerprint", {})
check(fp.get("files", 0) > 4 and {"lean:bin/lean", "lean:lib/lean/libleanshared.so", "rocq:bin/rocq"} <= set(fp.get("components", {}))
      and v["bound_sha256"].get("toolchain") == fp.get("digest"),
      f"verify.json binds the toolchain fingerprint ({fp.get('files')} files incl. lean, libleanshared, rocq, MetaRocq)")


# `status`: a VERIFIED result is reported current only while every bound digest is unchanged.
def st_cli():
    rc, out = cli("status", "--run", BASE)
    return rc, out
rc, out = st_cli()
check(rc == 0 and "VERIFIED_CURRENT" in out, "status: fresh VERIFIED run is VERIFIED_CURRENT (exit 0)")
src = ROOT / "fixtures" / "m3" / "M3Fix.v"
sb = src.read_bytes()
try:
    append(src, b"(* edited after verification *)\n")
    rc, out = st_cli()
    check(rc == 2 and "STALE" in out and "src:" in out, "status: source edited after verification -> STALE (exit 2), names the file")
    check(status() == "VERIFIED", "status is read-only (verify.json untouched)")
finally:
    src.write_bytes(sb)
rc, out = st_cli()
check(rc == 0 and "VERIFIED_CURRENT" in out, "status: restoring the exact source makes the result current again")
ob = (BASE / "lean" / "Rocq2LeanOut.olean").read_bytes()
append(BASE / "lean" / "Rocq2LeanOut.olean")
rc, out = st_cli()
check(rc == 2 and "module_olean" in out, "status: generated module changed -> STALE")
(BASE / "lean" / "Rocq2LeanOut.olean").write_bytes(ob)
(BASE / "translation_report.json").unlink()
rc, out = st_cli()
check(rc == 2 and "STALE" in out, "status: a bound artifact deleted -> STALE")
rc, out = cli("verify", "--run", BASE)
rc, out = st_cli()
check(rc == 2 and "NOT_VERIFIED" in out, "status after a failed re-verification: NOT_VERIFIED (exit 2)")

# Re-translation invalidates a previous success before it starts.
fresh()
p = subprocess.Popen(CLI + ["translate", "--input", str(BASE / "source.ndjson"), "--out", str(BASE)],
                     stdout=subprocess.PIPE, stderr=subprocess.PIPE)
time.sleep(1.5)
during = status()
p.wait()
check(during == "ABSENT", f"translate removes the previous verify.json when it starts (saw {during})")
check(status() == "ABSENT", "after re-translation no verify.json exists until a new verification")

# Interrupted verification never publishes success.
rc, _ = cli("verify", "--run", BASE)
assert rc == 0
p = subprocess.Popen(CLI + ["verify", "--run", str(BASE)], stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                     start_new_session=True)
deadline = time.time() + 60
while time.time() < deadline and status() != "ABSENT":      # verification has started
    time.sleep(0.02)
started = status() == "ABSENT"
while time.time() < deadline and not (BASE / "lean" / "Rocq2LeanConsumer.lean").exists():
    time.sleep(0.02)                                          # ... and reached the consumer
time.sleep(0.5)
os.killpg(p.pid, signal.SIGKILL)
p.wait()
check(started and status() == "ABSENT",
      f"verification killed mid-run (during the consumer) leaves no success (verify.json {status()})")
# Killed at the very start, before the toolchain check.
p = subprocess.Popen(CLI + ["verify", "--run", str(BASE)], stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                     start_new_session=True)
while time.time() < deadline + 60 and not (BASE / ".rocq2lean.lock").exists():
    time.sleep(0.01)
time.sleep(0.2)
os.killpg(p.pid, signal.SIGKILL)
p.wait()
check(status() != "VERIFIED", f"verification killed at its start leaves no success (verify.json {status()})")
check(not list(BASE.glob(".verify.json.*.tmp")) or status() != "VERIFIED", "no partial publication counted as success")

# Concurrent writer is rejected, not interleaved.
lockf = open(BASE / ".rocq2lean.lock", "w")
fcntl.flock(lockf, fcntl.LOCK_EX | fcntl.LOCK_NB)
rc, out = cli("verify", "--run", BASE)
lockf.close()
check(rc != 0 and "RUN_BUSY" in out, "a second writer on the same run is rejected (RUN_BUSY)")
rc, _ = cli("verify", "--run", BASE)
check(rc == 0 and status() == "VERIFIED", "positive control: verification succeeds once the run is free")
finish("test-artifact-integrity")

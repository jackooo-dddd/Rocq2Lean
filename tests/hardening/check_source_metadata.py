"""M1 source metadata (hardening P1): mutations of metadata only (no term bodies) must be caught by
the independent round trip, each by its specific check."""
import copy
import json
import os
import shutil
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from lib import ROOT, check, cli, finish, SWITCH  # noqa: E402

MAN = ROOT / "fixtures" / "m1" / "manifest.json"
RUN = ROOT / "runs" / "hm-meta"
shutil.rmtree(RUN, ignore_errors=True)
rc, _ = cli("export", "--manifest", MAN, "--roots", "M1.M1Chain.chain_qed,M1.M1Base.two_eq,M1.M1Base.three_opaque", "--out", RUN)
check(rc == 0, "positive control: M1 export with full round trip (bodies, metadata, universes) OK")
BASE = [json.loads(l) for l in open(RUN / "source.ndjson")]
env = dict(os.environ, PATH=f"{Path.home()}/.local/bin:" + os.environ["PATH"])


def roundtrip(name, mutate):
    lines = copy.deepcopy(BASE)
    mutate({d["name"]: d for d in lines if d.get("kind") in ("constant", "inductive")}, lines)
    d = RUN / f"mut-{name}"
    shutil.rmtree(d, ignore_errors=True)
    d.mkdir()
    (d / "source.ndjson").write_text("".join(json.dumps(x) + "\n" for x in lines))
    p = subprocess.run(["opam", "exec", "--switch=" + SWITCH, "--", sys.executable, "-I", str(ROOT / "tools" / "roundtrip.py"),
                        str(d / "source.ndjson"), str(d), "-Q", str(MAN.parent), "M1", "--", "M1.M1Chain", "M1.M1Base"],
                       capture_output=True, text=True, env=env)
    return p.returncode, json.loads((d / "roundtrip.json").read_text())["problems"]


def expect(name, mutate, needle):
    rc, probs = roundtrip(name, mutate)
    hit = any(needle in x for x in probs)
    check(rc != 0 and hit, f"metadata mutation '{name}' caught ({needle})" + ("" if hit else f" — got {probs[:3]}"))


rc, probs = roundtrip("unmutated", lambda D, L: None)
check(rc == 0 and not probs, "unmutated copy passes the round trip (positive control)")
expect("typing-flag", lambda D, L: D["M1.M1Base.two"]["native"]["typing_flags"].update(check_guarded=False),
       "M1.M1Base.two: native metadata differs in ['typing_flags']")
expect("template-flag", lambda D, L: D["Corelib.Init.Logic.eq"]["native"].update(template=False),
       "Corelib.Init.Logic.eq: native metadata differs in ['template']")
expect("private-universes", lambda D, L: D["M1.M1Base.two_eq_qed"]["native"].update(private_universes="polymorphic_private"),
       "native metadata differs in ['private_universes']")
expect("body-kind", lambda D, L: D["M1.M1Base.three_opaque"]["native"].update(body_kind="transparent"),
       "native metadata differs in ['body_kind']")
expect("body-state", lambda D, L: D["M1.M1Base.three_opaque"].update(body_state="transparent"), "RT_OPACITY_MISMATCH")
expect("dependency-edges", lambda D, L: D["M1.M1Chain.chain_qed"]["deps"].update(body=[]),
       "exported dependency edges differ")
expect("universe-record", lambda D, L: L[3]["constraints"].append(
    {"l": {"k": "global", "n": "Corelib.Init.Logic.19"}, "rel": {"k": "le", "offset": 1}, "r": {"k": "set"}}),
       "is not entailed by the native facts")
expect("polymorphic-flag", lambda D, L: D["M1.M1Base.two"]["native"].update(polymorphic=True),
       "native metadata differs in ['polymorphic']")
finish("test-source-metadata")

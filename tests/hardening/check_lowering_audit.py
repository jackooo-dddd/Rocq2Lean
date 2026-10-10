"""Case/Fix fidelity (hardening P1): targeted target-term mutations, each classified by real kernel
replay (tools/replay.py) and by the independent audit."""
import copy
import json
import shutil
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "tools"))
from lib import ROOT, audit_report, check, cli, finish, forge_run  # noqa: E402
import replay  # noqa: E402

M3 = ROOT / "fixtures" / "m3" / "manifest.json"
LOW = ROOT / "fixtures" / "lowering" / "manifest.json"
CLASS = []


def pipeline(name, man, roots):
    run = ROOT / "runs" / name
    shutil.rmtree(run, ignore_errors=True)
    rcs = [cli("export", "--manifest", man, "--roots", ",".join(roots), "--out", run)[0],
           cli("translate", "--input", run / "source.ndjson", "--out", run)[0], cli("verify", "--run", run)[0]]
    check(rcs == [0, 0, 0], f"{name}: positive control VERIFIED")
    return run


def recapps(e, out=None, path=()):
    """All recursor applications (head const ending in .rec) with their spines, in order."""
    out = [] if out is None else out
    if isinstance(e, dict):
        if e.get("k") == "app":
            spine, h = [], e
            while h["k"] == "app":
                spine.append(h)
                h = h["f"]
            if h["k"] == "const" and h["n"].endswith(".rec"):
                out.append((h, list(reversed([x["a"] for x in spine])), list(reversed(spine))))
        for v in e.values():
            recapps(v, out)
    elif isinstance(e, list):
        for v in e:
            recapps(v, out)
    return out


def classify(run, name, decl, mutate, expect):
    rep = json.loads((run / "translation_report.json").read_text())
    r = next(x for x in rep["results"] if x["source"] == decl)
    before = json.dumps(r["target_value"])
    mutate(r["target_value"])
    assert json.dumps(r["target_value"]) != before, f"mutation {name} did not change anything"
    d = run / f"mut-{name}"
    shutil.rmtree(d, ignore_errors=True)
    d.mkdir()
    (d / "report.json").write_text(json.dumps(rep))
    kern = next(x for x in replay.replay(d / "report.json", d) if x["source"] == decl)["kernel"]
    rc, probs = audit_report(run, rep, f"mut-{name}")
    dets = sorted({p["detector"] for p in probs})
    if kern == "REJECTED":
        got = "kernel rejection" + (" + audit" if rc else "")
    elif rc:
        got = "audit rejection (type-correct mutation)"
    else:
        got = "intentionally equivalent"
    CLASS.append({"mutation": name, "declaration": decl, "kernel": kern, "audit_exit": rc, "detectors": dets,
                  "classification": got})
    check(got.startswith(expect), f"{name}: {got} (kernel {kern}, audit detectors {dets}); expected {expect}")


def arg_of(app_nodes, i):
    return app_nodes[i]


m3b = pipeline("hl-m3b", M3, ["M3.M3Case.vid_cons", "M3.M3Case.pred_r_RS", "M3.M3Case.vtail_cons"])
m3c = pipeline("hl-m3c", M3, ["M3.M3Fix.mirrorR_node", "M3.M3Fix.addR_RS", "M3.M3Fix.vmap_cons"])
low = pipeline("hl-low", LOW, ["L.Lower.swapacc_RS"])


def first_rec(v):
    return recapps(v)[0]


# 1. Recursive-result order (type-correct): in mirrorR's Node branch (fields l x r, results ihl ihr),
#    the body Node ihr x ihl becomes Node ihl x ihr — only inside that branch.
def swap_results(v):
    h, args, nodes = first_rec(v)
    m = nodes[3]["a"]                    # Tree.rec: A (0), motive (1), Leaf minor (2), Node minor (3)
    for _ in range(5):
        m = m["b"]
    s = json.dumps(m)
    s = s.replace('{"k": "bvar", "i": 0}', "@@").replace('{"k": "bvar", "i": 1}', '{"k": "bvar", "i": 0}').replace("@@", '{"k": "bvar", "i": 1}')
    m.clear(); m.update(json.loads(s))
classify(m3c, "recursive-result-order", "M3.M3Fix.mirrorR", swap_results, "audit rejection")


# 2. Trailing-argument order (type-correct): swapacc's outer application rec ... x a b -> ... x b a.
def swap_trailing(v):
    h, args, nodes = first_rec(v)
    a, b = nodes[-2]["a"], nodes[-1]["a"]
    nodes[-2]["a"], nodes[-1]["a"] = b, a
classify(low, "trailing-argument-order", "L.Lower.swapacc", swap_trailing, "audit rejection")


# 3. Motive content (case): vid's motive body replaced.
def motive_body(v):
    h, args, nodes = first_rec(v)
    mot = nodes[1]["a"]           # Vec.rec params: A ; motive is argument 1
    m = mot
    while m["b"]["k"] == "lam":
        m = m["b"]
    m["b"] = {"k": "const", "n": "Rocq.M3.M3Types.RNat", "u": []}
classify(m3b, "case-motive-content", "M3.M3Case.vid", motive_body, "kernel rejection")


# 4. Index argument (case): beta-equivalent spelling is an intentional equivalence ...
def index_beta(v):
    h, args, nodes = first_rec(v)
    i = len(nodes) - 2            # ... idx major : the index is just before the major premise
    nodes[i]["a"] = {"k": "app", "f": {"k": "lam", "n": "x", "t": {"k": "const", "n": "Nat", "u": []},
                                       "b": {"k": "bvar", "i": 0}}, "a": nodes[i]["a"]}
classify(m3b, "case-index-beta-equivalent", "M3.M3Case.vid", index_beta, "intentionally equivalent")


# ... while a different index is rejected.
def index_wrong(v):
    h, args, nodes = first_rec(v)
    i = len(nodes) - 2
    nodes[i]["a"] = {"k": "app", "f": {"k": "const", "n": "Nat.succ", "u": []}, "a": nodes[i]["a"]}
classify(m3b, "case-index-different", "M3.M3Case.vid", index_wrong, "kernel rejection")


# 5. Relevant binder type in a minor: a beta-equivalent spelling is equivalent, a different type is not.
def minor_binder(newt):
    def f(v):
        h, args, nodes = first_rec(v)
        minor = nodes[2]["a"]     # RNat.rec (no parameters): motive (0), RZ minor (1), RS minor (2)
        minor["t"] = newt(minor["t"])
    return f
classify(m3c, "minor-binder-beta-equivalent", "M3.M3Fix.addR",
         minor_binder(lambda t: {"k": "app", "f": {"k": "lam", "n": "T", "t": {"k": "sort", "l": {"k": "succ", "l": {"k": "zero"}}},
                                                   "b": {"k": "bvar", "i": 0}}, "a": t}), "intentionally equivalent")
classify(m3c, "minor-binder-different-type", "M3.M3Fix.addR",
         minor_binder(lambda t: {"k": "const", "n": "Nat", "u": []}), "kernel rejection")


# 6. Recursor selection: RNat.rec replaced by Nat.rec.
def other_rec(v):
    h, args, nodes = first_rec(v)
    h["n"] = "Nat.rec"
classify(m3c, "recursor-selection", "M3.M3Fix.addR", other_rec, "kernel rejection")


# 7. Fix index argument passed to the recursor (vmap over Vec A n).
def fix_index(v):
    h, args, nodes = first_rec(v)
    i = len(nodes) - 2
    nodes[i]["a"] = {"k": "app", "f": {"k": "const", "n": "Nat.succ", "u": []}, "a": nodes[i]["a"]}
classify(m3c, "fix-index-different", "M3.M3Fix.vmap", fix_index, "kernel rejection")
# 8. Erased cast annotations (source side): the translator validates every kernel cast's annotation
#    (isDefEq) before erasing it. A non-convertible annotation is rejected; a convertible
#    re-spelling is an intentional equivalence (the cast carries no term content).
from lib import results  # noqa: E402
m2 = pipeline("hl-m2", ROOT / "fixtures" / "m2" / "manifest.json", ["M2.M2A.vm_proof"])
src = [json.loads(l) for l in open(m2 / "source.ndjson")]


def find_cast(t):
    if isinstance(t, dict):
        if t.get("k") == "cast":
            return t
        for v in t.values():
            c = find_cast(v)
            if c:
                return c
    elif isinstance(t, list):
        for v in t:
            c = find_cast(v)
            if c:
                return c
    return None


for name, ann, expect in (("cast-annotation-wrong", lambda ty: {"k": "ind", "ind": {"mind": "Corelib.Init.Datatypes.nat", "i": 0}, "u": []},
                           "TRANSLATION_FAILED"),
                          ("cast-annotation-convertible", lambda ty: ty, "TRANSLATED_AND_CHECKED")):
    lines = copy.deepcopy(src)
    d = next(x for x in lines if x.get("name") == "M2.M2A.vm_proof")
    c = find_cast(d["body"])
    c["ty"] = ann(c["ty"])
    c["kind"] = "default" if name.endswith("convertible") else c["kind"]
    run = ROOT / "runs" / f"hl-{name}"
    shutil.rmtree(run, ignore_errors=True)
    run.mkdir()
    (run / "source.ndjson").write_text("".join(json.dumps(x) + "\n" for x in lines))
    rc, _ = cli("translate", "--input", run / "source.ndjson", "--out", run)
    st = results(run)[0]["M2.M2A.vm_proof"]["status"]
    CLASS.append({"mutation": name, "declaration": "M2.M2A.vm_proof", "translator": st,
                  "classification": "translator rejection" if st != "TRANSLATED_AND_CHECKED" else "intentionally equivalent"})
    check(st == expect, f"{name}: translator status {st} (expected {expect})")

# 9. Further type-correct mutations (kernel-accepted, so only the audit can reject them).
m3x = pipeline("hl-m3x", M3, ["M3.M3Case.pred_r_RS", "M3.M3Fix.addR_RS", "M3.M3Fix.addAcc_RS"])
low2 = pipeline("hl-low2", LOW, ["L.Lower.neg2_T2", "L.Lower.swapacc_RS"])


def under_lams(e, n):
    for _ in range(n):
        e = e["b"]
    return e


def swap_minors(v):                      # neg2: B2.rec motive F2 T2 b  ->  B2.rec motive T2 F2 b
    h, args, nodes = first_rec(v)
    nodes[1]["a"], nodes[2]["a"] = nodes[2]["a"], nodes[1]["a"]


def case_uses_ih(v):                     # pred_r: RS minor  λ m ih. m  ->  λ m ih. ih  (a match must ignore ih)
    h, args, nodes = first_rec(v)
    body = under_lams(nodes[2]["a"], 1)
    body["b"] = {"k": "bvar", "i": 0}


def swap_major_trailing(v):              # addR: RNat.rec motive mz ms n m  ->  ... m n  (recursion on m)
    h, args, nodes = first_rec(v)
    nodes[-2]["a"], nodes[-1]["a"] = nodes[-1]["a"], nodes[-2]["a"]


def rec_call_argument(v):                # addAcc: ih (RS m)  ->  ih m  in the RS minor
    h, args, nodes = first_rec(v)
    body = under_lams(nodes[2]["a"], 3)  # λ p ih m. ih (RS m)
    assert body["k"] == "app" and body["f"] == {"k": "bvar", "i": 1}, body
    body["a"] = {"k": "bvar", "i": 0}


NEW = [(low2, "case-minor-swap", "L.Lower.neg2", swap_minors),
       (m3x, "case-uses-recursive-result", "M3.M3Case.pred_r", case_uses_ih),
       (m3x, "fix-major-premise-swap", "M3.M3Fix.addR", swap_major_trailing),
       (m3x, "fix-recursive-call-argument", "M3.M3Fix.addAcc", rec_call_argument)]
for run, name, decl, mut in NEW:
    classify(run, name, decl, mut, "audit rejection")

# The same type-correct mutations through the full public pipeline: a synchronized forged run (the
# generated module is rebuilt from the mutated report through the kernel) must not verify.
# (a) Roots are the mutated definitions themselves: every forged declaration is kernel-accepted and
#     the consumer's readback agrees with the report, so the rejection must come from the audit.
defs_m3 = pipeline("hl-defs", M3, ["M3.M3Case.pred_r", "M3.M3Fix.addR", "M3.M3Fix.addAcc"])
defs_low = pipeline("hl-defs-low", LOW, ["L.Lower.neg2"])
E2E = {"case-minor-swap": defs_low, "case-uses-recursive-result": defs_m3, "fix-major-premise-swap": defs_m3,
       "fix-recursive-call-argument": defs_m3}
for run0, name, decl, mut in NEW:
    run = E2E[name]
    rep = json.loads((run / "translation_report.json").read_text())
    mut(next(x for x in rep["results"] if x["source"] == decl)["target_value"])
    d, kernel_ok, rc, cons, aud = forge_run(run, name, rep)
    v = json.loads((d / "verify.json").read_text())
    struct = [p["message"] for p in aud.get("problems", []) if p["detector"] == "structure" and p["message"].startswith(decl + ":")]
    check(kernel_ok and cons.get("status") == "OK" and rc == 2 and v["status"] == "AUDIT_REJECTED" and struct,
          f"e2e {name}: forged module kernel-accepted, consumer OK, verify rejects via the structural audit of {decl}"
          + ("" if struct else f" — kernel_ok={kernel_ok} consumer={cons.get('status')} rc={rc} {aud.get('problems', [])[:2]}"))
    CLASS.append({"mutation": name + " (e2e, definition root)", "declaration": decl, "kernel": "ACCEPTED" if kernel_ok else "REJECTED",
                  "consumer": cons.get("status"), "verify_exit": rc, "classification": "audit rejection through verify" if struct else "?"})
# (b) Roots are the original computation lemmas (proved by reflexivity): the changed computation
#     makes a dependent proof ill typed, so the kernel itself rejects the forged module.
for run, name, decl, mut in NEW:
    rep = json.loads((run / "translation_report.json").read_text())
    mut(next(x for x in rep["results"] if x["source"] == decl)["target_value"])
    d, kernel_ok, rc, cons, aud = forge_run(run, name + "-lemma", rep)
    check(not kernel_ok and rc == 2, f"e2e {name} under its computation lemma: a dependent reflexivity proof is kernel-rejected; verify exit {rc}")
    CLASS.append({"mutation": name + " (e2e, lemma root)", "declaration": decl, "kernel": "dependent proof REJECTED",
                  "verify_exit": rc, "classification": "kernel rejection (through a dependent proof)"})
# Positive control for the e2e path: an unmutated synchronized forged run verifies.
d, kernel_ok, rc, cons, aud = forge_run(defs_m3, "unmutated", json.loads((defs_m3 / "translation_report.json").read_text()))
check(kernel_ok and rc == 0, "e2e positive control: unmutated synchronized forged run VERIFIED")

(ROOT / "reports" / "hardening").mkdir(parents=True, exist_ok=True)
(ROOT / "reports" / "hardening" / "lowering_mutations.json").write_text(json.dumps(CLASS, indent=2) + "\n")
finish("test-lowering-audit")

"""M6: compare the elaborated Prosa declarations of the patched build (fixed toolchain: Rocq 9.3.0,
MathComp 2.6.0, switch from the lock, .work/prosa-0.6-rocq93) against the ORIGINAL environment
(opam switch `prosa-0.6`: Rocq 9.0.1, MathComp 2.4.0 and the released rocq-prosa 0.6 package).

For every module given, the declarations are enumerated in each environment with `Print Module`,
then every declaration is printed with `Set Printing All` (fully explicit terms, opaque proofs
included). The printouts are compared after one normalization: MathComp 2.6 moved the ssreflect
libraries from `mathcomp.ssreflect.*` to `mathcomp.boot.*`, so those two path prefixes are
identified. Each declaration is classified as

  IDENTICAL          statement and body print identically;
  SAME_STATEMENT     identical statement (type), different body (for proofs: the Rocq 9.3 /
                     MathComp 2.6 tactics produced a different proof term of the same statement);
  STATEMENT_DIFFERS  the statements differ;
  ONLY_ORIGINAL / ONLY_PATCHED   present in one environment only.

Usage: python3 -I tools/compare_prosa.py OUT.json prosa.mod1 prosa.mod2 ...
"""
import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LOCK = json.loads((ROOT / "toolchains.lock.json").read_text())
PATCHED = {"name": "patched", "switch": LOCK["rocq"]["opam_switch"],
           "args": ["-R", str(ROOT / ".work" / "prosa-0.6-rocq93"), "prosa"]}
ORIGINAL = {"name": "original", "switch": "prosa-0.6", "args": []}
DECL = re.compile(r"(?:(?<=\s)|^)(Definition|Parameter|Axiom|Inductive|CoInductive|Record|Structure|Variant|Class)\s+([^\s:(]+)")
ENV = dict(os.environ, PATH=f"{Path.home()}/.local/bin:" + os.environ["PATH"])


def rocq(env, script, work):
    f = Path(work) / f"{env['name']}_{abs(hash(script)) % 10**8}.v"
    f.write_text(script)
    p = subprocess.run(["opam", "exec", "--switch=" + env["switch"], "--", "rocq", "compile", *env["args"], "-w", "-all",
                        str(f)], capture_output=True, text=True, env=ENV, cwd=work)
    if p.returncode != 0:
        raise RuntimeError(f"{env['name']}: rocq failed:\n{(p.stdout + p.stderr)[-3000:]}")


def names(env, mods, work):
    d = Path(work) / f"mods_{env['name']}"
    d.mkdir()
    s = [f"Require {m}." for m in mods] + ["Set Printing Width 1000000."]
    s += [f'Redirect "{d}/m{i}" Print Module {m}.' for i, m in enumerate(mods)]
    rocq(env, "\n".join(s) + "\n", work)
    out = {}
    for i, m in enumerate(mods):
        for g in DECL.finditer((d / f"m{i}.out").read_text()):
            out.setdefault(f"{m}.{g.group(2)}", g.group(1))
    return out


def prints(env, mods, decls, work, tag="decls", cmd="Print"):
    d = Path(work) / f"{tag}_{env['name']}"
    d.mkdir()
    s = [f"Require {m}." for m in mods] + ["Set Printing All.", "Set Printing Width 1000000."]
    s += [f'Redirect "{d}/d{i}" {cmd} {n}.' for i, n in enumerate(decls)]
    rocq(env, "\n".join(s) + "\n", work)
    res = {}
    for i, n in enumerate(decls):
        txt = (d / f"d{i}.out").read_text()
        txt = re.sub(r"\bmathcomp\.(ssreflect|boot)\.", "mathcomp.MC.", txt)
        txt = re.sub(r"^Fetching opaque proofs.*\n", "", txt, flags=re.M)
        res[n] = txt
    return res


def split(txt):
    """(body-or-whole, statement): `Print c` gives `c = body\n     : type` for constants."""
    m = re.search(r"\n\s+: ", txt)
    if not m:
        return txt.strip(), txt.strip()
    rest = txt[m.end():]
    stmt = rest.split("\n\n")[0].strip()
    return txt[:m.start()].strip(), stmt


# Presentation/relocation differences between the two environments that are not differences of the
# elaborated declaration. Each is applied to both printouts; the rules a declaration needed are recorded.
def unparen_return(t):
    """`return (T) with` (Rocq 9.0 printer) -> `return T with` (Rocq 9.3 printer)."""
    out, i = [], 0
    while True:
        j = t.find("return (", i)
        if j < 0:
            return "".join(out) + t[i:]
        k, depth = j + len("return ("), 1
        while k < len(t) and depth:
            depth += {"(": 1, ")": -1}.get(t[k], 0)
            k += 1
        if t.startswith(" with", k):
            out.append(t[i:j] + "return " + t[j + len("return ("):k - 1])
        else:
            out.append(t[i:k])
        i = k


RULES = [
    ("match_return_printing", "Rocq 9.3 prints `return T with` without parentheses", unparen_return),
    ("scope_delimiter_printing", "Rocq 9.3 prints Arguments scopes as %_scope", lambda t: t.replace("%_", "%")),
    ("ssreflect_rw_relocation", "Rocq 9.3 moved ssreflect's core (phant, Phant, ...) to Corelib.ssr.ssreflect_rw; "
     "Corelib.ssr.ssreflect re-exports them", lambda t: re.sub(r"\bssreflect_rw\.", "ssreflect.", t)),
]
IND_KINDS = ("Inductive", "Variant", "Record", "Structure", "Class", "CoInductive")
CTOR = re.compile(r"(?::=|\|)\s+(\w+)\s*(?:\{|:)")
HB = re.compile(r"\bHB_unnamed_(factory|mixin)_(\d+)\b")


def hb_renaming(mods, on, pn):
    """HB numbers its unnamed instances per file; patch 0002 removes a token before the first one,
    so the patched numbering is shifted. Pair them by order within each module (same kinds)."""
    ren = {}
    for m in mods:
        key = lambda n: int(HB.search(n).group(2))
        o = sorted((n for n in on if n.startswith(m + ".HB_unnamed_")), key=key)
        p = sorted((n for n in pn if n.startswith(m + ".HB_unnamed_")), key=key)
        if len(o) == len(p) and all(HB.search(a).group(1) == HB.search(b).group(1) for a, b in zip(o, p)):
            ren.update({b.rsplit(".", 1)[1]: a.rsplit(".", 1)[1] for a, b in zip(o, p) if a != b})
    return ren


def first_difference(a, b, ctx=120):
    i = next((k for k in range(min(len(a), len(b))) if a[k] != b[k]), min(len(a), len(b)))
    return {"original": a[max(0, i - ctx):i + ctx], "patched": b[max(0, i - ctx):i + ctx]}


def main():
    out, mods = Path(sys.argv[1]), sys.argv[2:]
    with tempfile.TemporaryDirectory() as work:
        envs = {}
        for env in (ORIGINAL, PATCHED):
            ns = names(env, mods, work)
            envs[env["name"]] = (ns, prints(env, mods, sorted(ns), work))
        # Constructors of inductive-like declarations (Rocq 9.3 prints records with Record syntax,
        # 9.0 as Variant): their full types are compared with `Check @C`.
        ctors = {}
        for e, (ns, ps) in envs.items():
            for n, k in ns.items():
                if k in IND_KINDS:
                    ctors.setdefault(n, set()).update(n.rsplit(".", 1)[0] + "." + c for c in CTOR.findall(ps[n]))
        ctor_names = sorted(c for n in ctors if n in envs["original"][0] and n in envs["patched"][0] for c in ctors[n])
        ctor_types = {e: prints(env, mods, ctor_names, work, "ctors", "Check @")
                      for e, env in (("original", ORIGINAL), ("patched", PATCHED))}
    on, op = envs["original"]
    pn, pp = envs["patched"]
    ren = hb_renaming(mods, on, pn)
    if ren:
        def hb(t):
            return HB.sub(lambda g: ren.get(g.group(0), g.group(0)), t)
        pn = {hb(n): k for n, k in pn.items()}
        pp = {hb(n): hb(t) for n, t in pp.items()}
    rows = {}

    def normalized(a, b):
        used = ["hb_unnamed_renumbering"] if ren and HB.search(a) else []
        for name, _, f in RULES:
            a2, b2 = f(a), f(b)
            if (a2, b2) != (a, b):
                used.append(name)
            a, b = a2, b2
        return a, b, used

    for n in sorted(set(on) | set(pn)):
        if n not in pn:
            rows[n] = {"status": "ONLY_ORIGINAL", "kind": on[n]}
            continue
        if n not in on:
            rows[n] = {"status": "ONLY_PATCHED", "kind": pn[n]}
            continue
        a, b, used = normalized(op[n], pp[n])
        (_, os_), (_, ps) = split(a), split(b)
        if op[n] == pp[n] and not (ren and HB.search(op[n])):
            st = "IDENTICAL"
        elif a == b:
            st = "IDENTICAL_MODULO_PRESENTATION"
        elif os_ == ps:
            st = "SAME_STATEMENT"
        else:
            st = "STATEMENT_DIFFERS"
        row = {"status": st, "kind": pn[n]}
        if st != "IDENTICAL" and used:
            row["normalizations"] = used
        if st == "STATEMENT_DIFFERS":
            row.update(original=os_, patched=ps)
        elif st == "SAME_STATEMENT":
            row["body_difference"] = first_difference(split(a)[0], split(b)[0])
        rows[n] = row
    # Inductive-like declarations whose printout differs only in presentation (Record vs Variant
    # syntax): equal arity (the printed header up to ":=") and constructors of identical full type.
    for n, r in rows.items():
        if r["status"] == "STATEMENT_DIFFERS" and r["kind"] in IND_KINDS:
            head = lambda t: re.sub(r"^(Variant|Record|Inductive|Structure|Class)\s+", "", t.split(":=")[0]).strip()
            cs = sorted(ctors.get(n, ()))
            same_ctors = cs and all(c in ctor_types["original"] and c in ctor_types["patched"] and
                                    normalized(ctor_types["original"][c], ctor_types["patched"][c])[0] ==
                                    normalized(ctor_types["original"][c], ctor_types["patched"][c])[1] for c in cs)
            if head(normalized(op[n], pp[n])[0]) == head(normalized(op[n], pp[n])[1]) and same_ctors:
                r["status"] = "INDUCTIVE_SAME_CONSTRUCTORS"
                r["constructors"] = cs
                r.pop("original"), r.pop("patched")
    summary = {}
    for r in rows.values():
        summary[r["status"]] = summary.get(r["status"], 0) + 1
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps({"original_env": {"switch": ORIGINAL["switch"], "rocq": "9.0.1", "mathcomp": "2.4.0",
                                                "prosa": "rocq-prosa 0.6 (opam, released)"},
                               "patched_env": {"switch": PATCHED["switch"], "rocq": "9.3.0", "mathcomp": "2.6.0",
                                               "prosa": "rt-proofs v0.6 + compat/prosa-0.6/patches"},
                               "normalizations": {k: d for k, d, _ in RULES} | {
                                   "hb_unnamed_renumbering": "HB unnamed instances renumbered (patch 0002): " + json.dumps(ren),
                                   "mathcomp_path": "mathcomp.ssreflect.* (2.4) and mathcomp.boot.* (2.6) identified"},
                               "modules": mods, "summary": summary, "declarations": rows}, indent=2) + "\n")
    print(json.dumps(summary))
    for n, r in rows.items():
        if r["status"] in ("STATEMENT_DIFFERS", "ONLY_ORIGINAL", "ONLY_PATCHED"):
            print(r["status"], n, r.get("original", "")[:400], "|", r.get("patched", "")[:400])
    return 0


if __name__ == "__main__":
    sys.exit(main())

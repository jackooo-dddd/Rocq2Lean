"""Classify every enumerated declaration and account for every file.

Authority for *what exists*: the compiled environment (tmQuoteModule, inventory/enumerate.py) and the
elaborated export (inventory/export.py: types, bodies, body states, universes, typing flags).
Source text is used only to attribute a declaration to its source sentence (keyword, locality).

Writes reports/prosa_inventory/declarations.jsonl and files.csv. Counting conventions are in the
module docstring of inventory/report.py and in FULL_INVENTORY_REPORT.md.
"""
import csv
import hashlib
import json
import os
import re
from collections import Counter, defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CFG = json.loads((ROOT / "inventory" / "config.json").read_text())
W = ROOT / ".work" / "inventory"
OUT = ROOT / "reports" / "prosa_inventory"
X = lambda p: Path(os.path.expanduser(p)) if p.startswith("~") else ROOT / p
norm = lambda n: n.replace("/", ".")

DECL_KW = ("Definition|Lemma|Theorem|Corollary|Fact|Remark|Proposition|Example|Property|Fixpoint|CoFixpoint|"
           "Inductive|CoInductive|Variant|Record|Structure|Class|Instance|Let|Canonical|Coercion|Function|"
           "Equations|Hypothesis|Hypotheses|Axiom|Parameter|Conjecture|Variable|Variables")
IDENT = r"[^\W\d][\w']*"                     # Rocq identifiers (Unicode letters, digits, _, ')
SENT = re.compile(r"(?:#\[[^\]]*\]\s*)*(?:(Local|Global|Polymorphic|Monomorphic|Program|Private|Existing)\s+)*"
                  rf"({DECL_KW})\s+(?:Structure\s+)?({IDENT})")
SCHEME = re.compile(r"^(.*)_(rect|ind|rec|sind)$")


def strip_comments(s):
    out, depth, i = [], 0, 0
    while i < len(s):
        if s.startswith("(*", i):
            depth += 1
            i += 2
        elif s.startswith("*)", i) and depth:
            depth -= 1
            i += 2
        else:
            if not depth:
                out.append(s[i])
            elif s[i] == "\n":
                out.append("\n")
            i += 1
    return "".join(out)


def sentence_end(txt, pos):
    """End of the vernacular sentence starting at pos: a '.' followed by blank or end of text."""
    m = re.compile(r"\.(?=\s|$)").search(txt, pos)
    return m.end() if m else len(txt)


def split_top(s, sep=";"):
    out, depth, cur = [], 0, []
    for ch in s:
        if ch in "({[":
            depth += 1
        elif ch in ")}]":
            depth -= 1
        if ch == sep and depth == 0:
            out.append("".join(cur))
            cur = []
        else:
            cur.append(ch)
    out.append("".join(cur))
    return out


def top_assign(sent):
    """Index just after the first ':=' outside parentheses/braces (binders may contain ':=')."""
    depth = 0
    for i in range(len(sent) - 1):
        ch = sent[i]
        if ch in "({[":
            depth += 1
        elif ch in ")}]":
            depth -= 1
        elif depth == 0 and sent.startswith(":=", i):
            return i + 2
    return None


def record_fields(sent):
    """Field / method names of a Record, Structure or Class sentence (also singleton classes)."""
    i = top_assign(sent)
    if i is None:
        return []
    rest = sent[i:].strip().rstrip(".").strip()
    m = re.match(rf"(?:{IDENT})?\s*\{{", rest)
    if m:
        body = rest[m.end():rest.rfind("}")]
        out = []
        for f in split_top(body):
            f = re.sub(r"#\[[^\]]*\]", "", f).strip()
            fm = re.match(rf"({IDENT})\s*(?:{IDENT}|\s|\(.*?\))*?:>?(?!=)", f, re.S)
            if fm:
                out.append(fm.group(1))
        return out
    sm = re.match(rf"({IDENT})\s*:(?!=)", rest)
    return [sm.group(1)] if sm else []


def source_attribution(path):
    """short name -> (keyword, local, line); fields/methods -> ("field", local, line)."""
    if not path.exists():
        return {}
    txt = strip_comments(path.read_text(errors="replace"))
    att = {}
    line_of = lambda pos: txt.count("\n", 0, pos) + 1
    for m in re.finditer(r"(?m)^\s*" + SENT.pattern, txt):
        attrs = m.group(0)
        kw, name = m.group(2), m.group(3)
        local = bool(re.search(r"#\[[^\]]*\blocal\b[^\]]*\]|\bLocal\b", attrs)) or kw in ("Let", "Hypothesis", "Hypotheses", "Variable", "Variables")
        att.setdefault(name, (kw, local, line_of(m.start(3))))
        if kw in ("Record", "Structure", "Class"):
            sent = txt[m.end():sentence_end(txt, m.end())]
            for f in record_fields(sent):
                att.setdefault(f, ("field", local, line_of(m.start(3))))
    for m in re.finditer(rf"HB\.mixin\s+Record\s+{IDENT}[^{{]*\{{([^}}]*)\}}", txt):
        for f in split_top(m.group(1)):
            fm = re.match(rf"\s*({IDENT})\s*:", re.sub(r"#\[[^\]]*\]", "", f))
            if fm:
                att.setdefault(fm.group(1), ("field", False, line_of(m.start())))
    return att


def digest(x):
    return None if x is None else hashlib.sha256(json.dumps(x, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


class Sorts:
    """Result sort of an elaborated type: walk to the codomain, read its head's type."""

    def __init__(self, decls):
        self.d = decls

    def gtype(self, t):
        k = t.get("k")
        if k == "const":
            x = self.d.get(norm(t["c"]))
            return x.get("type") if x else None
        if k == "ind":
            x = self.d.get(norm(t["ind"]["mind"]))
            if x:
                return x["bodies"][t["ind"]["i"]]["type"]
        return None

    def codomain_sort(self, ty, ctx=(), fuel=64):
        while ty.get("k") in ("prod", "let") and fuel:
            ctx = (ty.get("ty"),) + ctx
            ty, fuel = ty["b"], fuel - 1
        if ty.get("k") == "sort":
            return ("former", ty["s"]["k"])
        if ty.get("k") == "cast":
            return self.codomain_sort(ty["t"], ctx, fuel - 1)
        if ty.get("k") == "app" and ty["f"].get("k") == "lam" and fuel:
            # a β-redex `(fun x => B) a`: the sort of B (only its shape is read, so no substitution)
            return self.codomain_sort(ty["f"]["b"], (ty["f"].get("ty"),) + ctx, fuel - 1)
        h, n = ty, 0
        while h.get("k") == "app":
            n += len(h["args"])
            h = h["f"]
        ht = ctx[h["i"]] if h.get("k") == "rel" and h["i"] < len(ctx) else self.gtype(h)
        if ht is None:
            return ("unknown", None)
        for _ in range(n):
            if ht.get("k") != "prod":
                return ("unknown", None)
            ht = ht["b"]
        while ht.get("k") == "prod":
            ht = ht["b"]
        return ("inhabitant", ht["s"]["k"]) if ht.get("k") == "sort" else ("unknown", None)


ROLE_PATTERNS = [
    ("generated_anonymous_goal", re.compile(r"^Unnamed_thm\d*$")),
    ("generated_scheme", re.compile(r"_beq$|^internal_\w+_dec_(bl|lb)$|_eq_dec$")),
    ("generated_obligation", re.compile(r"_obligation_\d+$|_obligations$|_equation(_\d+)?$|_graph(_\w+)?$")),
    ("generated_instance", re.compile(r"_instance_\d+$")),
]


def role_of(kind, q, mod, short, a, inds):
    sm = SCHEME.match(short)
    if kind == "C" and sm and sm.group(1) in inds and not (a and a[0] != "field"):
        return "generated_scheme"
    if a and a[0] == "field":
        return "generated_projection"
    # a name introduced by a source sentence is a source declaration (HB commands are not matched as
    # sentences, so their output is never attributed); otherwise HB naming patterns
    if a:
        return "source_local_helper" if a[1] else "public_source"
    if "__" in short or short.startswith("HB_") or short == "axioms_" or ".Exports." in q or "/Exports." in q:
        return "generated_hb"
    for role, pat in ROLE_PATTERNS:
        if pat.search(short):
            return role
    return "unattributed"


def nature_of(kind, d, S):
    if kind == "I":
        return "inductive"
    if not d:
        return "unknown"
    st = d.get("body_state")
    if st in ("assumption", "unavailable"):
        return "assumption"
    shape = S.codomain_sort(d["type"])
    if shape[0] == "inhabitant" and shape[1] in ("prop", "sprop"):
        return "proof_opaque" if st == "opaque_present" else "proof_transparent"
    if shape[0] == "former":
        return "type_former_opaque" if st == "opaque_present" else "type_former"
    if shape[0] == "inhabitant":
        return "data_opaque" if st == "opaque_present" else "data_definition"
    return "unknown_opaque" if st == "opaque_present" else "unknown_transparent"


def relaxed_of(d):
    flags = (d or {}).get("native", {}).get("typing_flags") or {}
    r = sorted(k for k, v in flags.items()
               if (k in ("check_guarded", "check_positive", "check_universes", "check_eliminations") and v is False)
               or (k in ("impredicative_set", "allow_uip") and v is True))
    return r or None


def is_alias(d):
    b = (d or {}).get("body")
    while b and b.get("k") == "lam":
        b = b["b"]
    return bool(b) and b.get("k") in ("const", "ind", "construct")


def library_of(name):
    head = name.split(".", 1)[0]
    return {"prosa": "prosa", "mathcomp": "mathcomp", "Corelib": "corelib", "Stdlib": "stdlib",
            "HB": "hierarchy-builder", "elpi": "elpi", "CoqEAL": "coqeal", "Ltac2": "corelib"}.get(head, head)


def load_ir(fam):
    ir = {}
    p = W / f"ir-{fam}.ndjson"
    if p.exists():
        with open(p) as fh:
            for line in fh:
                x = json.loads(line)
                ir[x["name"]] = x
    return ir


def node_record(fam_reach, n, d, S, owner):
    k = "I" if d["kind"] == "inductive" else "C"
    return {"id": n, "family": owner, "reached_by": sorted(fam_reach), "module": ".".join(d["mp"].get("file", [])) if isinstance(d.get("mp"), dict) else None,
            "name": n, "kind": "inductive" if k == "I" else "constant", "role": "external_dependency" if owner == "external" else "shared_from_modern",
            "library": library_of(n), "nature": nature_of(k, d, S), "elaborated": True,
            "body_state": d.get("body_state"), "universes": (d.get("universes") or {}).get("k"),
            "type_sha256": digest(d.get("type") if k == "C" else [d.get("params"), d.get("bodies")]),
            "body_sha256": digest(d.get("body")) if k == "C" else None,
            "alias": is_alias(d) if k == "C" else False, "relaxed_checking": relaxed_of(d), "protected_interface": False}


def main():
    build = json.loads((W / "build.json").read_text())
    mods = json.loads((W / "modules.json").read_text())
    rows, files = [], []
    irs = {f: load_ir(f) for f in ("modern", "classic")}
    merged = {f: json.loads((W / f"merge-{f}.json").read_text()) if (W / f"merge-{f}.json").exists() else None
              for f in ("modern", "classic")}
    allir = {**irs["classic"], **irs["modern"]}
    S = Sorts({norm(n): d for n, d in allir.items()})
    owned = {}
    for fam in ("modern", "classic"):
        ir, mg = irs[fam], merged[fam] or {"requested": {}, "unquotable": {}, "failed": {}}
        tree = X(CFG[fam]["pristine"])
        fam_mods = {v["file"]: (m, v) for m, v in mods["modules"].items() if v["family"] == fam}
        for f, b in sorted(build[fam].items()):
            spath = tree / f
            mod = "prosa." + f[:-2].replace("/", ".")
            att = source_attribution(spath)
            entries = fam_mods[f][1]["entries"] if f in fam_mods else None
            counts = Counter()
            if entries is not None:
                inds = {norm(n.split("#")[0]).rsplit(".", 1)[-1] for k, n in entries if k == "I"}
                for k, n in entries:
                    req = n.split("#")[0]
                    q = mg["requested"].get(req, req)          # kernel identity (module path with "/")
                    alias = req.replace("/", ".") != q.replace("/", ".")
                    short = q.replace("/", ".").rsplit(".", 1)[-1]
                    a = att.get(short)
                    role = "alias_reexport" if alias else role_of(k, q, mod, short, a, inds)
                    d = ir.get(q)
                    counts[role] += 1
                    if not alias:
                        owned[q] = fam
                    export = ("exported" if d else "unquotable" if req in mg["unquotable"]
                              else "export_failed" if req in mg["failed"] else "not_exported")
                    rows.append({"id": req if alias else q, "family": fam, "module": mod, "file": f, "name": q, "requested": req,
                                 "canonical": q if alias else None,
                                 "kind": "inductive" if k == "I" else "constant", "role": role,
                                 "nature": nature_of(k, d, S), "export": export,
                                 "source": {"keyword": a[0], "local": a[1], "line": a[2]} if a else None,
                                 "elaborated": bool(d), "body_state": d.get("body_state") if d and k == "C" else None,
                                 "universes": (d.get("universes") or {}).get("k") if d else None,
                                 "type_sha256": (digest(d.get("type") if k == "C" else [d.get("params"), d.get("bodies")]) if d else None),
                                 "body_sha256": digest(d.get("body")) if d and k == "C" else None,
                                 "alias": is_alias(d) if d and k == "C" else False,
                                 "relaxed_checking": relaxed_of(d),
                                 "protected_interface": role in ("public_source", "generated_projection")})
                    if alias:
                        rows[-1]["source"] = None
            files.append({"family": fam, "file": f, "module": mod,
                          "sha256": hashlib.sha256(spath.read_bytes()).hexdigest() if spath.exists() else "",
                          "lines": spath.read_text(errors="replace").count("\n") if spath.exists() else "",
                          "build": b["build"], "build_reason": b.get("reason", ""),
                          "enumerated": "UNKNOWN" if entries is None else len(entries),
                          "public_source": "UNKNOWN" if entries is None else counts["public_source"],
                          "source_local_helper": "UNKNOWN" if entries is None else counts["source_local_helper"],
                          "generated": "UNKNOWN" if entries is None else sum(v for r, v in counts.items() if r.startswith("generated_")),
                          "unattributed": "UNKNOWN" if entries is None else counts["unattributed"],
                          "alias_reexports": "UNKNOWN" if entries is None else counts["alias_reexport"],
                          "import_only": entries is not None and len(entries) == 0,
                          "proposed_change": json.dumps(b.get("proposed_change")) if b.get("proposed_change") else ""})
    reach = defaultdict(set)
    for fam in ("modern", "classic"):
        for n in irs[fam]:
            reach[n].add(fam)
    for r in rows:
        r["reached_by"] = sorted(reach.get(r["name"], ()))
    for n in sorted(reach):
        if n not in owned:
            owner = "external"
            rows.append(node_record(reach[n], n, allir[n], S, owner))
    ids = Counter(r["id"] for r in rows)
    dup = [i for i, c in ids.items() if c > 1]
    if dup:
        raise SystemExit(f"duplicate identities: {dup[:10]}")
    OUT.mkdir(parents=True, exist_ok=True)
    with open(OUT / "declarations.jsonl", "w") as fh:
        for r in rows:
            fh.write(json.dumps(r, sort_keys=True) + "\n")
    with open(OUT / "files.csv", "w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=list(files[0]))
        w.writeheader()
        w.writerows(files)
    for fam in ("modern", "classic", "external"):
        rs = [r for r in rows if r["family"] == fam]
        print(fam, len(rs), dict(Counter(r["role"] for r in rs)), dict(Counter(r["nature"] for r in rs)))


if __name__ == "__main__":
    main()

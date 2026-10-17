"""Solver stage A: locate the level identifications typing forces in a failing declaration, from its shadow
record (fresh levels at every reference). Groups own levels and reference arguments by their value after
unification; prints the classes that join different source levels, with the source relation between them.
Usage: locate.py SHADOW.jsonl SOURCE.ndjson NAMES_FILE [REPORT.json]
With a report, only the classes of the levels its rejection messages name are printed, each member with the
constant it occurs in and whether it sits in the type (T) or the value (V)."""
import json, sys, collections, re
sys.path.insert(0, sys.argv[0].rsplit("/", 1)[0])
import solver_check as S

shadow, source, names = sys.argv[1], sys.argv[2], open(sys.argv[3]).read().split()
recs = {}
for l in open(shadow):
    r = json.loads(l)
    if r["decl"] in names: recs[r["decl"]] = r
# source universe facts: (a, rel, b) with rel in {"lt","le","eq"} (lines 2-4 of the IR: universe record)
facts = []
for l in open(source).readlines()[1:6]:
    d = json.loads(l)
    if d.get("kind") in ("universes", "universe_facts", "facts"):
        for x in d.get("relations", d.get("constraints", [])):
            facts.append(x)
lt = collections.defaultdict(set); le = collections.defaultdict(set)
for x in facts:
    nm = lambda v: v if isinstance(v, str) else ("Set" if v.get("k") == "set" else v.get("n", str(v)))
    a, rel, b = nm(x["l"]), x["rel"], nm(x["r"])
    (lt if rel in ("lt", "<") else le)[a].add(b)
def reach(a, b, strict=False, seen=None):
    seen = seen or set()
    if a in seen: return False
    seen.add(a)
    for c in lt[a]:
        if c == b or reach(c, b, False, seen): return True
    for c in le[a]:
        if (c == b and not strict) or reach(c, b, strict, seen): return True
    return False
def rel(a, b):
    if a == b: return "="
    x, y = reach(a, b), reach(b, a)
    return "≡" if x and y else ("≤" if x else ("≥" if y else "unrelated"))

msgs = {}
if len(sys.argv) > 4:
    for l in open(sys.argv[4]):
        l = l.strip().rstrip(",")
        if l.endswith("]}"): l = l[:-2]
        if not l.startswith('{"admitting'): continue
        try: row = json.loads(l)
        except ValueError: continue
        if row["source"] in names: msgs[row["source"]] = row["message"].split(" [last tier")[0]
def mvars(t, acc):
    if t[0] == "mvar": acc.add(t[1])
    elif t[0] not in ("zero", "param"):
        for x in t[1:]:
            if isinstance(x, tuple): mvars(x, acc)
    return acc
def by_message(n, r, resolve):
    side = collections.defaultdict(set)
    for tag, key in (("T", "sites_type"), ("V", "sites_value")):
        for _, v in r[key]:
            for m in mvars(S.parse(v), set()): side[m].add(tag)
    members = collections.defaultdict(list)
    for src, v in r["own"]:
        t = S.parse(v); members[S.canon(S.nf(resolve(t)))].append(("OWN", src, "".join(sorted(side[t[1]]))))
    for occ in r["occurrences"]:
        v, src, c = (occ + ["?"])[:3]
        t = S.parse(v); members[S.canon(S.nf(resolve(t)))].append((c.split(".")[-1], src, "".join(sorted(side[t[1]]))))
    named = set(re.findall(r"(?:mathcomp|HB|Corelib|Rocq)\.[\w.]*?\.\d+", msgs[n]))
    print(f"== {n.split('/')[-1][-75:]}\n   message: {msgs[n][:230]}")
    for ms in members.values():
        hit = {s for _, s, _ in ms} & named
        if not hit or len({s for _, s, _ in ms}) < 2: continue
        print(f"   class of {sorted(hit)}: {len(ms)} members")
        cnt = collections.Counter((".".join(s.split(".")[-2:]), c, sd) for c, s, sd in ms)
        for (s, c, sd), k in sorted(cnt.items(), key=lambda x: -x[1])[:10]:
            print(f"      {s:32} {c[:55]:55} {sd or '-':2} x{k}")

for n in names:
    rec = recs.get(n)
    if not rec or "record" not in rec:
        print(f"== {n[-70:]}: no record ({rec and rec.get('error')})"); continue
    r = rec["record"]
    asg = {int(k): S.parse(v) for k, v in r["assignments"]}
    def resolve(t, depth=0):
        if t[0] == "mvar" and t[1] in asg and depth < 200: return resolve(asg[t[1]], depth + 1)
        if t[0] in ("zero", "param", "mvar"): return t
        return (t[0],) + tuple(resolve(x, depth + 1) for x in t[1:])
    if n in msgs:
        by_message(n, r, resolve); continue
    site_of = {}
    for k, v in r["sites_type"] + r["sites_value"]:
        t = S.parse(v)
        if t[0] == "mvar": site_of.setdefault(t[1], k)
    members = collections.defaultdict(list)
    for src, v in r["own"]:
        t = S.parse(v)
        members[S.canon(S.nf(resolve(t)))].append(("own", src))
    for occ in r["occurrences"]:
        v, src = occ[0], occ[1]
        t = S.parse(v)
        members[S.canon(S.nf(resolve(t)))].append((site_of.get(t[1], "?").split("#")[0].split(".")[-1], src))
    print(f"== {n.split('/')[-1][-75:]}  ({len(r['own'])} own, {len(r['occurrences'])} occurrences, {len(r['postponed'])} postponed, diag {len(r['diagnostics'])})")
    shown = 0
    for cls, ms in sorted(members.items(), key=lambda kv: -len(kv[1])):
        srcs = sorted({s for _, s in ms})
        if len(srcs) < 2: continue
        owns = [s for k, s in ms if k == "own"]
        base = owns[0] if owns else srcs[0]
        rels = {s: rel(base, s) for s in srcs if s != base}
        bad = {s: x for s, x in rels.items() if x not in ("=", "≡")}
        if not bad: continue
        shown += 1
        if shown > 4: break
        print(f"   class of {base.split('.')[-1]} ({'own' if owns else 'reference'}): {len(ms)} members; joined with " +
              ", ".join(f"{s.split('.')[-2]}.{s.split('.')[-1]}[{x}]" for s, x in list(bad.items())[:6]))
    for d in r["diagnostics"][:2]: print("   diag:", d[:160])

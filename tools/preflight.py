#!/usr/bin/env python3
"""Preflight support classification of an export (no translation).

Classifies each declaration from its actual elaborated terms, never from surface keywords.
CANDIDATE_SUPPORTED means "no known blocker", not a guarantee of success. Kept in sync with
docs/SUPPORT_PROFILE.md. Every reason carries the node path of its first occurrence, and a root's
verdict names the dependency path to the first blocked declaration.

Statically detected blockers (the translator rejects the same shapes during translation):
  relaxed source checking flags; node kinds outside the fragment (cofix, proj, primitives, evars, section variables), SProp and
  irrelevant binders, universe-polymorphic levels and instances outside universe-polymorphic constants
  (R6 translates those), source assumptions and missing
  bodies; inductives that are polymorphic, coinductive, mutual, primitive records or mention
  template inductives with unbound template levels; `match` on a mutual block or an inductive with
  let-bound constructor arguments; mutual `fix` whose functions decrease at different
  positions; a single `fix` whose body is a match on its decreasing argument and whose recursive
  calls change a parameter before the decreasing argument while a type depends on that argument
  (otherwise the argument is generalized). M6 completion: calls on non-direct subterms
  (course-of-values), bodies that are not a match on the decreasing argument
  (ι-generalized lowering), mutual blocks, let-bound and higher-order partial uses of the function
  (ζ / δβ) and functional recursive fields are no longer static blockers; the translator decides.
Shape conditions that need typing (e.g. large elimination of a Prop-only inductive) are only
detected by the translator.
"""

import json
import sys

# Node kinds the current build translates (case/fix only in the shapes checked below).
SUPPORTED_NODES = {"rel", "sort", "cast", "prod", "lam", "let", "app", "const", "ind", "construct", "case", "fix", "proj"}
BOOTSTRAP = {"Corelib.Init.Datatypes.nat", "Corelib.Init.Logic.eq"}


class Found:
    """Reasons with the path of their first occurrence."""

    def __init__(self):
        self.where = {}

    def add(self, reason, path):
        self.where.setdefault(reason, "/".join(map(str, path)) or "<top>")


def head_rel_depth(ty):
    """For a constructor argument type `∀ zs, H args`: (H, number of leading products)."""
    depth = 0
    while ty["k"] == "prod":
        ty, depth = ty["b"], depth + 1
    while ty["k"] == "app":
        ty = ty["f"]
    return ty, depth


def mentions_rel(t, i):
    """Does `t` mention `rel i` (counting binders)?"""
    if isinstance(t, dict):
        k = t.get("k")
        if k == "rel":
            return t["i"] == i
        if k in ("prod", "lam"):
            return mentions_rel(t["ty"], i) or mentions_rel(t["b"], i + 1)
        if k == "let":
            return mentions_rel(t["v"], i) or mentions_rel(t["ty"], i) or mentions_rel(t["b"], i + 1)
        return any(mentions_rel(v, i) for v in t.values() if isinstance(v, (dict, list)))
    if isinstance(t, list):
        return any(mentions_rel(v, i) for v in t)
    return False


class Inductives:
    def __init__(self, decls):
        self.decls = decls
        self.in_poly = False        # walking a universe-polymorphic constant (R6)

    def ctor_args(self, ref, k):
        """Outermost-first constructor arguments of constructor k."""
        mib = self.decls[ref["mind"]]
        return list(reversed(mib["bodies"][ref["i"]]["ctors"][k]["args"]))

    def recursive_positions(self, ref, k):
        mib = self.decls[ref["mind"]]
        pos = []
        for p, a in enumerate(self.ctor_args(ref, k)):
            h, depth = head_rel_depth(a["ty"])
            if h == {"k": "rel", "i": p + mib["npars"] + depth}:
                pos.append(p)
        return pos

    def case_blockers(self, ref):
        """Reasons why `match` on this inductive cannot be lowered to a single-motive recursor."""
        mib = self.decls.get(ref["mind"])
        if mib is None:
            return ["match on an inductive absent from the export"]
        out = []
        if len(mib["bodies"]) != 1:
            out.append("match on a mutual inductive block")
            return out
        for k in range(len(mib["bodies"][0]["ctors"])):
            for p, a in enumerate(self.ctor_args(ref, k)):
                if a.get("body") is not None:
                    out.append("match on an inductive with let-bound constructor arguments")
                selfi = p + mib["npars"]
                h, depth = head_rel_depth(a["ty"])
                if h == {"k": "rel", "i": selfi + depth}:
                    # the self reference may still occur nested inside the arguments
                    t = a["ty"]
                    for _ in range(depth):
                        t = t["b"]
                    args = t["args"] if t["k"] == "app" else []
                    if any(mentions_rel(x, selfi + depth) for x in args):
                        out.append("match on a nested inductive")
                # (a field of another inductive applied to the type, e.g. list Rose: a nested inductive,
                # whose plain matches and fixpoints are supported since M6 completion; recursion through
                # the nesting is rejected by the translator)
        return sorted(set(out))


def walk(t, found, inds, path):
    if isinstance(t, list):
        for i, v in enumerate(t):
            walk(v, found, inds, path + [i])
        return
    if not isinstance(t, dict):
        return
    k = t.get("k")
    if k == "sort":
        s = t["s"]
        if s["k"] == "sprop":
            found.add("SProp", path)
        elif s["k"] == "type":
            for e in s["u"]:
                if e["l"]["k"] == "var" and not inds.in_poly:
                    found.add("polymorphic universe level", path)
        return
    if k is not None and k not in SUPPORTED_NODES:
        found.add(f"node:{k}", path)
    if k in ("const", "ind", "construct") and t.get("u"):
        # R6: an instance on a universe-polymorphic *constant* is translated; on an inductive it is not
        tgt = inds.decls.get(t["c"]) if k == "const" else None
        if not (tgt and tgt["kind"] == "constant" and tgt["universes"]["k"] == "polymorphic"):
            found.add("universe instance", path)
    if t.get("r") == "I":
        found.add("SProp-irrelevant binder", path)
    if k == "case":
        for reason in inds.case_blockers(t["ci"]["ind"]):
            found.add(reason, path)
    if k == "fix":
        fix_blockers(t, found, inds, path)
    for key, v in t.items():
        if key == "u" and k in ("const", "ind", "construct"):
            continue                      # a universe instance (levels), not a term
        if isinstance(v, (dict, list)):
            walk(v, found, inds, path + [key])


def fix_blockers(t, found, inds, path):
    defs = t["defs"]
    if len(defs) != 1:
        if len({d["rarg"] for d in defs}) != 1:
            found.add("mutual fixpoint whose functions decrease at different positions", path)
        return                               # otherwise decided by the translator (joint recursor)
    d = defs[0]
    r = d["rarg"]
    lams, b = [], d["body"]
    while b["k"] == "lam":
        lams.append(b)
        b = b["b"]
    nl = len(lams)
    if r >= nl:
        found.add("fixpoint decreasing argument not bound by its leading lambdas", path)
        return
    if b["k"] != "case" or b["c"] != {"k": "rel", "i": nl - 1 - r}:
        return                               # ι-generalized lowering: decided by the translator
    ref = b["ci"]["ind"]
    if inds.case_blockers(ref):
        return                               # reported by the case itself
    npar = b["ci"]["npar"]
    xty = lams[r]["ty"]
    xargs = xty["args"] if xty["k"] == "app" else []
    idx_pos = {r - 1 - a["i"] for a in xargs[npar:] if a["k"] == "rel" and a["i"] < r}
    changed = set()
    for k, br in enumerate(b["brs"]):
        nf = len(br["ctx"])
        rec_q = {nf - 1 - p for p in inds.recursive_positions(ref, k)}
        calls(br["body"], 0, nl, nf, r, idx_pos, rec_q, found, path + ["defs", 0, "body", f"branch{k}"], changed)
    # Changed leading arguments are generalized in the motive (supported), unless the decreasing
    # argument's type, or the type of a leading argument kept fixed, depends on them.
    for i in changed:
        if mentions_rel(lams[r]["ty"], r - 1 - i) or any(
                j not in changed and mentions_rel(lams[j]["ty"], j - 1 - i) for j in range(i + 1, r)):
            found.add("a type depends on an argument that recursive calls change", path)


def calls(t, depth, nl, nf, r, idx_pos, rec_q, found, path, changed):
    """Check every occurrence of the fixpoint variable inside a branch body (binder `depth` below the
    branch's fields): f = rel(nl + nf + depth), parameter i = rel(nl - 1 - i + nf + depth),
    field q = rel(q + depth)."""
    fi = nl + nf + depth
    go = lambda x, dd, seg: calls(x, depth + dd, nl, nf, r, idx_pos, rec_q, found, path + [seg], changed)
    if isinstance(t, list):
        for i, v in enumerate(t):
            calls(v, depth, nl, nf, r, idx_pos, rec_q, found, path + [i], changed)
        return
    if not isinstance(t, dict):
        return
    k = t.get("k")
    if k == "rel":
        return                               # a partial use: ζ / δβ, decided by the translator
    if k == "app" and t["f"] == {"k": "rel", "i": fi}:
        args = t["args"]
        if len(args) >= r + 1:
            for i in range(r):
                if i not in idx_pos and args[i] != {"k": "rel", "i": nl - 1 - i + nf + depth}:
                    changed.add(i)
            # (a call on a subterm that is not a direct field — a field of a matched field — is
            # course-of-values recursion since M6 completion: decided by the translator)
        for i, a in enumerate(args):
            go(a, 0, f"arg{i}")
        return
    if k in ("prod", "lam"):
        go(t["ty"], 0, "ty")
        go(t["b"], 1, "b")
        return
    if k == "let":
        go(t["v"], 0, "v")
        go(t["ty"], 0, "ty")
        go(t["b"], 1, "b")
        return
    if k == "case":
        go(t["p"]["params"], 0, "params")
        go(t["p"]["ret"], len(t["p"]["ctx"]), "ret")
        go(t["c"], 0, "c")
        for j, br in enumerate(t["brs"]):
            go(br["body"], len(br["ctx"]), f"branch{j}")
        return
    if k in ("fix", "cofix"):
        n = len(t["defs"])
        for j, dd in enumerate(t["defs"]):
            go(dd["ty"], 0, f"def{j}.ty")
            go(dd["body"], n, f"def{j}.body")
        return
    for key, v in t.items():
        if isinstance(v, (dict, list)):
            go(v, 0, key)


def global_levels(t, acc):
    if isinstance(t, list):
        for v in t:
            global_levels(v, acc)
    elif isinstance(t, dict):
        if t.get("k") == "sort" and t["s"]["k"] == "type":
            acc.update(e["l"]["n"] for e in t["s"]["u"] if e["l"]["k"] == "global")
        for v in t.values():
            if isinstance(v, (dict, list)):
                global_levels(v, acc)
    return acc


def template_blockers(d, found):
    """Inductives with global levels are supported (R2T): non-template ones obey R3 at references;
    template ones need every template level bound by exactly one parameter of sort Type@{l}
    (offset 0, possibly quality-polymorphic: translated at quality Type), per the kernel record."""
    gs = global_levels([[b["type"], [c["type"] for c in b["ctors"]]] for b in d["bodies"]], set())
    nat = d.get("native") or {}
    if not gs or not nat.get("template"):
        return
    ti = nat.get("template_info") or {}
    bound = []
    for k, pa in enumerate(ti.get("param_arguments", [])):
        if pa is None:
            continue
        us = pa.get("u", [])
        if pa.get("k") not in ("type", "quality_sort") or len(us) != 1 or us[0].get("n") != 0 or us[0].get("bound") is None:
            found.add("template parameter binding a level with an offset or an algebraic universe", ["native", "template_info"])
            return
        bound.append(us[0]["l"])
    defaults = ti.get("defaults", [])
    # other (non-template) levels are solved by unification or kept as non-template parameters (R5S)
    if sorted(bound) != sorted(defaults):
        found.add("template inductive with unbound template levels", ["native", "template_info"])


def relaxed_flags(d):
    """Source checking that the pilot does not accept (same rule as Emit.relaxedFlags)."""
    f = (d.get("native") or {}).get("typing_flags") or {}
    bad = [k for k in ("check_guarded", "check_positive", "check_universes", "check_eliminations") if f.get(k) is not True]
    bad += [k for k in ("impredicative_set", "allow_uip") if f.get(k) is not False]
    return bad


def classify(d, inds):
    found = Found()
    bad = relaxed_flags(d)
    if bad:
        found.add(f"relaxed source checking ({', '.join(bad)})", [])
    if d["kind"] == "constant":
        inds.in_poly = d["universes"]["k"] == "polymorphic"      # R6: its universe variables are parameters
        if d["body_state"] == "assumption":
            found.add("genuine source assumption", [])
        if d["body_state"] in ("unavailable", "unsupported_primitive"):
            found.add(f"body state {d['body_state']}", [])
        walk(d["type"], found, inds, ["type"])
        walk(d["body"], found, inds, ["body"])
        inds.in_poly = False
    else:
        if d["name"] in BOOTSTRAP and not found.where:
            return "CANDIDATE_SUPPORTED", {}
        if d["universes"]["k"] != "monomorphic":
            found.add("universe-polymorphic inductive", [])
        if d["finite"] == "CoFinite":
            found.add("coinductive type", [])
        if len(d["bodies"]) != 1:
            found.add("mutual inductive block", [])
        if any(b["projs"] and (len(b["ctors"]) != 1 or b["indices"] or len(b["projs"]) != len(b["ctors"][0]["args"]))
               for b in d["bodies"]):
            found.add("primitive record that is not structure-like", [])
        for i, b in enumerate(d["bodies"]):
            walk(b["type"], found, inds, ["bodies", i, "type"])
            for j, c in enumerate(b["ctors"]):
                walk(c["type"], found, inds, ["bodies", i, "ctors", j, "type"])
        if len(d["bodies"]) == 1:
            template_blockers(d, found)
    return ("UNSUPPORTED_FEATURE" if found.where else "CANDIDATE_SUPPORTED"), dict(sorted(found.where.items()))


def preflight(ir_path):
    lines = [json.loads(l) for l in open(ir_path)]
    decls = {d["name"]: d for d in lines if d["kind"] in ("constant", "inductive")}
    inds = Inductives(decls)
    roots = [r["name"] for r in lines[1]["roots"]]
    status = {n: classify(d, inds) for n, d in decls.items()}

    def deps(n):
        dd = decls[n]["deps"]
        return dd["type"] + dd.get("body", [])

    def blocker_path(n, seen=()):
        if status[n][0] != "CANDIDATE_SUPPORTED":
            return [n]
        for m in deps(n):
            if m in decls and m not in seen:
                p = blocker_path(m, seen + (n,))
                if p:
                    return [n] + p
        return None

    def root_entry(r):
        p = blocker_path(r)
        if not p:
            return {"status": "CANDIDATE_SUPPORTED"}
        where = status[p[-1]][1]
        return {"status": "UNSUPPORTED_FEATURE", "dependency_path": p, "blocked_declaration": p[-1],
                "reasons": sorted(where), "locations": where}

    return {
        "schema": "rocq2lean-preflight/2",
        "roots": {r: root_entry(r) for r in roots},
        "declarations": {n: {"status": s, "reasons": sorted(w), "locations": w} for n, (s, w) in status.items()},
    }


if __name__ == "__main__":
    # Exit status (docs/ACCEPTANCE_INVARIANTS.md, "CLI"): 0 every requested root is a candidate;
    # 2 a known blocker; 3 invalid input or tool failure. A candidate is not a translation result.
    if len(sys.argv) != 2:
        print("usage: preflight.py SOURCE.ndjson", file=sys.stderr)
        sys.exit(3)
    try:
        rep = preflight(sys.argv[1])
    except (OSError, ValueError, KeyError, IndexError, TypeError) as e:
        print(f"TOOL_FAILURE: invalid input: {type(e).__name__}: {e}", file=sys.stderr)
        sys.exit(3)
    print(json.dumps(rep, indent=2))
    blocked = {r: v["reasons"] for r, v in rep["roots"].items() if v["status"] != "CANDIDATE_SUPPORTED"}
    if blocked:
        print(f"UNSUPPORTED_FEATURE: blockers for roots {blocked}", file=sys.stderr)
        sys.exit(2)

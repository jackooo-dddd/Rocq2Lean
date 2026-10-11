"""Consistency tests of the Prosa inventory tooling (inventory/*.py) on a synthetic workspace:
duplicate identities, inconsistent chunk copies, missing bodies and missing dependency targets,
an import-only module, a failed build (unknown counts, never zero), cycles in the dependency graph,
role/nature classification and evidence grading without promotion."""
import hashlib
import json
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tests"))
sys.path.insert(0, str(ROOT / "inventory"))
from lib import check, finish  # noqa: E402

import classify  # noqa: E402
import coverage  # noqa: E402
import graph  # noqa: E402
import merge  # noqa: E402

FLAGS = {"check_guarded": True, "check_positive": True, "check_universes": True, "check_eliminations": True,
         "indices_matter": False, "impredicative_set": False, "sprop_allowed": True, "allow_uip": False}
PROP = {"k": "sort", "s": {"k": "prop"}}
TYPE = {"k": "sort", "s": {"k": "type", "u": [{"l": {"k": "set"}, "n": 1}]}}


def const(name, ty, body, state, tdeps=(), bdeps=()):
    return {"kind": "constant", "name": name, "mp": {"file": name.split(".")[:-1]}, "id": name.split(".")[-1],
            "type": ty, "body": body, "body_state": state, "universes": {"k": "monomorphic"}, "relevance": "R",
            "deps": {"type": list(tdeps), "body": list(bdeps)},
            "native": {"body_kind": state, "polymorphic": False, "typing_flags": FLAGS}}


def c(n):
    return {"k": "const", "c": n, "u": []}


def line(d):
    return json.dumps(d, separators=(",", ":")) + "\n"


def setup(tmp):
    w, out = tmp / "work", tmp / "reports"
    w.mkdir()
    out.mkdir()
    mt, ct = tmp / "modern", tmp / "classic"
    mt.mkdir()
    ct.mkdir()
    (mt / "a.v").write_text("(* Lemma commented : p. *)\nAxiom ax : Prop.\nDefinition p := ax.\nLemma thm : p.\n"
                            "#[local] Definition helper := Prop.\nDefinition c1 := c2.\nDefinition c2 := c1.\n")
    (mt / "imp.v").write_text("Require Export prosa.a.\n")
    (mt / "bad.v").write_text("Lemma broken : False.\n")
    (mt / "al.v").write_text("Module M := prosa.a.\n")
    decls = [const("prosa.a.ax", PROP, None, "assumption"),
             const("prosa.a.p", PROP, c("prosa.a.ax"), "transparent", bdeps=["prosa.a.ax"]),
             const("prosa.a.thm", c("prosa.a.p"), c("prosa.a.missing"), "opaque_present", ["prosa.a.p"], ["prosa.a.missing"]),
             const("prosa.a.helper", TYPE, PROP, "transparent"),
             const("prosa.a.c1", TYPE, c("prosa.a.c2"), "transparent", bdeps=["prosa.a.c2"]),
             const("prosa.a.c2", TYPE, c("prosa.a.c1"), "transparent", bdeps=["prosa.a.c1"])]
    names = [d["name"] for d in decls]
    # two chunks: identical copies of p, and an inconsistent copy of helper
    for i, ds in enumerate([decls[:4], [decls[1], dict(decls[3], body=TYPE), decls[4], decls[5]]]):
        cd = w / "export-modern" / f"chunk-{i:03d}"
        cd.mkdir(parents=True)
        ir = cd / "source-00.ndjson"
        alias = [{"requested": "prosa.al.M.p", "name": "prosa.a.p"}] if i == 1 else []
        ir.write_text(line({"kind": "header"}) + line({"kind": "roots", "roots": [{"requested": d["name"], "name": d["name"]} for d in ds] + alias})
                      + "".join(line(d) for d in ds))
        (cd / "result.json").write_text(json.dumps({"chunk": i, "roots": [d["name"] for d in ds], "unquotable": {}, "failed": {},
                                                    "irs": [{"tag": "00", "ir": str(ir), "roots": [d["name"] for d in ds],
                                                             "ir_sha256": hashlib.sha256(ir.read_bytes()).hexdigest()}]}))
    (w / "export-classic").mkdir()
    (w / "build.json").write_text(json.dumps({"modern": {"a.v": {"build": "COMPILED"}, "imp.v": {"build": "COMPILED"}, "al.v": {"build": "COMPILED"},
                                                         "bad.v": {"build": "COMPILE_ERROR", "reason": "synthetic"}},
                                              "classic": {}}))
    (w / "modules.json").write_text(json.dumps({"modules": {
        "prosa.a": {"family": "modern", "file": "a.v", "entries": [["C", n] for n in names]},
        "prosa.imp": {"family": "modern", "file": "imp.v", "entries": []},
        "prosa.al": {"family": "modern", "file": "al.v", "entries": [["C", "prosa.al.M.p"]]}}}))
    cfg = {"modern": {"pristine": str(mt), "working": str(mt)}, "classic": {"pristine": str(ct), "working": str(ct)}}
    for m in (classify, graph, merge, coverage):
        m.W = w
        if hasattr(m, "OUT"):
            m.OUT = out
        if hasattr(m, "CFG"):
            m.CFG = cfg
    return w, out, names


def main():
    with tempfile.TemporaryDirectory() as td:
        w, out, names = setup(Path(td))
        merge.main("modern")
        merge.main("classic")
        mg = json.loads((w / "merge-modern.json").read_text())
        check(mg["declarations"] == 6, "merge: identical chunk copies are stored once (6 distinct declarations)")
        check(list(mg["inconsistent_copies"]) == ["prosa.a.helper"], "merge: a differing copy of one name is recorded as inconsistent")
        stored = [json.loads(l)["name"] for l in open(w / "ir-modern.ndjson")]
        check(stored == sorted(stored), "merge: the store is sorted by name (deterministic)")

        classify.main()
        rows = {r["id"]: r for r in map(json.loads, open(out / "declarations.jsonl"))}
        check(set(rows) == set(names) | {"prosa.al.M.p"}, "classify: every enumerated entry has exactly one record")
        check(rows["prosa.al.M.p"]["role"] == "alias_reexport" and rows["prosa.al.M.p"]["canonical"] == "prosa.a.p"
              and not rows["prosa.al.M.p"]["protected_interface"],
              "classify: a module-alias entry is an alias/re-export of its canonical declaration, not a new declaration")
        check(rows["prosa.a.ax"]["nature"] == "assumption", "classify: a missing body is a source assumption")
        check(rows["prosa.a.thm"]["nature"] == "proof_opaque", "classify: an opaque proof of a Prop-valued type is proof_opaque")
        check(rows["prosa.a.p"]["nature"] == "type_former", "classify: a definition of type Prop is a type former")
        check(rows["prosa.a.helper"]["role"] == "source_local_helper", "classify: #[local] definitions are source-local helpers")
        check(rows["prosa.a.thm"]["role"] == "public_source" and rows["prosa.a.thm"]["protected_interface"],
              "classify: a public lemma is a protected interface declaration")
        check(rows["prosa.a.thm"]["source"]["line"] == 4, "classify: attribution ignores commented-out sentences")
        files = {r["file"]: r for r in __import__("csv").DictReader(open(out / "files.csv"))}
        check(set(files) == {"a.v", "imp.v", "bad.v", "al.v"}, "files: every source file is listed, including failed builds")
        check(files["al.v"]["alias_reexports"] == "1" and files["al.v"]["public_source"] == "0",
              "files: alias entries are counted separately from declarations")
        check(files["imp.v"]["import_only"] == "True" and files["imp.v"]["enumerated"] == "0",
              "files: an import-only module is recorded with zero declarations")
        check(files["bad.v"]["enumerated"] == "UNKNOWN" and files["bad.v"]["public_source"] == "UNKNOWN",
              "files: a failed build has UNKNOWN counts, not zero")

        # duplicate identities are refused
        mods = json.loads((w / "modules.json").read_text())
        mods["modules"]["prosa.imp"]["entries"] = [["C", "prosa.a.p"]]
        (w / "modules.json").write_text(json.dumps(mods))
        try:
            classify.main()
            dup = False
        except SystemExit as e:
            dup = "duplicate identities" in str(e)
        check(dup, "classify: a declaration attributed to two modules is refused as a duplicate identity")
        mods["modules"]["prosa.imp"]["entries"] = []
        (w / "modules.json").write_text(json.dumps(mods))
        classify.main()

        graph.main(build_graph=False)
        g = json.loads((w / "graph.json").read_text())
        check(g["preflight_declarations"]["prosa.a.ax"]["status"] == "UNSUPPORTED_FEATURE", "graph: the assumption is a direct blocker")
        check(g["roots"]["prosa.a.thm"]["preflight"] == "BLOCKED_DEPENDENCY" and g["roots"]["prosa.a.thm"]["reachable_blockers"] == ["prosa.a.ax"],
              "graph: a root reaching the assumption through its type is blocked downstream")
        check(g["roots"]["prosa.a.helper"]["preflight"] == "CANDIDATE_SUPPORTED", "graph: an independent declaration stays a candidate")
        check("prosa.al.M.p" not in g["roots"], "graph: an alias entry is not a separate root")
        check(g["missing_edge_targets"] == {"prosa.a.missing": 1}, "graph: a dependency absent from the export is recorded, not dropped")
        deps = {r["id"]: r for r in map(json.loads, open(out / "dependencies.jsonl")) if r["graph"] == "semantic"}
        check(deps["prosa.a.thm"]["edges"] == {"opaque_body": ["prosa.a.missing"], "type": ["prosa.a.p"]},
              "graph: opaque proof dependencies are a separate edge kind")
        check(deps["prosa.a.thm"].get("missing_targets") == ["prosa.a.missing"], "graph: the missing target is listed on its node")
        check(["prosa.a.c1", "prosa.a.c2"] in g["nontrivial_sccs"], "graph: a dependency cycle is one strongly connected component")
        ax_group = next(x for x in g["groups"] if x["mechanism"] == "genuine source assumption")
        check(ax_group["affected_roots"]["combined"] == 3 and ax_group["direct_roots"] == 1,
              "blockers: affected roots count the direct and the downstream roots (ax, p, thm)")

        # a translation failure recorded by a run is a known blocker, separate from the preflight verdict
        (w / "extra_blockers.json").write_text(json.dumps({"declarations": {"prosa.a.c2": [
            {"reason": "UNSUPPORTED_FEATURE: synthetic", "category": "missing_rule", "status": "UNSUPPORTED_FEATURE",
             "source": "translation:synthetic", "detail": "synthetic"}]}}))
        graph.main(build_graph=False)
        g = json.loads((w / "graph.json").read_text())
        check(g["roots"]["prosa.a.c1"]["preflight"] == "CANDIDATE_SUPPORTED" and g["roots"]["prosa.a.c1"]["known"] == "KNOWN_BLOCKER_DOWNSTREAM",
              "graph: a known translation failure blocks its cycle partner without changing the preflight verdict")
        check(g["roots"]["prosa.a.c2"]["known"] == "KNOWN_BLOCKER_DIRECT", "graph: the failing declaration is a direct known blocker")
        # a preflight reason contradicted by a current translation of the same record is not a known blocker
        x = json.loads((w / "extra_blockers.json").read_text())
        x["translated_in_current_runs"] = {"prosa.a.ax": ["synthetic"]}
        (w / "extra_blockers.json").write_text(json.dumps(x))
        graph.main(build_graph=False)
        g = json.loads((w / "graph.json").read_text())
        check(g["roots"]["prosa.a.thm"]["preflight"] == "BLOCKED_DEPENDENCY" and g["roots"]["prosa.a.thm"]["known"] == "NO_KNOWN_BLOCKER"
              and "prosa.a.ax" in g["preflight_contradicted_by_evidence"],
              "graph: a preflight blocker contradicted by translation evidence keeps the preflight verdict but is not a known blocker")

        # evidence grading: no promotion
        e = {"current_impl": True, "identical_source": True, "status": "TRANSLATED_AND_CHECKED", "as_root": False}
        check(coverage.grade(dict(e, run_verify="AUDIT_REJECTED")) == "KERNEL_CHECKED_UNVERIFIED",
              "coverage: kernel acceptance in an unverified run is not VERIFIED")
        check(coverage.grade(dict(e, run_verify="VERIFIED")) == "VERIFIED_AS_DEPENDENCY", "coverage: a verified dependency is not a verified root")
        check(coverage.grade(dict(e, run_verify="VERIFIED", identical_source=False)) == "STALE_EVIDENCE_ONLY",
              "coverage: evidence for a different elaborated declaration is stale")
        check(coverage.grade(dict(e, run_verify="VERIFIED", current_impl=False)) == "STALE_EVIDENCE_ONLY",
              "coverage: evidence from another implementation is stale")
    finish("test-inventory")


if __name__ == "__main__":
    main()

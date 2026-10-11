"""Enumerate the declarations of every compiled module with MetaRocq's tmQuoteModule (the compiled
Rocq environment is the authority: Sections closed, generated declarations included). One Rocq file
per family; each module's output is one line `MOD <module> <kind> <kername> | …`.
Writes .work/inventory/modules.json: module -> [(kind, kername)], plus failures per module.
"""
import json
import os
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CFG = json.loads((ROOT / "inventory" / "config.json").read_text())
W = ROOT / ".work" / "inventory"
SW = json.loads((ROOT / "toolchains.lock.json").read_text())["rocq"]["opam_switch"]
X = lambda p: Path(os.path.expanduser(p)) if p.startswith("~") else ROOT / p
ENV = dict(os.environ, PATH=f"{Path.home()}/.local/bin:" + os.environ["PATH"])
HEAD = '''From MetaRocq.Utils Require Import utils.
From MetaRocq.Template Require Import All.
Open Scope bs_scope.
Definition gname (g : global_reference) : string :=
  match g with
  | ConstRef k => "C " ^ string_of_kername k
  | IndRef i => "I " ^ string_of_kername i.(inductive_mind) ^ "#" ^ string_of_nat i.(inductive_ind)
  | ConstructRef i n => "K " ^ string_of_kername i.(inductive_mind) ^ "#" ^ string_of_nat i.(inductive_ind) ^ "#" ^ string_of_nat n
  | VarRef v => "V " ^ v
  end.
'''


def run_family(fam, mods, loadpaths):
    d = W / f"enum-{fam}"
    d.mkdir(parents=True, exist_ok=True)
    lines = [HEAD] + [f"Require {m}." for m in mods]
    for m in mods:
        lines.append(f'MetaRocq Run (tmBind (tmQuoteModule "{m}") (fun l => tmMsg ("MOD {m} " ^ String.concat " | " (map gname l)))).')
    (d / "Enum.v").write_text("\n".join(lines) + "\n")
    p = subprocess.run(["opam", "exec", f"--switch={SW}", "--", "rocq", "compile", *loadpaths, "Enum.v"],
                       cwd=d, capture_output=True, text=True, env=ENV)
    (d / "enum.log").write_text(p.stdout + p.stderr)
    got = {}
    for line in (p.stdout + p.stderr).splitlines():
        if line.startswith("MOD "):
            _, m, rest = (line + " ").split(" ", 2)
            items = [x.strip() for x in rest.split(" | ") if x.strip()]
            got[m] = [x.split(" ", 1) for x in items]
    return got, p.returncode


def main():
    b = json.loads((W / "build.json").read_text())
    mw, cb = X(CFG["modern"]["working"]), X(CFG["classic"]["working"])
    comp = cb / "compat"
    out = {"modules": {}, "failures": {}}
    modern = [("prosa." + f[:-2].replace("/", "."), f) for f, x in b["modern"].items() if x["build"] == "COMPILED"]
    classic = [("prosa." + f[:-2].replace("/", "."), f) for f, x in b["classic"].items() if x["build"] == "COMPILED"]
    ce = ROOT / ".work" / "coqeal-ce3d1d6"
    for fam, mods, lp in (("modern", modern, ["-R", str(mw), "prosa", "-R", str(ce), "CoqEAL"]),
                          ("classic", classic, ["-R", str(mw), "prosa", "-R", str(cb / "classic"), "prosa.classic",
                                                "-Q", str(comp), "Compat"])):
        got, rc = run_family(fam, [m for m, _ in mods], lp)
        for m, f in mods:
            if m in got:
                out["modules"][m] = {"family": fam, "file": f, "entries": got[m]}
            else:
                out["failures"][m] = {"family": fam, "file": f, "reason": f"no tmQuoteModule output (rocq exit {rc})"}
        print(fam, len(mods), "modules,", sum(1 for m, _ in mods if m in got), "enumerated,",
              sum(len(got.get(m, [])) for m, _ in mods), "entries")
    (W / "modules.json").write_text(json.dumps(out, indent=1) + "\n")


if __name__ == "__main__":
    main()

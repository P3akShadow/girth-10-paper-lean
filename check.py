#!/usr/bin/env python3
"""Rebuild this project's proof files and audit every Paper theorem.

Only this project's installed dependency object files are reused; project
proof modules are rebuilt into a fresh temporary directory. No paper LaTeX
files or sibling projects are required.
"""
from pathlib import Path
import os
import re
import subprocess
import sys
import tempfile

PROJECT = Path(__file__).resolve().parent
PACKAGES = PROJECT / ".lake/packages"
TOOLCHAIN = (PROJECT / "lean-toolchain").read_text().strip()

# Every numbered paper item has explicit exports in PaperProofs.lean.
PAPER_RESULTS = {
    1: ["Paper.Numbered.theorem_01"],
    2: ["Paper.Numbered.lemma_02"],
    3: ["Paper.Numbered.lemma_03"],
    4: ["Paper.Numbered.lemma_04"],
    5: ["Paper.Numbered.theorem_05"],
    6: ["Paper.Numbered.theorem_06"],
    7: ["Paper.Numbered.Definition07", "Paper.Numbered.definition_07_regular_connected"],
    8: ["Paper.Numbered.lemma_08"],
    9: ["Paper.Numbered.lemma_09"],
    10: ["Paper.Numbered.corollary_10_minimum", "Paper.Numbered.corollary_10_tower"],
    11: ["Paper.Numbered.corollary_11_minimum", "Paper.Numbered.corollary_11_tower"],
    12: ["Paper.Numbered.lemma_12"],
    13: ["Paper.Numbered.lemma_13"],
    14: ["Paper.Numbered.proposition_14"],
    15: ["Paper.Numbered.corollary_15"],
    16: ["Paper.Numbered.corollary_16"],
}
PAPER_EQUATIONS = ["Paper.Numbered.equation_01"]


def source_order(requested):
    sources = {p.stem: p for p in PROJECT.glob("*.lean")}
    visiting, done, ordered = set(), set(), []

    def visit(name):
        if name in done:
            return
        if name in visiting:
            raise SystemExit(f"Cyclic project import: {name}")
        visiting.add(name)
        source = sources[name]
        for line in source.read_text().splitlines():
            match = re.match(r"^import\s+(.+)$", line)
            if match:
                for dep in match.group(1).split():
                    if dep in sources:
                        visit(dep)
                    elif not dep.startswith(("Mathlib", "Lean", "Std", "Batteries")):
                        raise SystemExit(f"Missing independent module {dep} in {source.name}")
        visiting.remove(name)
        done.add(name)
        ordered.append(source)

    for source in requested or sorted(sources.values()):
        if source.parent != PROJECT or source.stem not in sources:
            raise SystemExit(f"Not a project proof file: {source}")
        visit(source.stem)
    return ordered


def main():
    files = source_order([Path(p).resolve() for p in sys.argv[1:]])
    full_audit = not sys.argv[1:]
    with tempfile.TemporaryDirectory(prefix="paper-proof-check-") as out:
        env = os.environ.copy()
        env["LEAN_PATH"] = os.pathsep.join([
            out,
            *(str(p) for p in sorted(PACKAGES.glob("*/.lake/build/lib/lean"))),
        ])
        for source in files:
            print(f"Checking {source.name}", flush=True)
            subprocess.run([
                "lean", f"+{TOOLCHAIN}", "--root", str(PROJECT),
                "-o", str(Path(out) / (source.stem + ".olean")), str(source),
            ], check=True, cwd=PROJECT, env=env)
        audit = Path(out) / "Audit.lean"
        audit.write_text(
            "".join(f"import {source.stem}\n" for source in files)
            + ("".join(f"#check {name}\n" for names in PAPER_RESULTS.values() for name in names)
               + "".join(f"#check {name}\n" for name in PAPER_EQUATIONS)
               if full_audit else "")
            + '''open Lean Elab Command in
run_cmd do
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let mut count : Nat := 0
  for (name, info) in (← getEnv).constants.toList do
    if name.toString.startsWith "Paper." && info.isTheorem then
      count := count + 1
      for axiomName in ← Lean.collectAxioms name do
        unless allowed.contains axiomName do
          throwError "Unexpected axiom {axiomName} in {name}"
  logInfo m!"Axiom audit passed for {count} Paper theorems."
'''
        )
        result = subprocess.run(
            ["lean", f"+{TOOLCHAIN}", str(audit)],
            check=False, cwd=PROJECT, env=env, capture_output=True, text=True,
        )
        if result.returncode:
            print(result.stdout, end="")
            print(result.stderr, end="", file=sys.stderr)
            raise SystemExit(result.returncode)
        for line in result.stdout.splitlines():
            if "Axiom audit passed" in line:
                print(line)
        if "Axiom audit passed" not in result.stdout:
            raise SystemExit("Missing axiom audit result")
        print(f"Checked {len(files)} independent proof modules.")
        if full_audit:
            print(f"All {len(PAPER_RESULTS)} numbered paper items and Equation (1) "
                  "are present; their theorems are axiom-audited.")


if __name__ == "__main__":
    main()

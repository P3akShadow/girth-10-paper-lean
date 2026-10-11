# Paper proofs

This directory is an independent Lean project containing the paper's definitions
and proofs. It can be copied out of the surrounding repository and built on its
own. All external packages are fetched into its own `.lake/packages/` directory;
no sibling project or preexisting package cache is required.

## Build

Install Git and the Lean toolchain manager `elan`, which supplies the `lean` and
`lake` commands. The first build requires internet access to fetch the pinned
toolchain, dependencies, and compiled Mathlib cache.

From this directory, run:

```sh
lake exe cache get Mathlib.Order.Partition.Finpartition Mathlib.Combinatorics.SimpleGraph.Girth Mathlib.Combinatorics.SimpleGraph.Acyclic Mathlib.Tactic
lake build
```

The first command downloads the compiled Mathlib modules used by these proofs
and their dependencies. A plain `lake build` also works without the cache, but
then Lean must compile the required dependencies from source.

The versions are pinned by the files shipped with this directory:

- `lean-toolchain`: Lean `v4.34.0-rc1`.
- `lakefile.toml`: Mathlib commit
  `fd891ee98c2a2188e2d19011d304e0db23a1759f`.
- `lake-manifest.json`: exact Git revisions of all transitive dependencies.

Keep the manifest when copying or distributing the project. There is no need
to run `lake update` for a normal build.

## Check the proofs

`PaperProofs.lean` collects every numbered statement in paper order. Its imports
provide the definitions and supporting proofs, so keep all `.lean` files when
copying the project.

Corollary 16 is exported as `Paper.Numbered.corollary_16`. Its supporting
proof in `Corollary16MinimalSubcubic.lean` works for every threshold `k >= 6`:
minimum-order subcubic graphs of twin-width at least `k` are cubic and have
girth at least five. `SubcubicOrderMinimal` compares against all smaller
finite subcubic graphs, not only induced subgraphs. `SubcubicReductions.lean`
checks the low-degree and short-cycle contractions, and the quotient argument
preserves the sparse-width lower bound when edge colors are forgotten.
The girth conclusion uses `egirth`, with infinity for acyclic graphs.

For a clean recompilation of the project's proof modules and an axiom audit,
install Python 3 and run after the build:

```sh
python3 check.py
```

The checker compiles project modules into a fresh temporary directory, using
only the dependency object files from this project's `.lake/packages/`. It
rejects any theorem in the `Paper` namespace that depends on axioms other than
`propext`, `Classical.choice`, and `Quot.sound`, including unproved placeholders.

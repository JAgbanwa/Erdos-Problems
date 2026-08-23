# Erdős Problem #81 — Chordal Clique Partitions

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.21273143.svg)](https://doi.org/10.5281/zenodo.21273143)
[![License: CC BY-NC 4.0](https://img.shields.io/badge/License-CC_BY--NC_4.0-lightgrey.svg)](https://creativecommons.org/licenses/by-nc/4.0/)

Erdős Problem #81 asks whether the edge clique-partition number of every
n-vertex chordal graph is at most `n^2/6 + O(n)`. **The problem remains open.**

This directory collects individually verified preprints and formal artifacts
from an ongoing research program on the problem. Each release states its exact
scope; **no single item here resolves Erdős #81.** Further findings related to
the problem will be published here as they are completed and verified.

Problem reference: https://www.erdosproblems.com/81

## Published preprints

**Paper I — *Affine Profile Reduction for Fractional Triangle Packings in Split
Graphs.*** For every split graph `G`, it proves

```text
|E(G)| − 2·ν₃*(G) ≤ n²/6 + n,
```

by a finite, analytic argument (no asymptotic transfer theorem). The theorem is
machine-verified in Lean 4 (Mathlib v4.28.0): sorry-free, with an axiom report
reducing to Lean's three standard foundational axioms and no project-specific
axiom.

- [Paper I v1.3 — PDF (English)](preprints/PAPER_I/01_manuscript/PAPER_I_preprint_v1.3_en.pdf)
- [Paper I v1.3 — PDF (Spanish)](preprints/PAPER_I/01_manuscript/PAPER_I_preprint_v1.3_es.pdf)
- [Full package (manuscript, ledger, reproducibility, integrity, Lean)](preprints/PAPER_I/)
- [Lean 4 formalization](preprints/PAPER_I/05_formalization/lean_v1.2_freeze/)
- [Plain-language explainer (four levels, rendered)](https://htmlpreview.github.io/?https://github.com/jtraverso/erdos-81-chordal-clique-partitions/blob/main/preprints/PAPER_I/PaperI_explained_4_levels.html)

**Paper II — *Complete-Split Extremizers for a Fractional Triangle-Cover
Functional on Chordal Graphs.*** For every integer `n ≥ 1`, over chordal graphs
on `n` vertices it determines the exact maximum

```text
max ( |E(G)| − 2·τ₃*(G) ) = ⌊(2n+1)²/24⌋,
```

attained by a complete-split graph `S_{p,q} = K_p ∨ K̄_q`. Finite and cover-first
(no integral packing, no strong LP duality, no asymptotic packing theorem);
machine-verified in Lean 4 (Mathlib v4.28.0): sorry-free, unconditional on the
standard `IsChordal` definition, axioms reducing to Lean's three standard ones.

- [Paper II v1.2 — PDF (English)](preprints/PAPER_II/01_manuscript/PAPER_II_preprint_v1.2_en.pdf)
- [Paper II v1.2 — PDF (Spanish)](preprints/PAPER_II/01_manuscript/PAPER_II_preprint_v1.2_es.pdf)
- [Full package (manuscript, ledger, validation, reproducibility, integrity, Lean)](preprints/PAPER_II/)
- [Lean 4 formalization](preprints/PAPER_II/05_formalization/lean_v1.2_freeze/)
- [Plain-language explainer (four levels, rendered)](https://htmlpreview.github.io/?https://github.com/jtraverso/erdos-81-chordal-clique-partitions/blob/main/preprints/PAPER_II/PaperII_explained_4_levels.html)

**Paper III — *Linear-Error Clique Partitions of Split Graphs via Structured
Triangle Packing.*** It resolves the split-graph case of Erdős Problem #81 at
the conjectured scale:

```text
cp(G) ≤ n²/6 + O(n)
```

The coefficient `1/6` is sharp in the quadratic term, improving the previously
identified split-graph upper coefficient `3/16`; the least uniform linear
coefficient is not claimed. The theorem is machine-verified in Lean 4 with no
project mathematical axiom on the public theorem path. The full problem for
all chordal graphs remains open.

- [Paper III v1.5 — PDF (English)](preprints/PAPER_III/01_manuscript/PAPER_III_preprint_v1.5_en.pdf)
- [Paper III v1.5 — PDF (Spanish)](preprints/PAPER_III/01_manuscript/PAPER_III_preprint_v1.5_es.pdf)
- [Full package (manuscript, validation, reproducibility, integrity, Lean)](preprints/PAPER_III/)
- [Lean 4 formalization](preprints/PAPER_III/05_formalization/lean_v1.4_freeze/)
- [Plain-language explainer (four levels, rendered)](https://htmlpreview.github.io/?https://github.com/jtraverso/erdos-81-chordal-clique-partitions/blob/main/preprints/PAPER_III/PaperIII_explained_4_levels.html)

## What Papers I–III establish — and what remains open

| Paper | Established result | Scope not claimed |
|---|---|---|
| **Paper I** | The finite fractional inequality `\|E(G)\| − 2·ν₃*(G) ≤ n²/6 + n` for split graphs | No integral clique-partition theorem and no theorem for all chordal graphs |
| **Paper II** | The exact maximum `⌊(2n+1)²/24⌋` of `\|E(G)\| − 2·τ₃*(G)` over `n`-vertex chordal graphs, attained by a complete-split graph | No integral clique-partition theorem and no resolution of Erdős #81 |
| **Paper III** | The integral bound `cp(G) ≤ n²/6 + O(n)` for split graphs, with sharp quadratic coefficient `1/6` | No theorem for all chordal graphs and no claim for the least uniform linear coefficient |

Thus Paper III resolves Erdős #81 for split graphs at the conjectured quadratic
scale, while the problem for all chordal graphs remains open.

## Formal verification

Paper I's main theorem is checked in Lean 4. To reproduce, from
`preprints/PAPER_I/05_formalization/lean_v1.2_freeze/`:

```bash
lake exe cache get   # fetch the prebuilt Mathlib cache
lake build           # exit 0 type-checks every theorem with no sorry
```

The recorded `#print axioms` output is in
`preprints/PAPER_I/05_formalization/lean_v1.2_freeze/gate_logs/`:

```text
PaperI.paperI_main depends on axioms: [propext, Classical.choice, Quot.sound]
```

Paper II is likewise checked from `preprints/PAPER_II/05_formalization/lean_v1.2_freeze/`
(`lake exe cache get` then `lake build`), with recorded output in that package's
`gate_logs/`:

```text
PaperII.theorem_1_2 depends on axioms: [propext, Classical.choice, Quot.sound]
```

Paper III uses the immutable source freeze at
`preprints/PAPER_III/05_formalization/lean_v1.4_freeze/`. Its aggregate public
root and directed axiom-query roots were reproduced independently; the public
theorem path has footprint:

```text
[propext, Classical.choice, Quot.sound]
```

## Scope and disclaimers

- These are preprints and formalization artifacts. They have undergone the
  documented adversarial AI audits linked from each package, but they have
  **not undergone human peer review** or specialist priority review.
- Each item is deliberately scoped. Paper I concerns the finite fractional
  packing bound for split graphs; Paper II concerns the exact fractional-cover
  extremum for chordal graphs; Paper III proves the integral `n²/6 + O(n)`
  bound for split graphs. None resolves the full chordal problem.

## Citation

Archived on Zenodo — concept DOI [10.5281/zenodo.21273143](https://doi.org/10.5281/zenodo.21273143),
which resolves to the latest deposited version. The current Papers I–III
snapshot is [Zenodo v3](https://doi.org/10.5281/zenodo.22064657).
See also `CITATION.cff`, `CITATION.bib`, and `CITATION.md` in this directory.

## License

Documents and artifacts are licensed under Creative Commons
Attribution-NonCommercial 4.0 International (CC BY-NC 4.0); see `LICENSE`.
The Lean sources additionally depend on Mathlib, distributed under the Apache
License 2.0.

## Integrity

A SHA-256 manifest for this directory is provided in `manifest_sha256.txt`.
Sub-packages contain their own integrity manifests.

The complete preceding public packages are retained under each paper's
`superseded/preprint_v1.0/` directory. Intermediate v1.x working drafts were
internal and were not public releases.

## Author

Juan Pablo Traverso Gianini — Independent research

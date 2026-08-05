# Erdős Problem #81 — Chordal Clique Partitions

Erdős Problem #81 asks whether the edge clique-partition number of every
n-vertex chordal graph is at most `n^2/6 + O(n)`. **The problem remains open.**

This folder holds public materials from an ongoing research program on the
problem. **No item here resolves Erdős #81**; each is individually scoped and
verified, and further findings will be added as they are completed.

Problem reference: https://www.erdosproblems.com/81

## Official materials

See [`official/`](official/).

Currently published:

- **Paper I — *Affine Profile Reduction for Fractional Triangle Packings in
  Split Graphs.*** Proves `|E(G)| − 2·ν₃*(G) ≤ n²/6 + n` for split graphs, by a
  finite analytic argument, machine-verified in Lean 4 (sorry-free, axiom-clean).
  [PDF](official/preprints/PAPER_I/01_manuscript/PAPER_I_preprint_v1.0.pdf) ·
  [package](official/preprints/PAPER_I/) ·
  [Lean](official/preprints/PAPER_I/05_formalization/lean/) ·
  [explainer](https://htmlpreview.github.io/?https://github.com/jtraverso/erdos-81-chordal-clique-partitions/blob/main/preprints/PAPER_I/PaperI_explained_4_levels.html)

- **Paper II — *Complete-Split Extremizers for a Fractional Triangle-Cover
  Functional on Chordal Graphs.*** Determines the exact maximum over **chordal**
  graphs on `n` vertices: `max ( |E(G)| − 2·τ₃*(G) ) = ⌊(2n+1)²/24⌋`, attained by a
  complete-split graph, by a finite analytic argument, machine-verified in Lean 4
  (sorry-free, axiom-clean, unconditional on the standard `IsChordal` definition).
  [PDF](official/preprints/PAPER_II/01_manuscript/PAPER_II_preprint_v1.0.pdf) ·
  [package](official/preprints/PAPER_II/) ·
  [Lean](official/preprints/PAPER_II/05_formalization/lean/) ·
  [explainer](https://htmlpreview.github.io/?https://github.com/jtraverso/erdos-81-chordal-clique-partitions/blob/main/preprints/PAPER_II/PaperII_explained_4_levels.html)

Both papers are fractional-functional results (a triangle-**packing** bound on
split graphs, ν₃*; an exact triangle-**cover** extremum on chordal graphs, τ₃*).
Neither establishes an integral clique-partition bound `cp(G)`, an asymptotic
transfer, or a resolution of Erdős #81, which remains open. Each has an
independent AI adversarial audit (PASS) but is not externally peer-reviewed. See
each package README for the exact scope.

## Status

These are preprints and formalization artifacts; they are not externally
peer-reviewed. Erdős #81 itself remains open.

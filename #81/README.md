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
  [Lean](official/preprints/PAPER_I/05_formalization/lean/)

Paper I establishes the finite fractional bound for **split** graphs only. It
does not establish an integral clique-partition theorem, an asymptotic transfer
result, or a theorem for all chordal graphs. See the package README for the
exact scope.

## Status

These are preprints and formalization artifacts; they are not externally
peer-reviewed. Erdős #81 itself remains open.

# Erdős Problem #81 — Chordal Clique Partitions

Erdős Problem #81 asks whether the edge clique-partition number of every
`n`-vertex chordal graph is at most `n²/6 + O(n)`. **The problem for all chordal
graphs remains open.**

This folder mirrors the current public Papers I–III repository maintained at
[jtraverso/erdos-81-chordal-clique-partitions](https://github.com/jtraverso/erdos-81-chordal-clique-partitions).
The complete mirrored package is under [`official/`](official/), including the
manuscripts, Lean formalizations, audit evidence, reproducibility records and
integrity manifests.

Zenodo concept DOI: [10.5281/zenodo.21273143](https://doi.org/10.5281/zenodo.21273143)

Problem reference: https://www.erdosproblems.com/81

## Current preprints

### Paper I — Affine Profile Reduction for Fractional Triangle Packings in Split Graphs

Paper I v1.3 proves the finite fractional inequality

```text
|E(G)| − 2·ν₃*(G) ≤ n²/6 + n
```

for every split graph `G` on `n` vertices.

[English PDF](official/preprints/PAPER_I/01_manuscript/PAPER_I_preprint_v1.3_en.pdf) ·
[Spanish PDF](official/preprints/PAPER_I/01_manuscript/PAPER_I_preprint_v1.3_es.pdf) ·
[complete package](official/preprints/PAPER_I/)

### Paper II — Complete-Split Extremizers for a Fractional Triangle-Cover Functional on Chordal Graphs

Paper II v1.2 determines, for every integer `n ≥ 1`,

```text
max (|E(G)| − 2·τ₃*(G)) = floor((2n+1)²/24)
```

over `n`-vertex chordal graphs, with equality attained by a complete-split
graph.

[English PDF](official/preprints/PAPER_II/01_manuscript/PAPER_II_preprint_v1.2_en.pdf) ·
[Spanish PDF](official/preprints/PAPER_II/01_manuscript/PAPER_II_preprint_v1.2_es.pdf) ·
[complete package](official/preprints/PAPER_II/)

### Paper III — Linear-Error Clique Partitions of Split Graphs via Structured Triangle Packing

Paper III v1.5 proves

```text
cp(G) ≤ n²/6 + O(n)
```

for every split graph `G`, with sharp quadratic coefficient `1/6`. Thus it
resolves the split-graph case of Erdős Problem #81 at the conjectured
quadratic scale. It does **not** resolve the problem for all chordal graphs.

[English PDF](official/preprints/PAPER_III/01_manuscript/PAPER_III_preprint_v1.5_en.pdf) ·
[Spanish PDF](official/preprints/PAPER_III/01_manuscript/PAPER_III_preprint_v1.5_es.pdf) ·
[complete package](official/preprints/PAPER_III/)

## Verification status and scope

The three packages contain frozen Lean 4 sources and recorded internal and
independent adversarial AI audits with final verdict `PASS`. These controls are
an intermediate assurance tier: the papers have not undergone human peer
review or specialist priority review.

Paper I and Paper II establish fractional results. Paper III establishes the
integral `n²/6 + O(n)` bound for split graphs. None proves the corresponding
statement for every chordal graph.

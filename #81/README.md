# Erdős Problem #81 — Chordal Clique Partitions

Erdős Problem #81 asks whether the edge clique-partition number of every
`n`-vertex chordal graph is at most `n²/6 + O(n)`. **Paper IV gives a Lean-verified
proof of this bound, using pieces of order at most four**, as well as sharp
eventual bounds and quantitative stability. Other proofs of the extremal
bounds are attributed and compared in the manuscript; no priority is claimed.

This folder mirrors the public Papers I–IV repository maintained at
[jtraverso/erdos-81-chordal-clique-partitions](https://github.com/jtraverso/erdos-81-chordal-clique-partitions).
The complete package under [`official/`](official/) is an exact Git-tree copy
of [commit b76e7948645d7482fdb1c98102129bf7adbf64ef](https://github.com/jtraverso/erdos-81-chordal-clique-partitions/tree/b76e7948645d7482fdb1c98102129bf7adbf64ef),
tagged `paper-IV-v1.23`. It includes the manuscripts, frozen Lean sources,
audit evidence, reproducibility records and integrity manifests.

- Series concept DOI: [10.5281/zenodo.21273143](https://doi.org/10.5281/zenodo.21273143).
- Published Papers I–IV deposit: [10.5281/zenodo.23089131](https://doi.org/10.5281/zenodo.23089131).
- [Series overview](official/index.html) and [browser preview](https://htmlpreview.github.io/?https://github.com/jtraverso/erdos-81-chordal-clique-partitions/blob/main/index.html).
- Problem reference: https://www.erdosproblems.com/81.

The source snapshot records the DOI as awaiting publication at its preparation
time; the deposit is now public. That dated record is preserved unchanged.

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

over `n`-vertex chordal graphs, with equality attained by a complete-split graph.

[English PDF](official/preprints/PAPER_II/01_manuscript/PAPER_II_preprint_v1.2_en.pdf) ·
[Spanish PDF](official/preprints/PAPER_II/01_manuscript/PAPER_II_preprint_v1.2_es.pdf) ·
[complete package](official/preprints/PAPER_II/)

### Paper III — Linear-Error Clique Partitions of Split Graphs via Structured Triangle Packing

Paper III v1.5 proves `cp(G) ≤ n²/6 + O(n)` for every split graph `G`, with
sharp quadratic coefficient `1/6`. It establishes the conjectured quadratic
scale for split graphs and supplies infrastructure used in Paper IV.

[English PDF](official/preprints/PAPER_III/01_manuscript/PAPER_III_preprint_v1.5_en.pdf) ·
[Spanish PDF](official/preprints/PAPER_III/01_manuscript/PAPER_III_preprint_v1.5_es.pdf) ·
[complete package](official/preprints/PAPER_III/)

### Paper IV — Clique partitions with rooted simplicial defect: quantitative stability and sharp eventual bounds

Paper IV v1.23 proves, for every chordal graph of order `n`,

```text
cp(G) ≤ c₄(G) ≤ M(n) + b,    M(n) = floor(n(n+1)/6),
```

for an absolute constant `b`, where `c₄` restricts partition pieces to cliques
of order at most four. For sufficiently large `n`, the bound is `M(n)` and is
attained even against unrestricted clique partitions. Quantitative stability
controls both the graph and all near-optimal partitions using one clique root.
The paper also treats fixed and sublinear rooted simplicial defect and gives
explicit, impractical thresholds. The universal strengthening `b = 0` is not proved.

[English PDF](official/preprints/PAPER_IV/01_manuscript/PAPER_IV_preprint_v1.23_en.pdf) ·
[Spanish PDF](official/preprints/PAPER_IV/01_manuscript/PAPER_IV_preprint_v1.23_es.pdf) ·
[complete package](official/preprints/PAPER_IV/) ·
[four-level explainer](official/preprints/PAPER_IV/PaperIV_explained_4_levels.html)

## Verification status and scope

Papers I–III retain their recorded audits. Paper IV's consolidated external
adversarial AI audit concluded **PASS for the exact v1.22-r4 artifacts**.
Version 1.23 is an editorial-only revision with separate semantic and typesetting
checks; the mathematical content and Lean freeze are unchanged. The exact
audited manuscripts and original reports remain in the audit backups. The
public draft v0.8 is retained as superseded, not as a current preprint.

The main formal source identity is `piv-v12-fb459343d234`. The recorded formal
evidence covers 607 main modules, 19 explicit targets and 224 export checks,
plus a separate 50-module annex. The public proof declarations use only
`propext`, `Classical.choice` and `Quot.sound`, or subsets; Lean, Mathlib and
pinned packages remain software dependencies. No new build is claimed for this mirror.

These are author preprints, not human peer-reviewed publications. The reports
state the scope and model-independence limitations of the AI audits. Such
audits are not a specialist priority determination. Historical material outside
`official/` is preserved, not endorsed as the current proof.

# Erdős Problem #81 — Chordal Clique Partitions

Erdős Problem #81 asks whether the edge clique-partition number of every
n-vertex chordal graph is at most `n^2/6 + O(n)`. **The problem remains open.**

This directory collects individually verified preprints and formal artifacts
from an ongoing research program on the problem. Each release states its exact
scope; **no single item here resolves Erdős #81.** Further findings related to
the problem will be published here as they are completed and verified.

Problem reference: https://www.erdosproblems.com/81

## Published preprint

**Paper I — *Affine Profile Reduction for Fractional Triangle Packings in Split
Graphs.*** For every split graph `G`, it proves

```text
|E(G)| − 2·ν₃*(G) ≤ n²/6 + n,
```

by a finite, analytic argument (no asymptotic transfer theorem). The theorem is
machine-verified in Lean 4 (Mathlib v4.28.0): sorry-free, with an axiom report
reducing to Lean's three standard foundational axioms and no project-specific
axiom.

- [Paper I — PDF (English)](preprints/PAPER_I/01_manuscript/PAPER_I_preprint_v1.0.pdf)
- [Paper I — PDF (Spanish)](preprints/PAPER_I/01_manuscript/PAPER_I_preprint_v1.0_es.pdf)
- [Full package (manuscript, ledger, reproducibility, integrity, Lean)](preprints/PAPER_I/)
- [Lean 4 formalization](preprints/PAPER_I/05_formalization/lean/)
- [Plain-language explainer (four levels)](preprints/PAPER_I/PaperI_explained_4_levels.html)

## What Paper I proves — and what it does not

| Statement | Status in Paper I |
|---|---|
| `\|E\| − 2·ν₃* ≤ n²/6 + n` for split graphs (fractional) | **Proved**, finite & analytic, Lean-verified |
| Leading constant `1/6` | Matches the constant of Erdős #81 |
| Integral clique-partition bound `cp(G) ≤ n²/6 + O(n)` | **Not** established here |
| Asymptotic transfer `cp = (1/6+o(1))n²` for chordal graphs | **Not** established here |
| A theorem for **all chordal** graphs (beyond split) | **Not** established here |
| Erdős #81 itself | **Open** |

## Formal verification

Paper I's main theorem is checked in Lean 4. To reproduce, from
`preprints/PAPER_I/05_formalization/lean/`:

```bash
lake exe cache get   # fetch the prebuilt Mathlib cache
lake build           # exit 0 type-checks every theorem with no sorry
```

The recorded `#print axioms` output is in
`preprints/PAPER_I/05_formalization/lean/gate_logs/`:

```text
PaperI.paperI_main depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Scope and disclaimers

- These are preprints and formalization artifacts; they are **not externally
  peer-reviewed** and have not undergone specialist priority review.
- Each item is deliberately scoped. Paper I concerns the finite fractional
  bound for split graphs only.

## Citation

See `CITATION.cff`, `CITATION.bib`, and `CITATION.md` in this directory.

## License

Documents and artifacts are licensed under Creative Commons
Attribution-NonCommercial 4.0 International (CC BY-NC 4.0); see `LICENSE`.
The Lean sources additionally depend on Mathlib, distributed under the Apache
License 2.0.

## Integrity

A SHA-256 manifest for this directory is provided in `manifest_sha256.txt`.
Sub-packages contain their own integrity manifests.

## Author

Juan Pablo Traverso Gianini — Independent researcher, Santiago, Chile
ORCID: https://orcid.org/0009-0003-6068-4096 — jtraverso@gmail.com

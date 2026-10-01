# Paper IV — draft (v0.8)

**Title:** *Clique partitions of chordal graphs: mixed rounding and construction in the critical regime*  
**Author:** Juan Pablo Traverso Gianini  
**Package date:** 2026-09-21  
**Status:** public author draft; not a final release; not human peer-reviewed.

This package presents the chordal clique-partition theorem in two forms:

\[
\exists b\in\mathbb N\quad\forall G\text{ chordal},\qquad
c_4(G)\le\left\lfloor\frac{n(n+1)}6\right\rfloor+b,
\]

and the sharp bound without the additive constant for all sufficiently large
orders. Here a partition covers every edge exactly once, and each piece is a
clique of order at most four. The all-orders bound implies the
`cp(G) ≤ n²/6 + O(n)` formulation of Erdős Problem #81. The draft also gives
eventual extremal witnesses and further structural results. It does not prove
the sharp bound for every small order, evaluate the full global threshold, or
claim a universal linear fractional–integral gap.

## Read the draft / Leer el borrador

- [English PDF](01_manuscript/PAPER_IV_preprint_v0.8_en.pdf)
- [PDF en español](01_manuscript/PAPER_IV_preprint_v0.8_es.pdf)
- [English Markdown](01_manuscript/PAPER_IV_preprint_v0.8_en.md)
- [Markdown en español](01_manuscript/PAPER_IV_preprint_v0.8_es.md)
- [English LaTeX](01_manuscript/PAPER_IV_preprint_v0.8_en.tex)
- [LaTeX en español](01_manuscript/PAPER_IV_preprint_v0.8_es.tex)

The version is **draft**, with manuscript revision **v0.8**. The six manuscript
files are byte-identical to the reviewed bilingual v0.8 artifacts; no
mathematical or editorial text was changed during packaging. The manuscript's
discussion of an unassigned public cut records its pre-publication state.
This package binds that cut by source hashes; its repository commit supplies
the public identifier. See [release metadata](RELEASE_METADATA.json).

## Evidence and what it means

- [Internal audit and limits](02_validation/01_INTERNAL_AUDITS/run_draft_20260921/FINAL_INTERNAL_REPORT.md)
- [Executable checks](02_validation/01_INTERNAL_AUDITS/run_draft_20260921/check_release.py)
- [Fresh author-side build and audit results](03_reproducibility/author_build_evidence/RESULTS.json)
- [Public theorem contract tests](03_reproducibility/PublicContracts.lean)
- [Trust boundary and provenance](04_integrity/PROVENANCE_AND_TRUST.md)
- [Source and package integrity](04_integrity/README.md)

| Statement | Frozen Lean declaration |
|---|---|
| All orders, additive constant | `PaperIV.Erdos81AllOrders.erdos81_all_orders_additive` |
| All orders, historical linear-error form | `PaperIV.Erdos81AllOrders.erdos81_all_orders` |
| Sharp bound for sufficiently large orders | `PaperIV.Erdos81Unconditional.erdos81_cliquePartition` |
| Eventual extremal maximum | `PaperIV.PaperTheorems.erdos81_max_eq` |

Their full printed statements and axiom footprints are retained in
[`public_contracts.log`](03_reproducibility/author_build_evidence/public_contracts.log).

“No external mathematical hypotheses” means that the named exported theorems
do not take an unproved rounding, near-regime or LP-optimum interface as an
argument, and their audited axiom sets contain no project mathematical axiom
or `sorryAx`. The allowed foundational axioms are `propext`,
`Classical.choice` and `Quot.sound`.

It does **not** mean “no third-party software”, “no prior mathematical
results”, or “all code independently originated here”. Lean, Mathlib and its
pinned packages remain dependencies. Proofs and infrastructure from this
series are included. Namespace-cone checks alone cannot detect copied and
renamed code and do not establish bibliographic originality.

**En español.** La evidencia incluye comprobaciones de integridad,
reproducción con caché, axiomas y tipos literales de los teoremas. No sustituye
una auditoría matemática independiente ni revisión humana. Las constantes
aditivas y el umbral global no se presentan como valores numéricos óptimos.

## Package structure

```text
01_manuscript/       English/Spanish Markdown, TeX, PDF and figures
02_validation/      Author-side internal checks; external-audit status
03_reproducibility/ Frozen-source reproduction, fresh/recorded logs, PDF QA
04_integrity/       Source binding, provenance, package manifest
05_formalization/   Immutable Lean source tree and original frozen ZIP
```

This matches the five-part structure of Papers I–III. No earlier Paper IV
working drafts, API credentials, research downloads, cache or compiled Lean
artifacts are part of this draft package. The previous releases of Papers
I–III and their historical evidence are unchanged.

## Reproduce

Follow [the reproduction instructions](03_reproducibility/README.md).
The freeze uses Lean/Mathlib v4.28.0. Its original source ZIP has SHA-256
`4f6ba1b40ace1d926ae5fab7490c4bc0dc3f236dea28640de4cee0166da60afa`.

The internal run is author-side and cache-assisted, not an independent
clean-room reproduction. See the [external-audit status](02_validation/02_IA_ADVERSARIAL_AUDITS/README.md)
before treating the package as a final release.

## License

Written materials follow the series' CC BY-NC 4.0 license. Existing upstream
software licenses and notices remain applicable; packaging does not relicense
Mathlib or third-party contributions. See [LICENSE.md](LICENSE.md).

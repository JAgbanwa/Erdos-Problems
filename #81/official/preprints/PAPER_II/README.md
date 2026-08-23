# Paper II — Official preprint release v1.2

**Title:** *Complete-Split Extremizers for a Fractional Triangle-Cover Functional on Chordal Graphs*
**Author:** Juan Pablo Traverso Gianini
**Release date:** 2026-08-22
**Status:** official author preprint; externally AI-audited; not human peer-reviewed
**Novelty boundary:** corpus-bounded review; no specialist priority determination

This is the canonical public package for Paper II v1.2. It supersedes the public
v1.0 package, retained in full at [`superseded/preprint_v1.0/`](superseded/preprint_v1.0/).
Intermediate v1.x working drafts were internal and were not public releases.

## Read the paper

- [English PDF](01_manuscript/PAPER_II_preprint_v1.2_en.pdf)
- [Spanish PDF](01_manuscript/PAPER_II_preprint_v1.2_es.pdf)
- [English Markdown](01_manuscript/PAPER_II_preprint_v1.2.md)
- [Spanish Markdown](01_manuscript/PAPER_II_preprint_v1.2_es.md)
- [Bilingual plain-language explainer](PaperII_explained_4_levels.html)

## Package

```text
01_manuscript/       Markdown, LaTeX, PDF, figures and artifact hashes
02_validation/       Internal and independent external adversarial audits
03_reproducibility/  Manuscript build records and reproduction notes
04_integrity/        Current release manifests and provenance
05_formalization/    Lean v1.2 frozen source archive and build evidence
figures/             Image assets used by the GitHub-rendered explainer
superseded/          Complete preceding public package
```

The final external residual report closes Paper II v1.2 with `PASS`; see
[`02_validation/02_IA_ADVERSARIAL_AUDITS/run_2026-08-21_v1.2_pkgfix/30_REPORT/FINAL_AUDIT_REPORT.md`](02_validation/02_IA_ADVERSARIAL_AUDITS/run_2026-08-21_v1.2_pkgfix/30_REPORT/FINAL_AUDIT_REPORT.md).
The promotion from audited draft to public preprint changed release-status
prose, filenames and derived PDF/hash artifacts only; protected mathematics and
the Lean freeze are unchanged.

## Scope

For every integer `n ≥ 1`, over chordal graphs on `n` vertices, the paper
determines

```text
max (|E(G)| − 2·τ₃*(G)) = floor((2n+1)²/24),
```

attained by a complete-split graph. It does not establish an integral
clique-partition theorem, an asymptotic transfer theorem, or a resolution of
Erdős Problem #81.

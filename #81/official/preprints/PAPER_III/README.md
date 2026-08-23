# Paper III — Official preprint release v1.5

**Title:** *Linear-Error Clique Partitions of Split Graphs via Structured Triangle Packing*  
**Author:** Juan Pablo Traverso Gianini  
**Release date:** 2026-08-23  
**Status:** official author preprint; externally AI-audited; not human peer-reviewed  
**Novelty boundary:** corpus-bounded review; no specialist priority determination

Paper III v1.5 is the first formal public preprint release of Paper III. It
resolves the split-graph case of Erdős Problem #81 at the conjectured sharp
quadratic scale `n²/6 + O(n)`. It does not resolve the full chordal-graph
problem.

## Read the paper

- [English PDF](01_manuscript/PAPER_III_preprint_v1.5_en.pdf)
- [Spanish PDF](01_manuscript/PAPER_III_preprint_v1.5_es.pdf)
- [English Markdown](01_manuscript/PAPER_III_preprint_v1.5.md)
- [Spanish Markdown](01_manuscript/PAPER_III_preprint_v1.5_es.md)
- [Bilingual plain-language explainer](PaperIII_explained_4_levels.html)

## Audit continuity from v1.4 to v1.5

The mathematical manuscript and Lean freeze were audited as the unpublished
`preprint_draft_v1.4` target. That exact package is preserved at
[`superseded/unpublished_audited_draft_v1.4/`](superseded/unpublished_audited_draft_v1.4/).

The v1.4 mathematical, computational and Lean conclusions remain applicable to
v1.5 because the theorem core, definitions, constants, proof architecture,
formulas, citations, Lean source tree and frozen ZIP are unchanged. In
particular:

- [the complete v1.4 internal audit](02_validation/01_INTERNAL_AUDITS/run_2026-08-22_v1.4/10_REPORT/INTERNAL_AUDIT_FINAL_REPORT.md)
  closed with `PASS` after 144/144 checks;
- [the v1.4 external residual audit](02_validation/02_IA_ADVERSARIAL_AUDITS/run_2026-08-22_v1.4_residual/30_REPORT/FINAL_AUDIT_REPORT.md)
  independently rederived the analytic core and completed an uninterrupted
  clean-room Lean reproduction;
- [the final v1.4 external challenger report](02_validation/02_IA_ADVERSARIAL_AUDITS/run_2026-08-23_v1.4_challenger/30_REPORT/FINAL_AUDIT_REPORT.md)
  closed with `PASS`, with no blocker, major finding or open minor finding;
- [the separate clean author reproduction](03_reproducibility/author_build_evidence/run_2026-08-23_clean_PASS/README.md)
  is retained as corroborating build evidence.

The v1.5 delta is deliberately narrow: release-status promotion; explicit
`simple` in Theorem 2.2; three one-line Appendix D justifications already
checked by the external challenger; removal of a duplicated rendered author
block; correction of the PDF author metadata; and synchronized English/Spanish
format regeneration. These changes are documented in
[`CHANGELOG_v1.5.md`](CHANGELOG_v1.5.md) and covered by the v1.5 internal
[residual audit](02_validation/01_INTERNAL_AUDITS/run_2026-08-23_v1.5_internal_residual/10_REPORT/FINAL_INTERNAL_RESIDUAL_AUDIT_REPORT.md),
which closed with `PASS` after 79/79 checks, including the added stale-evidence
shadowing controls from `EXT-V15-M01`. The independent v1.5 residual audit
verified all gates but initially preserved one non-mathematical minor finding;
the subsequent [external closure report](02_validation/02_IA_ADVERSARIAL_AUDITS/run_2026-08-23_v1.5_residual_closure/30_REPORT/FINAL_CLOSURE_REPORT.md)
closed that finding after 10/10 checks and issued the consolidated verdict
`PASS`. No earlier audit report has been rewritten. The audited release is now
ready for the public repository commit and tag.

## Formalization

The release carries the immutable source-only freeze
[`05_formalization/lean_v1.4_freeze/`](05_formalization/lean_v1.4_freeze/).
Its archive is `PAPER_III_lean_v1.4_freeze.zip`, SHA-256
`79ee24c38fd776bc2585a0c3c996e30817f0829fc5064463bdbde0fa2d3d7104`.

The external clean-room run compiled the public root in 8,455 jobs, the query
roots in 8,444 jobs, and all eight axiom-query files. The designated theorem
surfaces have foundational footprint
`[propext, Classical.choice, Quot.sound]`, with no project mathematical axiom
and no `sorryAx` on the public theorem path.

## Package

```text
01_manuscript/       Markdown, LaTeX, PDF, figures and artifact hashes
02_validation/       Internal and independent external adversarial audits
03_reproducibility/  Manuscript builds, rendered QA and Lean build evidence
04_integrity/        Release manifests, provenance and semantic-diff records
05_formalization/    Immutable Lean v1.4 frozen source and archive
figures/             Images used by the GitHub-rendered explainer
superseded/          Unpublished historical and audited precursor packages
```

## Historical status

Paper III had no preceding formal public release. The earlier repository-local
v1.0 package is retained at
[`superseded/unpublished_local_preprint_v1.0/`](superseded/unpublished_local_preprint_v1.0/)
as historical material; it is not represented as a prior official release.

The manuscript and audits do not constitute human peer review. Negative
literature-search conclusions are limited to the sources actually examined.

## License

The manuscript and explanatory materials are released under CC BY-NC 4.0.
The Lean development depends on Mathlib and retains applicable upstream license
notices.

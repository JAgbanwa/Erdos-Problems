# Paper III v1.5 changelog

Baseline: unpublished, externally audited `preprint_draft_v1.4`.

Paper III v1.5 is the paper's first formal public preprint. It does not
supersede a prior formal Paper III release. The repository-local v1.0 package
and the audited v1.4 draft are retained as unpublished historical packages.

## Protected editorial clarifications

- Theorem 2.2 now states explicitly that the bipartite graph is simple,
  matching Theorem D.3 and the simple gain graph used in Section 7.2. This
  closes external note `EXT-V14C-N02` without changing the intended domain of
  application.
- Appendix D now states explicitly three standard facts already used by its
  proof: hereditary kernel-perfectness under induced subdigraphs; maximum
  degree two of the two-color subgraph, which makes the alternating component
  a well-defined simple path; and induction over bipartite graphs whose maximum
  degree is at most the fixed bound. These additions close external note
  `EXT-V14C-N03` without changing the proof strategy or conclusion.

The external v1.4 challenger independently checked the substance of these
clarifications and classified them as notes rather than proof defects.

## Release and status corrections

- Canonical manuscript filenames were promoted from
  `PAPER_III_preprint_draft_v1.4*` to `PAPER_III_preprint_v1.5*`.
- Front matter now records the completed independent Lean reproduction,
  external adversarial `PASS`, corpus-bounded novelty boundary and absence of
  human peer review.
- Stale pre-release language in Sections 11.6 and 13 was replaced by the exact
  completed build and audit status.

## Header and artifact corrections

- The Markdown author block remains once for GitHub readability.
- The Markdown-to-LaTeX generator now begins body conversion at the series
  metadata boundary, so the template's centered `\author` block is not repeated
  below `\maketitle`.
- PDF metadata now records `Juan Pablo Traverso Gianini` instead of the literal
  placeholder `AUTHORBLOCK`.
- English and Spanish LaTeX and PDF artifacts were regenerated from their final
  Markdown sources using the established series template.

## Formalization

- No Lean source changed.
- The frozen archive remains `PAPER_III_lean_v1.4_freeze.zip`, SHA-256
  `79ee24c38fd776bc2585a0c3c996e30817f0829fc5064463bdbde0fa2d3d7104`.
- The v1.4 internal audit, independent uninterrupted build, axiom checks,
  mathematical rederivations and final external challenger `PASS` carry forward
  on the unchanged surfaces by exact byte identity.

## Public package

- Added a current bilingual four-level HTML explainer with links to the v1.5
  manuscripts and the preserved v1.4 audit evidence.
- Added a release README that explains the v1.4-to-v1.5 audit-continuity
  boundary and links the internal audit, independent Lean reproduction and
  final external challenger report.
- Preserved the audited v1.4 package and repository-local v1.0 precursor under
  `superseded/` without rewriting their reports.

No definition, mathematical constant, displayed formula, proof architecture,
canonical Lean declaration, source file or axiom footprint changed in v1.5.

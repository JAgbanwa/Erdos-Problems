# Paper IV — version 1.2, English review candidate

**State: EDITORIAL_DRAFT_WITH_OPEN_GATES. Not a release or an audited manuscript.**

Read **PAPER_IV_preprint_v1.2_en.md** first. This is the only manuscript submitted for review in this iteration. The title, abstract, introduction, fixed-defect and sublinear extensions, comparison with prior work, and source-status account have been updated.

The next step is the author's review of that English Markdown. Spanish synchronization, TeX/PDF production, visual inspection, new internal validation and external adversarial review are deferred until that review. No publication is authorized by this folder.

## Review materials

- V1.2_EN_REVIEW_REPORT.md: editorial decisions, semantic changes and remaining gates.
- V1.2_CLAIM_MAP.md: new statements, historical frozen sources and separately validated integration additions.
- EN_REVIEW_CHECKS.json: mechanical baseline and Markdown checks.
- PROTECTED_BASELINE.json: protected mathematical elements indexed before editing.
- check_en_review.py: reproducible static checks; it does not compile Lean.

The local baseline actually used is the preserved v1.0.1_candidate English Markdown. The author's reference to an internally reviewed v1.1 is not treated as an audit certificate for v1.2.

## Prepared files that are not deliverables yet

The Spanish Markdown and copied templates, builders and figures are staging materials. The Spanish text is not synchronized with the final English revision. Template metadata and the typeset presentation must be reviewed before any builder is run. Do not treat these files as a complete bilingual edition. No v1.2 TeX or PDF has been generated.

## Lean authority

The historical source freeze is piv-stability-fe9bb18343da. Its combined local build and selected axiom checks passed. The editor-feedback pass additionally integrates E35 and a new public Theorem C adapter in C:/Users/jtraverso/e81p4/clean_stability_build_20260928, with separate incremental validation. The historical frozen sources remain unchanged. Their record is:

../../04_integrity/FREEZE_piv-stability-fe9bb18343da.json

The new source-and-manuscript pair still needs its own audits. Historical reports and the earlier manuscript remain untouched.

Proposition 6.4a now states and proves the square-root obstruction for distance to the entire optimal-size family. Its Lean module and six-declaration axiom/cone audit passed locally in build-logs/optimal-template-obstruction-20260929/lean-r4. This closes the requested formalization, not the pending freeze and publication audits. The earlier frozen tree remains untouched.

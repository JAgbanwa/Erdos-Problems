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
- V1.2_R3_EDITORIAL_REPORT.md: latest review decisions and the two restored addition signs.
- R3_REVIEW_CHECKS.json and R3_MANUSCRIPT.diff: exact four-edit comparison and operator-regression checks.

The local baseline actually used is the preserved v1.0.1_candidate English Markdown. The author's reference to an internally reviewed v1.1 is not treated as an audit certificate for v1.2.

## Prepared files that are not deliverables yet

The Spanish Markdown and copied templates, builders and figures are staging materials. The Spanish text is not synchronized with the final English revision. Template metadata and the typeset presentation must be reviewed before any builder is run. Do not treat these files as a complete bilingual edition. No v1.2 TeX or PDF has been generated.

## Lean authority

The selected local source freeze is **piv-v12-fb459343d234**:

- Source tree: `../../05_formalization/lean_piv-v12-fb459343d234/`.
- Freeze record: `../../04_integrity/FREEZE_piv-v12-fb459343d234.json`.
- Evidence: `../../03_reproducibility/build_piv-v12-fb459343d234/`.
- 607 Lean modules, 19 freshly executed targets, 224 exports;
  461 printed standard-axiom records.
- One audit command: `python tools/audit_publication.py`, with the existing
  pinned dependency cache attached as described in docs/PUBLICATION_AUDIT.md.

The cut includes E35, the explicit public Theorem C and the square-root
obstruction. Exactly five superseded unused modules were retired. The historical
cut piv-stability-fe9bb18343da and all earlier evidence remain unchanged.

## Second-review editorial changes

See V1.2_R2_EDITORIAL_CLOSURE.md and R2_STRUCTURAL_MAP.json. The static check
preserved all 201 displays modulo labels and all five Lean blocks. The new
Figure 4 explains the proof of C′; that proof stays in the main body.

## Mathematical-exposition review O1–O5

The English v1.2 manuscript now includes Appendix E.4 (the five retained
accounts), Lemma F.3a and Corollary F.3b (clique recovery), the three-case
pinned-sample assembly in F.5, and the rooted-defect justification for
Proposition 6.3a. The notation distinguishes exception count t_W, phase-I
triangle count t_I, and additional core displacement r.

See V1.2_O1_O5_EDITORIAL_REPORT.md for the correspondence and limitations.
The preserved input is in review_history/before-o1-o5-20260929/.
The checks retain all 201 old displays after the documented scoped renaming,
all five Lean blocks and all 31 indexed result blocks; the expanded text has
227 displays. All 615 frozen source entries and the archive identity still
match. No Lean file or build result was changed.

Run check_en_review.py and check_o1_o5_revision.py for the static checks.
These checks do not replace an independent review of the added proofs.

The third review restores two omitted addition signs in E.4 and F.12,
uses the sufficient non-strict light-clique bound, and qualifies the reference
to Proposition D.1. Run check_r3_revision.py as well. The previous manuscript
and checks are preserved in review_history/before-r3-errata-20260929/.
The current manuscript identity is recorded in R3_REVIEW_CHECKS.json.

This is a local source freeze, not a frozen bilingual manuscript or an internal
or external audit PASS. After English approval: synchronize Spanish, generate
and inspect both typeset versions, identify that pair, then repeat the audits.
No GitHub publication, tag or deposit has been made.

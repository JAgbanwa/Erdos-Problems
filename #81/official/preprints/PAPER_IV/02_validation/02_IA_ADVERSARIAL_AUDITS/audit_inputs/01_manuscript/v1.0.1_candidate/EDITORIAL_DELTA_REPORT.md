# Paper IV v1.0.1 — editorial handoff r3

Date: 28 September 2026. Stage: corrected candidate for renewed external
adversarial review. Editorial verdict: **EDITORIAL_DRAFT_WITH_OPEN_GATES**.
Disposition: **RETURN_TO_AUDIT**. Preparation is not publication clearance.

## 1. Authority and identity

The author authorized corrections to external cycle r2 and supplied further
attribution comments. Public manuscript version remains **1.0.1**; handoff
revision becomes **r3**. Internal labels 1.0.2/1.0.3 remain historical reviews.
The public draft is still v0.8; no push, tag, deposit or release was performed.

The r2 external verdict remains **FAIL** for F-01 attribution. It stopped
before E4 and does not certify an external Lean build or axiom check.
Its run and sealed report remain unchanged. The old manuscript ZIP and
protocol were preserved under
`C:/Users/jtraverso/e81p4-editorial-history/20260928_pre_external_audit/protocol_r2/`.
The detailed finding response is
`../../04_integrity/revision_r3/AUTHOR_RESPONSE_r2.md`.

The Lean cut remains **piv-v1.0-f1769273dd2c**. No Lean source, dependency
pin or proof was changed; no Lean build ran in this editorial correction.
The main source, annex and author-side internal audit retain their hashes.
The author-run 504-module/13-target/195-export evidence is not an external PASS.

The mathematical-paper-editor skill governed semantic protection and
bilingual synchronization; the PDF skill governed generation and visual QA.
Existing series templates and local Pandoc/Tectonic were reused.

## 2. Corrections and mathematical boundary

| Location/finding | Correction | Limit |
|---|---|---|
| Abstract, introduction, Theorem C, §8.1 / F-01 | Explicitly credit [15, Theorem 1.1] for the fixed-defect class, target and unrestricted eventual maximum; credit its definition/notation and attaining family | No claim of a new extremal formula |
| Theorem C and §8.1 | Present the order-at-most-four upper bound as a strengthening of the stated unrestricted conclusion, with an independent formal proof | Does not assert that the method in [15] cannot be adapted |
| Abstract and Theorem C / D.2 | Order three fails uniformly already for s=0 | Not a minimality claim for every positive fixed defect |
| §8.1 | Trace the accuracy-dependent L through [15, Theorem 3.3, Lemma 3.4, Theorem 1.3, Proposition 5.4 and Theorem 1.1]; distinguish the separate L=4 approximation (1.5) | Source comparison, not a new impossibility result |
| Introduction, new [21] / F-03 | Credit Cipollini's announced subquadratic-error bound | Announcement checked in the preserved primary forum snapshot; linked proof not independently audited |
| Appendix A.2 / F-02 | List seven groups not fully developed in prose | OPEN independent-rederivation/exposition obligation; disclosure is not a proof |
| §7, builders / F-06 | Monospaced formal identifiers and visible continuation arrows at line breaks | Arrow is a typesetting marker; literal source spelling retained |
| English MD / F-07 | Remove stray Needspace command | Layout-only change |
| Table 7 / F-09 | Include SplitCompleteSharpValue alongside mixed_gap_zero for Proposition 6.3 | Mapping clarification, not a new theorem |
| §7 / F-12 | Correct reference to lean/FORMALIZATION_STATUS.md | Document path, not a declaration |
| Front matter / audit state | Record r2's pre-build attribution stop and renewed review | No claim that the external review passed |

The primary text of [15] was checked at
https://arxiv.org/html/2609.20871v1. Its localization chooses L depending on
accuracy; the explicit L=4 use following Theorem 1.3 concerns (1.5).
This supports a comparison of the stated conclusions, not historical
priority or a limitation of every possible adaptation of [15].

Cipollini's announcement was checked in r2's retained primary HTML:
proof-claim-201, 10 August 2026. Fresh forum/Overleaf retrieval was unavailable
during this response; [21] identifies the announcement and linked manuscript
without asserting proof validation. E7 must independently recheck all this.

## 3. Protected elements and bilingual parity

`check_editorial.py` compares both final sources to retained v1.0 and
records hashes in `PROTECTED_ELEMENTS.json`. Complete diffs are retained.

| Check | EN | ES |
|---|---:|---:|
| Displayed mathematical blocks unchanged | 158 | 158 |
| Code blocks unchanged | 5 | 5 |
| Body headings unchanged | 67 | 67 |
| Formal declaration identifier set unchanged | PASS | PASS |
| Equation tags and translation-aware display parity | PASS | PASS |

The identifier checker now excludes document extensions on both sides:
its former regex treated FORMALIZATION_STATUS.md as a Lean name. The sole
initial apparent identifier deletion was that file path; correcting its
prefix is the authorized F-12 edit. No declaration was removed or renamed.

The changed attribution, piece-size qualification, D.2 scope, seven-item
disclosure and audit status were compared across languages. The numbered
theorems, proof blocks, equations, constants and Lean excerpts were not
altered. Protected-block equality alone is not a proof of semantic
correctness; E1/E2/E3/E6 remain independent audit obligations.

## 4. Final artifact checks

Both existing builders regenerated TeX from final MD and compiled the
delivered PDFs with two TeX passes and exit zero. The logs name the correct
outputs. No new engine, Mathlib or dependency installation was made.
There are no detected TeX errors, missing glyphs, undefined references,
overfull boxes or off-page text spans. Nonfatal Fontconfig advisories and
underfull-box warnings remain recorded in the complete logs.

| Edition | Pages | Final rendered evidence |
|---|---:|---|
| English | 52 | qa_en/page_*.png and nine contact sheets |
| Spanish | 53 | qa_es/page_*.png and nine contact sheets |

All **105 pages** were rendered after the final PDF and visually inspected
in contact sheets. Readable-size inspection additionally covered EN pages
1–4, 25, 30, 34, 36, 52 and ES pages 1–4, 26, 31, 35, 37, 53: title/status,
abstract, attribution, Theorem C, formal identifier wrapping, comparison,
declaration table, F-02 list and the new reference. No collision, clipping,
missing symbol or ambiguous identifier continuation was observed in those
checks. This is author-side visual QA, not the external E6 verdict.

The original series A4/11-point layout, margins, fonts, numbering and
figure treatment were retained. Pagination changed; no old page-level
verdict is silently applied to the new PDFs. A first failed typesetting
attempt for continuation arrows is retained under revision_r3; the corrected
hbox discretionary is the one in the delivered builders and successful logs.

## 5. Binding and deliverables

After final checks, MANIFEST.json and MANIFEST_SHA256.md bind deliverables,
builders, templates, figures, logs and rendered QA. Generated AUX/XDV files
are compiler intermediates, explicitly excluded from the deliverable ZIP.
The source ZIP and separate annex remain independent artifacts.

The r3 target binds the new manuscript ZIP and six manuscript files,
unchanged Lean evidence, immutable r2 audit package, author response,
input allowlist and mandate. The read-only intake verifier checks bytes
and archives, not mathematics. Publication-wide historical manifests are
not presented as manifests for these new bytes.

## 6. Remaining gates

- F-01 is corrected in the text but only the new auditor may close it.
- F-02 remains OPEN: seven derivations are summarized, not newly expanded
  here. The next reviewer must record sources, hypotheses, decisive steps
  and completion for each. A successful build cannot alone yield E2 PASS.
- The r3 external review has not started; no model/service was contacted.
  Prefer a second family for E7/E2, or disclose the remaining overlap.
- Recheck E0/E7/E6 and affected semantics; complete Certo and E8 review.
  Full isolated Lean build remains last, after a no-blocker checkpoint,
  reusing the existing pinned Mathlib installation.
- No human peer review, universal b=0, practical threshold or bibliographic
  novelty is certified by this preparation.
- Concept DOI remains 10.5281/zenodo.21273143; no release DOI, commit or
  publication date was invented.

The corrected target is prepared for renewed scrutiny, not declared valid
by its own editor.

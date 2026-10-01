# Paper IV v1.23 — editorial changes from published v1.22

Prepared and approved for GitHub publication on 1 October 2026. Baseline: tag `paper-IV-v1.22`,
commit `cfcd5cf57cadc8583a218caaa1476911efe6158a`.

## Manuscripts

1. Replace the administrative opening block with version and date, in ES/EN.
2. Consolidate audit-status prose in §7; place the round-by-round record in
   this package's README and the unmodified audit reports.
3. Update §7.1 to identify the actual published baseline and preserve the
   series concept DOI in the availability section rather than on the cover.
4. Remove obsolete review-stage narration from A.1, A.2 and F.4, preserving
   the distinction between formal checks, prose assessment and human review.
5. Regenerate both TeX/PDF editions and check their new pagination.

The title, abstract, every theorem, definition, assumption, quantifier,
constant, equation, proof step, mathematical reference and Lean source are
unchanged. The administrative-only delta is recorded paragraph by paragraph
in [ADMINISTRATIVE_DELTA.json](02_validation/03_EDITORIAL_CHECKS/v1.23/ADMINISTRATIVE_DELTA.json).
No new Lean build is necessary or claimed: both versions use exactly
`piv-v12-fb459343d234`, with its existing verified build evidence.

## Explanatory and repository material

- Add a bilingual Paper IV explainer: overview and four levels (intuition,
  statements, proof and evidence), following the series' existing concept.
- Add a static series landing page linking all four explanations. Prepare
  a replacement for the repository's Paper-I-only homepage URL and outdated
  description; do not change remote settings before publication approval.
- Add an English translation of the final v1.22-r4 audit report, outside
  the sealed audit run. The Spanish original remains authoritative.
- Update package/series READMEs, citations, version metadata and hashes.
- Preserve published v1.22 as audit backing, and v0.8 as superseded. Do not
  expose intermediate manuscript candidates as alternative current editions.

## What the inherited PASS means

The consolidated external verdict remains **PASS for v1.22-r4, E0–E8**.
The new editorial checks establish the documented delta and source identity;
they are not a new external mathematical audit, a Lean kernel replay, or
human peer review. See [EDITORIAL_REPORT.md](02_validation/03_EDITORIAL_CHECKS/v1.23/EDITORIAL_REPORT.md).

## Administrative record moved from the manuscript

v1.2 and v1.21 recorded INCONCLUSIVE overall pending exposition; v1.22-r1
recorded PASS with minor findings, r2 PASS_WITH_OBSERVATIONS, r3
PASS_WITH_FINDINGS, and r4 PASS after NEW-05 was closed. Historical reports
retain their original labels and limitations. E4 reuses the verified external
v1.2 build by unchanged source identity; r4 ran no new build.

The v1.22 opening described r2/r3, before the final r4 verdict. That text is
preserved byte-for-byte in the baseline backup, not silently corrected there.
The series concept DOI remains `10.5281/zenodo.21273143`. After editorial
preparation the author supplied version DOI `10.5281/zenodo.23089131`.
It is added to the repository README and citation metadata, not to the
approved manuscript bytes. Its public record was not yet available at the
1 October 2026 check; no completed Zenodo deposit is asserted by this release.

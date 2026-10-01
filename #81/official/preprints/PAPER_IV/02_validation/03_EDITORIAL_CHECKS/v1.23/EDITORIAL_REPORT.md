# Paper IV v1.23 — editorial revision report

Date: 1 October 2026. Editorial stage: author review before publication.
Verdict: **EDITORIALLY_READY** within the administrative-only scope below.
This is an author-side editorial check, not a new external audit or Lean build.

## Purpose and protected content

The author requested that the manuscript no longer open with its audit-cycle
history. The published v1.22-r4 manuscript is the protected baseline.
Six administrative passages per language changed: front matter, verification
status, repository information, the audit-command explanation, A.2 scope and
the F.4 evidence paragraph. The full before/after text is retained in
`ADMINISTRATIVE_DELTA.json` and four source diffs.

No theorem, definition, hypothesis, formula, constant, proof argument,
bibliographic entry, figure or Lean source was changed. The title and abstract
are unchanged. The semantic lock records 994 untouched Markdown paragraphs;
an additional check reconstructs the exact allowed Markdown delta and checks
the TeX paragraphs independently. It compares inline/display mathematics,
fenced code, headings, figures, bibliography, labels and environments.

## Bilingual and typesetting checks

The twelve changed passages were compared pairwise. Both languages preserve
the same source identity, the v1.22-r4 E0–E8 verdict, the distinction between
inherited formal evidence and a new audit, and the separate human-review
milestone. ACCEPTABLE_SUMMARY and the C.2 second-moment exposition limitation
remain explicit. No historical failed or inconclusive verdict was rewritten.

Both PDFs were generated from the delivered TeX using the existing cached
Tectonic engine, serially. No installation or dependency download was used.
`TYPESETTING.json` binds the TeX and PDF hashes; its initial PENDING visual
flag is superseded by this completed review, not silently rewritten.

All 71 English and 73 Spanish pages were visually inspected as rendered
contact sheets. Readable-page inspection covered the new front matter,
verification/repository passages, A.1/A.2 and F.4, including the adjacent
tables and formal statement excerpts. Figures, proof pages and references
were inspected in the page survey. No clipping, missing glyph, broken figure,
blank page or overlapping text was found. The logs contain no overfull box,
undefined reference or missing-character error. Nonfatal underfull-box and
Fontconfig diagnostics remain in the retained logs; the explicit local fonts
render correctly. English pagination changes from 72 to 71; Spanish remains
73 pages. Existing cross-references are by section/equation, not fixed pages.

## Website and report translation

The new series `index.html` replaces the Paper-I-only orientation. It links
the four original/current packages and explains the historical context of the
older pages. The Paper IV companion provides an overview and four depths,
in English and Spanish. Its claims distinguish all-order and eventual bounds,
fixed and growing defect, formal verification and human peer review.

Browser checks exercised 20 Paper IV combinations: two languages, five depth
panels and desktop/mobile widths. No script error, missing image, horizontal
page overflow or external resource request occurred. Screenshots were inspected
for the landing page, overview and mobile results. Local target files are
checked separately. GitHub Pages is not enabled by this work. The prepared
repository homepage must be applied only after the new index is public.

The English consolidated audit report is an explicitly labelled translation
of v1.22-r4, retaining all eleven numbered sections, literal code tokens and
full hashes. The Spanish original, PDF and signed-off package remain unchanged.
The translation is not attributed as a new statement by the auditor.

## Identity and limits

The 615-entry main source manifest is unchanged, as are the separate annex
and original audit packages. The external PASS remains the v1.22-r4 verdict;
the present report does not extend that auditor's attestation to new document
bytes. The v1.23 identity is bound separately in the publication manifest.
Exact v1.22 artifacts are retained under audit inputs and in the published tag.
Papers I–III are unchanged. No Lean compilation was invoked.

No open mathematical content query was introduced. This is not a new
literature review, priority determination, human peer review or universal
mathematical test. Publication, remote homepage changes and a Zenodo version
deposit await the owner's decision. No new version DOI or release commit is
asserted.

## Reproducible records

- `SEMANTIC_CHECKS.json`: exact delta, protected content, PDF bindings and source identity.
- `TYPESETTING.json`, `compiler_*.log`, `tex_*.log`: final compilation evidence.
- `WEB_CHECKS.json`: browser cases and network/error checks.
- `../../translations/v1.22_r4/TRANSLATION_CHECKS.json`: translation/source identity.
- `../../../04_integrity/PUBLICATION_CHECKS.json`: final local packaging controls.

Checks still belonging to the author: approve the presentation and authorize
publication; assign and record a version DOI only if a new deposit is created.

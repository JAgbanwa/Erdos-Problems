# Paper IV v1.2 — bilingual production and manuscript freeze

**Editorial verdict: EDITORIAL_DRAFT_WITH_OPEN_GATES.**
**Production state: STYLE_MATCHED_REVIEW; prepared for renewed internal audit.**
**Date: 29 September 2026.** This is an author-side editorial check, not an
independent mathematical audit, a new Lean build or publication approval.

## 1. Authority and changes

The semantic authority is the author's approved English v1.2, preserved in
`review_history/before-bilingual-20260929/PAPER_IV_preprint_v1.2_en.md`
(SHA-256 `7881b035b73cac09ad84da55090002788cd7da8cae238baa0c742ed6d71f5298`).
No theorem, hypothesis, constant, equation, proof step or literal Lean block
was changed in the English mathematical text.

The four English differences are recorded in BILINGUAL_APPROVED_EN.diff:

1. Status now records bilingual production while keeping renewed audits pending.
2. The C′ diagram's explicit caption number is 3, its order of appearance.
3. The later comparison refers to Figure 4, not Figure 3.
4. Appendix A.1 points to the selected source manifest rather than its predecessor.

The Spanish edition was synchronized with the approved English. Existing
reviewed translations were reused where applicable; changed and new paragraphs
were translated editorially with mathematical spans and literal code protected.
The final comparison corrected three stale reused passages: the abstract,
the removal-based explanation of uniform localization, and the scope of Table 6.
Those corrections restore equivalence with the English rather than change
the approved mathematics. The two restored addition signs from r3 remain intact.

The mathematical-paper-editor protocol governed semantic locking, translation,
the distinction between recorded formal verification and manuscript audit,
and final artifact sealing. No new mathematical result was created in this pass.

## 2. Typesetting and series fit

Layout authority: Paper III v1.5, in
`../../../PAPER_III/01_manuscript/PAPER_III_preprint_v1.5_en.tex` and its PDF,
with the existing Paper IV series templates retained.

The comparison covered reference pages 1, 6, 12, 19 and 46: title/metadata,
figure and table, theorem, proof, and bibliography. The shared format is
11-point article, A4, one-inch margins, Latin Modern body typography,
centered title/author, compact status block, bold result/proof headings,
unnumbered LaTeX sections carrying explicit manuscript numbers, paragraph
spacing, centered figures/tables, blue links, and numbered manual references.
Paper IV retains Latin Modern mono rather than Paper III's Cascadia Mono.
Its denser prose and smaller long tables are deliberate existing choices.
This is a series adaptation, not a claim of byte-identical preambles.

Both delivered PDFs were compiled from their delivered TeX using the existing
Tectonic runtime (XeTeX), with two TeX passes, and rendered using PyMuPDF.
Pandoc converts the body only; the series templates determine the document.
No additional TeX installation or Mathlib installation was made.

Presentation fixes include the C′ glyph, visible continuation marks on long
Lean identifiers and hashes, a safe break in the E.2 inline formula paragraph,
and one integrated caption for Figure 3 instead of a duplicate caption.
The four figures retain their mathematical content. The new Spanish C′ figure
uses the same geometry as its English counterpart.

## 3. Final checks and visual coverage

ARTIFACT_CHECKS.json records PASS_ARTIFACT_CHECKS, narrowly scoped to:

- 486 corresponding paragraph blocks, matching heading hierarchy and equation
  labels, four figures in each language;
- 227 English displayed equations and five unchanged literal Lean blocks;
- protected inline/display mathematics and code unchanged from the approved
  English, apart from the documented manifest locator;
- no protected-token discrepancy between languages after the declared
  translation of words inside mathematical text;
- final PDF/TeX ordering, two-pass compiler output and render-to-PDF hash binding;
- zero final overfull boxes, missing glyphs, fatal errors or undefined references;
- unchanged source manifest, all 615 source entries, source ZIP and recorded
  evidence files, together with the recorded successful combined-build summary,
  607 result entries and the 19 freshly executed targets.

This does not reprove the statements or replace a semantic Lean audit.
The existing build has 19 freshly compiled modules and 588 validated cache
hits; it must not be described as 607 fresh compilations.

Final PDFs: **English 68 pages; Spanish 69 pages**. All pages were inspected
on final contact sheets after the last correction. Full-resolution inspection
included EN pages 1, 7, 26, 38, 40, 54, 62 and 68; ES pages 1, 26, 36, 39, 63
and 69. This covers title/status, the proof map, same-root diagram and theorem,
source tables, literal Lean, corrected E.2 line, adapted-removal table and
references. The reference comparison and additional pre-final inspections
were not substituted for final contact-sheet review.

The compiler retains 11 underfull-box warnings in English and three in Spanish,
principally identifier-heavy prose. The inspected output is readable and these
are not content-loss or overflow warnings. A Fontconfig default-configuration
notice is preserved in both console logs. Font resources are embedded, including
Type 3 glyph procedures used by the existing vector figures. No missing-glyph
warning or visual substitution was found.

## 4. Freeze and evidence boundary

The manuscript manifest and its archive identify this exact bilingual edition.
MANUSCRIPT_FREEZE.json records the computed identity, archive hash and immutable
link to Lean cut `piv-v12-fb459343d234`. It is a local artifact freeze,
not a Git commit, release tag, Zenodo deposit or public release.

The Lean cut is unchanged: 607 modules, 19 targets, 224 export checks and 461
printed standard-axiom records. The selected sources include the explicit
E34/E35 chains and the square-root obstruction. The records do not constitute
461 distinct theorem claims. Historical source cuts and their evidence remain
preserved. The source ZIP and manuscript ZIP are separate; caches, credentials,
working-tree branches and unrelated research are not copied into the manuscript ZIP.

No new internal or external adversarial audit has run on this manuscript pair.
No claim of current bibliographic priority or new literature search is made.
Appendix A.2 still identifies derivations summarized rather than fully expanded
in prose. These and all new public claims must be checked in the next audit.

## 5. Next action

Use NEXT_INTERNAL_AUDIT_SCOPE_v1.2.md with the existing internal standard,
starting with the exact hashes in MANUSCRIPT_FREEZE.json. Open a new audit
execution directory. Retain the prior verdicts as history only. Do not start
another full build by default or install another Mathlib.

### Research status checklist

- Plan activo: preparar y sellar los manuscritos bilingües v1.2.
- Resultado: MD, TeX y PDF ES/EN sincronizados, revisados e identificados.
- Estado matemático: contenido inglés aprobado conservado; no nueva prueba.
- Dependencias: corte Lean identificado y herramientas locales existentes.
- Pendiente: nueva auditoría interna y después auditoría externa adversarial.
- Siguiente acción: ejecutar la auditoría interna cuando lo solicite el autor.

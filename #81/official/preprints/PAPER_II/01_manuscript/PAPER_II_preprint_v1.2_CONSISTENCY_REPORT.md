# Paper II v1.2 artifact consistency report

**Status:** PASS — release-promotion artifact validation.

## Method

1. Treat the English Markdown manuscript as semantic authority and preserve theorem statements, constants, equations, citations and Lean identifiers.
2. Prepare and editorially review the Spanish translation for mathematical sense; do not rely on a deterministic translation library.
3. Generate the English and Spanish LaTeX sources from their language-specific Markdown files using the established series template.
4. Compile each final LaTeX source twice with LuaLaTeX; generate each PDF only from its checked-in `.tex` source.
5. Compare EN/ES heading hierarchy, figures and protected identifiers, then inspect extracted PDF text.
6. Require zero fatal compilation errors, missing glyphs, overfull boxes and undefined references.
7. Render and visually inspect every page with Poppler for clipping, blanks, broken tables, missing figures and layout discontinuities.
8. Verify embedded fonts and seal the six manuscript artifacts with an LF-only SHA-256 sidecar.

## Results

- Markdown headings: EN 52; ES 52; hierarchy aligned.
- Figures: EN 3; ES 3; order aligned; all files present.
- Protected Lean/code identifiers: EN/ES sets aligned.
- PDF pages: EN 24; ES 24.
- PDF fonts embedded: EN yes; ES yes.
- Final second-pass logs: zero fatal errors, missing glyphs, overfull boxes and undefined references in both languages. The inherited Cascadia Mono shape-substitution warnings and harmless underfull boxes do not alter content or margins.
- Full-page visual inspection: PASS.
- All 48 final pages were rendered after the final PDF build and visually inspected, including the four release-status first pages at full resolution.
- Normalized prose-duplication scan (paragraphs of at least 180 characters): EN 0; ES 0.
- The delivered v1.2 freeze, its exact archive hash, the main build log and the supplementary build log are synchronized across MD, TeX and PDF.

## Scope note

This release promotion changes only the version/status language and the two reproduction-status sentences made current by the completed audit, together with associated public-package metadata. It does not change any theorem statement, formula, proof, citation, figure, Lean source or frozen Lean archive. The v1.2 manuscript and the unchanged formal archive passed the recorded independent clean-room reproduction and external adversarial review. This report does not claim human peer review, specialist priority determination or a new Lean rebuild.

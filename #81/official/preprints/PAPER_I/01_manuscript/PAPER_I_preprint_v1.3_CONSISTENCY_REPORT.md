# Paper I v1.3 artifact consistency report

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

- Markdown headings: EN 33; ES 33; hierarchy aligned.
- Figures: EN 2; ES 2; order aligned; all files present.
- Protected Lean/code identifiers: EN/ES sets aligned.
- PDF pages: EN 19; ES 20.
- PDF fonts embedded: EN yes; ES yes.
- Final second-pass logs: zero fatal errors, missing glyphs, overfull boxes and undefined references in both languages. The inherited Cascadia Mono shape-substitution warnings and harmless underfull boxes do not alter content or margins.
- Full-page visual inspection: PASS.
- All 39 final pages were rendered after the final PDF build and visually inspected, including the four release-status first pages at full resolution.
- Normalized prose-duplication scan (paragraphs of at least 180 characters): EN 0; ES 0.
- The five Spanish blocks identified by the external audit occur exactly once in Spanish Markdown, LaTeX and extracted PDF text.
- The `z=x` accounting for (4.7), the `o>=3` Appendix A.2 condition, the scope of `sharp`, the archive declaration and the axiom namespaces are synchronized across MD, TeX and PDF.
- The obsolete Schrijver pinpoint and stale repository citation are absent; the Chen--Erdős--Ordman scan appears in both languages.

## Scope note

This release promotion changes only the version/status language and associated public-package metadata. It does not change any theorem statement, formula, proof, citation, figure, Lean source or frozen Lean archive. The v1.3 manuscript and the unchanged formal archive passed the recorded independent external adversarial review. This report does not claim human peer review, specialist priority determination or a new Lean rebuild.

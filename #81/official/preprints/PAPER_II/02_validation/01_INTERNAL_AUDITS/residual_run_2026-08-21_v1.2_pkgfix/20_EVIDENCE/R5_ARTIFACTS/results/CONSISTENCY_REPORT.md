# Paper II v1.2 artifact consistency report

**Status:** PASS — internal artifact-production validation; not an external mathematical or adversarial audit.

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
- PDF pages: EN 23; ES 24.
- PDF fonts embedded: EN yes; ES yes.
- Final second-pass logs: zero selected errors or warnings in both languages.
- Full-page visual inspection: PASS.
- The delivered v1.2 freeze, its exact archive hash, the main build log and the supplementary build log are synchronized across MD, TeX and PDF.

## Scope note

This report validates editorial synchronization and artifact generation. It reviews the recorded Lean evidence but does not rerun the full Lean builds, perform independent reproduction, or replace the planned external adversarial audit. The prior-art statement is explicitly an internal assessment.

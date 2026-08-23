# G6 TEX-PDF -- Paper I audit record

**Verdict:** `PASS_AFTER_CORRECTION`

Both language artifacts use the series layout: `article`, 11 pt, A4,
one-inch margins, language-aware Babel, microtype, embedded figures, and
embedded PDF fonts. English has 19 pages and Spanish has 20.

After `P1-IA-002`, the Spanish LaTeX was regenerated from the corrected Spanish
Markdown and compiled twice with LuaLaTeX. The retained second-pass log has
zero fatal errors, missing glyphs, overfull boxes, or undefined references.
All 20 corrected Spanish pages were rendered with Poppler and inspected; no
clipping, overlap, blank page, broken table, missing figure, or malformed code
block remains. All 19 English pages were also rendered and visually inspected.

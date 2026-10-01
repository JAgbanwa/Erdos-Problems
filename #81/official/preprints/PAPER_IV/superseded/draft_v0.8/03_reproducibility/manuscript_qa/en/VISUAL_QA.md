# Rendered QA — English v0.8

Final PDF SHA-256: `f7b1df774585b0356c40f898d1830781d2121a5fc9ab3b7a02d39513964acc50`.

The final PDF contains 40 pages. Every page was rendered after the last source correction and inspected in `contact_1.png` through `contact_7.png`. Readable-scale inspections additionally covered pages 1, 5, 22, 33, and 39: title and abstract, proof map, long source table and audit caveat, marked-selection proof, and references.

This same-version correction replaces only the titles of references [2]–[4] with the titles verified in the English editions of Papers I–III, and renames the English figure assets without changing their numbering or content. Compared with the previous English manifest, 39 rendered pages are byte-identical; only page 39 changes. Its revised reference entries fit within the text block. Report labels are now English. The protected wording in Sections 7–8 and all other bibliographic entries remains unchanged, as verified by reversing the six authorized manuscript substitutions and recovering the previous source hash.

The reference comparison used Paper III v1.5 English: pages 1, 3, 4, 6, and 46. The reference contact sheet and individual renders are retained here. The English edition preserves the series' A4 layout, serif typography, title hierarchy, author block, margins, displayed-equation treatment, restrained figures, and printed URLs. The local v0.8 template remains the immediate layout source; the translation did not adopt a generic standalone converter template.

## Findings

- Figures retain the Spanish geometry and reference numbers. Labels fit inside the boxes; no arrow or label collisions were observed.
- Formula-rich tables remain within the text block. The long module correspondence table is readable and retains its caption.
- Mathematical glyphs and the rendered literal Lean headers are present. The five Markdown Lean blocks remain literal in the semantic source.
- No clipped text, overlapping blocks, missing glyphs, accidental blank pages, or isolated headings were observed.
- The acknowledgments/disclosure page is intentionally shorter because the reference section starts on a new page, as in the source template.
- English wrapping changes page boundaries; matching Spanish page numbers was not requested. Numbered semantic objects remain identical.

Automated companion checks are in `BILINGUAL_PARITY_v0.8.json`. Visual QA does not certify the mathematical correctness of the manuscript.

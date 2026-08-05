# Build

## Manuscript (PDF from Markdown)
```bash
pandoc 01_manuscript/PAPER_II_preprint_v1.0.md \
  -o PAPER_II_preprint_v1.0.pdf --pdf-engine=lualatex
```
(The `.tex` source is also provided for direct typesetting. The Spanish version
uses the `_es` files. Figures are in `01_manuscript/figures/`.)

## Lean formalization
```bash
cd 05_formalization/lean
lake exe cache get      # fetch Mathlib build cache (optional but recommended)
lake build
```
The toolchain and dependency versions are pinned (`lean-toolchain`,
`lake-
# Environment

| Item | Value |
|---|---|
| Host OS | Windows 11 Home Single Language 10.0.26200 |
| Date of run | 2026-08-23 |
| Python | 3.14 (CPython), stdlib only; no random seeds anywhere |
| LuaTeX | LuaHBTeX 1.24.0 (MiKTeX 25.12) — same producer string as the sealed ES PDF |
| pdftotext / pdffonts / pdftoppm | Xpdf 4.00 (Glyph & Cog) |
| Lean / Lake / Mathlib | not invoked in this run; no rebuild requested or performed |
| Long-path mitigation | directory junction `C:\v14c` -> the run directory; `C:\p3v14` -> target |

## Commands of record

    python review_challenger_request.py      # baseline + target hashes, regression boundary
    python v14c_bilingual.py                 # independent bilingual structural comparator
    python v14c_adjudicate.py                # adjudication of the three flagged differences
    lualatex -interaction=nonstopmode es.tex # x2, auditor's own rebuild of the sealed ES .tex
    pdftoppm -r 72 -gray ..._es.pdf pg       # raster margin scan, 47 pages
    pdffonts / pdfinfo                       # embedding and page count

All scripts are included under `20_EVIDENCE/`.

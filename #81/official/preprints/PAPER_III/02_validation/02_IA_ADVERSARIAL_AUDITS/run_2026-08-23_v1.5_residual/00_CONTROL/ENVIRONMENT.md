# Environment and command ledger

| Item | Value |
|---|---|
| Host OS | Windows 11 Home Single Language 10.0.26200 |
| Run date | 2026-08-23 |
| Python | 3.14 CPython, standard library only; no random seeds anywhere |
| LuaTeX | LuaHBTeX 1.24.0 (MiKTeX 25.12) — same producer string as both delivered PDFs |
| pdfinfo / pdftotext / pdffonts / pdftoppm / pdfimages | Xpdf 4.00 (Glyph & Cog) |
| Lean / Lake / Mathlib | not invoked; no rebuild requested or performed |
| Long-path mitigation | junctions `C:\p3v15` -> target, `C:\v15r` -> this run |

## Commands of record

    python v15_E0_intake.py        # hashes, sidecar, ZIP CRC, authorities, superseded state
    python v15_E1_delta.py         # structural invariance + delta containment, EN and ES
    python v15_E1_sections.py      # hunk location by section
    python v15_E3_formal.py        # manifests, archive identity, axiom logs, release claims
    python v15_E3_probe.py         # isolation of the suffix-matching false positive
    python v15_E5_bilingual.py     # bilingual loss/duplication + N02/N03 propagation
    python v15_E5_render.py        # render QA, auditor rebuild, margin scan
    python v15_E6_E7.py            # prior-art regression, release surfaces
    python v15_stale_sweep.py      # generically-named stale evidence copies

    lualatex -interaction=nonstopmode {en,es}.tex   # x2 each, auditor rebuild
    pdftoppm -r 72  -gray  ...   # margin scan, 46 + 47 pages
    pdftoppm -r 130 -png   ...   # visual inspection of title / Thm 2.2 / Appendix D pages

All scripts are included under `20_EVIDENCE/`.

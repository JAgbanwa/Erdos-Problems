# Informe de puerta E6 — run_v1.22_r4 (Paper IV v1.22-r4)

Veredicto actual: **PASS**. Evidencia: `20_EVIDENCE/E6/`. Auditor: Claude Opus 5.5, misma sesión que las ejecuciones anteriores; no se ejecutó Lean.

---

# E6 — NEW-05 and parity (run_v1.22_r4)

## Independent method
`10_SCRIPTS/e6_r4_delta.py` produces `E6_R4_DELTA.json` and `auditor_diff_es_md.diff`. The editor's `check_r4.py` was not run and not trusted.

- **MD.** 2565 → 2565 lines. Changed lines: **only l.1355 (A.2) and l.2356 (F.4)**.
  - A.2: «**la programación numérica** de C.3» → «**el calendario numérico** de C.3». The article agreement also changes, so the edit spans three tokens.
  - F.4: «cota adaptada con **muestra fijada**» → «cota adaptada con **muestras con anclajes**».
- **TeX.** 2367 → 2367 lines. Only l.1317 and l.2159 change, with the same substitutions. The preamble is identical.
- **Editor's diff.** The body of `CHANGES_es.diff` equals the auditor's diff.
- **Protected content r3 = r4.** Identical: displays, inline math, code spans and blocks, tags, headings, bold leads, table rows, images and references.
- **Established terms, r4.**
  - «calendario numérico» appears at l.1355 and l.1599, consistent with the C.3 heading «Un calendario explícito» (l.1638).
  - «muestras con anclajes» appears at l.2356 and in the F.5 heading at l.2403; Table 10 has «Cota de muestra con anclajes» (l.2398).
  - «programación numérica» and «muestra fijada»: 0 occurrences.
- **PDF corresponds to TeX.** ES r4 has 73 pages (xdvipdfmx, 2026-10-01 15:39 UTC). The token diff against r3 has **exactly 2 regions**, the two substitutions, after joining hyphenated words. The three line-break changes declared in `ARTIFACT_CHECKS.json` («conso-lidado», «declara-do», «ve-rifica») are line-wrap effects only.
- **Raster (72 dpi) vs. r3.** Only **pp. 40 and 66** change, matching `ARTIFACT_CHECKS.json`; 71 pages are raster-identical. On pp. 40 and 66 the first line, the last line and the line count are unchanged, so **pagination does not shift**.
- **Visual check.**
  - Side-by-side r3|r4 at 130 dpi (`cmp/`) and the changed paragraphs at 160 dpi (`zoom/`), for pp. 40 and 66. The image was displayed and the row logged at that moment.
  - The new wording is legible, with no overflow; nothing else on those pages changed.
  - The other ES pages (raster-identical) and all EN pages (byte-identical) are **inherited and revalidated by identity** with the run_v1.22_r3 inspection (`PAGE_INSPECTION_LOG.csv`, 145 rows).

## Result
- **NEW-05: CLOSED in r4.**
- NEW-04, X-15 and NEW-01 stay closed: the status paragraphs, prose and `Model` are unchanged apart from the two substitutions.
- Style note, not a finding: «con muestras con anclajes» repeats «con». It is grammatical, and the term matches F.5.

**E6 verdict (r4): PASS.** Executed in r4 for the ES delta; EN inherited and revalidated by identity.

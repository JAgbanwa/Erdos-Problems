# R5 artifact regression

**Verdict:** `PASS_UNCHANGED_ARTIFACTS`

The English and Spanish Markdown, LaTeX and PDF hashes are byte-identical to the
external v1.3 audit anchors. PDFs were therefore not rebuilt. Fresh read-only QA
confirmed A4, unencrypted PDFs with 19 English and 20 Spanish pages, PDF version
1.5 and fully embedded/subset fonts. All 39 pages were freshly rendered at 100
dpi after the package correction; the contact sheets were inspected and show no
blank, duplicated, clipped, missing-figure or collision defect.

Because no semantic source, TeX, PDF or figure changed, regeneration would add
risk without testing either package-only correction.


# R5 -- bilingual and artifact-chain reuse

**Verdict:** `PASS_UNCHANGED_ARTIFACTS`

The package correction did not alter either Markdown source, either LaTeX
source, either PDF or any figure. The six hashes in
`results/PAPER_II_preprint_draft_v1.2_SHA256.txt` verify against the delivered
files and match the external audit anchors.

Prior internal QA, copied into `results/`, records two successful LuaLaTeX
passes per language, zero selected compiler defects, embedded fonts and visual
PASS over 23 English and 24 Spanish pages. The external v1.2 audit independently
rendered and analysed all 47 unchanged pages and found no blank, malformed or
duplicated page.

Because the artifact bytes are unchanged, this residual audit reuses the
post-build and rendered-page evidence. It does not regenerate TeX, PDFs or
figures and does not claim an additional PDF compilation.

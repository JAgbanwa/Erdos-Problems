# Reproducibility — Paper III v1.4

The author-build evidence is retained under
`author_build_evidence/run_2026-08-22_CCS_NOTEBOOK456_resumed/` and copied verbatim into
the formal freeze gate logs. Its SHA-256 manifests verify.

The source-only project began clean. `lake build PaperIII` completed with exit 0 and
8,455 jobs; the query-root build completed with exit 0 and 8,444 jobs; eight axiom files
cover 42 queries over 35 distinct surfaces. The recorded axiom union is exactly
`[propext, Classical.choice, Quot.sound]`, with no `sorryAx`.

Because the desktop application restarted during the first build process, the unchanged
project was resumed. The correct classification is `PASS_CLEAN_ORIGIN_RESUMED`, not an
uninterrupted independent reproduction. The latter remains an external gate.

The manuscript-generation scripts, final TeX logs, 51-check consistency result and
all-page rendered-PDF QA are retained here.

# Reproducibility — Paper III v1.5

The author-build evidence is retained under
`author_build_evidence/run_2026-08-22_CCS_NOTEBOOK456_resumed/` and copied verbatim into
the formal freeze gate logs. Its SHA-256 manifests verify.

The source-only project began clean. `lake build PaperIII` completed with exit 0 and
8,455 jobs; the query-root build completed with exit 0 and 8,444 jobs; eight axiom files
cover 42 queries over 35 distinct surfaces. The recorded axiom union is exactly
`[propext, Classical.choice, Quot.sound]`, with no `sorryAx`.

The resumed author run is preserved as historical evidence. It was followed by an
uninterrupted clean author reproduction and by an independent external clean-room
reproduction. The external run compiled the public root in 8,455 jobs and the query roots
in 8,444 jobs, and reproduced the directed axiom checks. Those results bind to the same
v1.4 Lean archive used by v1.5, whose SHA-256 is
`79ee24c38fd776bc2585a0c3c996e30817f0829fc5064463bdbde0fa2d3d7104`.

The v1.5 manuscript-generation scripts, final TeX logs, 61-check consistency result and
all-page rendered-PDF QA are retained here. No Lean build is rerun for the v1.5 editorial
residual; formal results carry forward only after exact archive and source-tree identity
checks.

Current compiler evidence is version-scoped under `manuscript_build_logs/v1.5/`, and the
current consistency result is `MANUSCRIPT_CONSISTENCY_RESULTS_v1.5.json`. Historical v1.3
compiler logs are retained only under the explicitly labelled
`manuscript_build_logs/v1.3_legacy/`; no generic filename shadows the current evidence.

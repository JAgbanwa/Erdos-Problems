# Paper IV v1.0 — bounded-clique-gap annex

This annex contains the 38 `BoundedCliqueGap` Lean modules cited in §8.2 of the
English and Spanish preprints. It is **separate** from the 504-module main
freeze `piv-v1.0-f1769273dd2c`; in particular, `import PaperIV` does not export
`BoundedCliqueGap.chordal_gap_linear_cliqueFree`, and the annex is not used by
the proof of the main Erdős 81 theorem.

The recorded compilation of these modules is the earlier 579-module
`optimized-clean-all` run, preserved at
`../../03_reproducibility/build_gap_annex_20260927/`. Its `SUMMARY.json` reports
579 passes and no failures. All 38 annex sources match that run's `SOURCES.json`
byte for byte. The annex imports twelve `PaperIV` modules, each byte-identical
between that run and the main freeze. The other modules in the earlier run are
not part of this annex, nor evidence for the main freeze.

`BoundedCliqueGap.AxiomCheck` was compiled in the earlier run; its log records
633 checked declarations and only `propext`, `Classical.choice`, and
`Quot.sound` for the cited theorems. This is recorded-build evidence, not a
second independent rebuild or a human mathematical review.

For reproduction, overlay `BoundedCliqueGap/` on the main source-only freeze,
using its pinned Lean/Mathlib configuration. The two directories are archived
separately so that the main theorem's source and audit identity remain intact.

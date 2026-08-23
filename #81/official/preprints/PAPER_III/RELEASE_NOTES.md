# Paper III v1.5 release notes

Paper III v1.5 is the first formal public preprint release of *Linear-Error
Clique Partitions of Split Graphs via Structured Triangle Packing*.

The paper establishes the conjectured `n²/6 + O(n)` clique-partition scale for
split graphs, with sharp quadratic coefficient `1/6`. This resolves the
split-graph case of Erdős Problem #81; the full chordal-graph problem remains
open.

## Evidence status

The mathematical manuscript and the immutable Lean freeze were audited as the
unpublished v1.4 target. The internal audit closed with `PASS` (144/144 checks),
the external residual audit completed an uninterrupted clean-room build and
mathematical rederivation, and the final external challenger review closed with
`PASS` and no blocker, major finding or open minor finding.

The v1.5 release carries the same Lean bytes. Its protected manuscript delta is
limited to two Appendix D clarifications (`EXT-V14C-N02` and
`EXT-V14C-N03`) whose substance was already checked by the external challenger.
Header, release-status, bilingual-format and PDF-metadata corrections were
regenerated and reviewed as derived artifacts. See `README.md` and
`CHANGELOG_v1.5.md` for the exact evidence links and change boundary.

The v1.5 internal residual audit closed with `PASS` after 79/79 checks,
including byte comparison of all 707 manifested Lean sources, bilingual
duplicate/loss controls, all-page rendered QA and the added control that no
stale generic evidence shadows version-scoped v1.5 evidence. The independent
external residual review confirmed the v1.5 artifact bytes and all substantive
gates. Its sole non-mathematical minor finding, `EXT-V15-M01`, was corrected
without changing the manuscript or Lean archive; the independent closure run
then passed 10/10 checks and issued the consolidated verdict `PASS`. The
release is ready for the public repository commit and tag.

## Review boundary

The audits are independent adversarial AI reviews, not human peer review. The
prior-art conclusion is a negative search bounded by the reviewed corpus and is
not a specialist determination of priority.

## Formal archive

`PAPER_III_lean_v1.4_freeze.zip`  
SHA-256: `79ee24c38fd776bc2585a0c3c996e30817f0829fc5064463bdbde0fa2d3d7104`

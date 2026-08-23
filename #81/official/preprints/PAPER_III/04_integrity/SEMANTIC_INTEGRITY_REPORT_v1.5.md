# Paper III v1.5 semantic-integrity report

**Input baseline:** unpublished, externally audited v1.4 English and Spanish Markdown
artifacts preserved under `superseded/unpublished_audited_draft_v1.4/`.

**Output target:** v1.5 English and Spanish Markdown, generated TeX and compiled PDF.

## Protected delta

| Change | Classification | Disposition |
|---|---|---|
| Theorem 2.2 explicitly says that the bipartite graph is simple | authorized clarification of the intended domain; `EXT-V14C-N02` | accepted; the unique application was already verified to be simple |
| Appendix D states hereditary kernel-perfectness of the remaining induced subdigraph | proof-explication clarification; `EXT-V14C-N03` | accepted; no dependency or conclusion changed |
| Appendix D states induction over maximum degree at most the fixed bound | proof-explication clarification; `EXT-V14C-N03` | accepted; no dependency or conclusion changed |
| Appendix D states the degree-two alternating subgraph and simple-path consequence | proof-explication clarification; `EXT-V14C-N03` | accepted; no parity or recoloring conclusion changed |

The external v1.4 challenger had already checked the mathematical substance of all four
clarifications and classified the omissions as notes, not proof defects.

## Release-only delta

The remaining changes are release status, filenames, exact completed-audit language,
removal of a duplicated generated author block, correction of PDF author metadata and the
updated README/HTML/changelog surfaces. These do not alter mathematical content.

## Invariants checked

- Quantifier changes: none beyond making the already intended simple-graph domain explicit.
- Assumption changes: no new premise in the proof of Theorem 1.1.
- Constants or asymptotic orders changed: none.
- Displayed formulas or equation tags changed: none.
- Theorem order, proof architecture or dependency order changed: none.
- Citation or bibliography sequence changed: none.
- Novelty scope strengthened: no; all absence claims remain corpus-bounded.
- Canonical Lean declarations or formal source bytes changed: none.
- Formal axiom footprint changed: none.

## Derived artifacts

The v1.5 TeX files were regenerated from the final Markdown sources, the PDFs were compiled
from those TeX files, all pages were rendered after the final compilation, bilingual and
duplicate-text checks were rerun, and the six-artifact SHA-256 sidecar was generated last.

**Unresolved content queries:** none.

**Verdict:** `EDITORIALLY_READY` within the internal process; independent external residual
confirmation remains the final release gate.


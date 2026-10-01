# Final internal report — Paper IV draft v0.8

**Verdict:** PASS within the declared internal draft scope.  
**Class:** author-side, non-independent, source/contract/artifact audit.  
**Package date:** 2026-09-21 (America/Santiago).  
**Executable checks:** 82/82.  
**Final-release verdict:** EDITORIAL_DRAFT_WITH_OPEN_GATES.

## Frozen target

The six manuscripts are the unchanged reviewed v0.8 English/Spanish MD, TeX
and PDF files. The source-only ZIP hash is
`4f6ba1b40ace1d926ae5fab7490c4bc0dc3f236dea28640de4cee0166da60afa`.
All 479 source/configuration entries, including 474 Lean sources, match the
frozen archive. The package status is draft, not a claim of external approval.

## Gates

| Gate | Result and limits |
|---|---|
| G0 | Artifact hashes, ZIP CRC, archive safety and extracted identity pass. |
| G1 | Manuscripts and mathematical sources unchanged; printed Lean excerpts match source. |
| G2 | Four bounded integer-accounting regressions through order 1000 pass; an intentionally incorrect coefficient is rejected. These are not universal proofs or a new full mathematical rederivation. |
| G3 | Import closure complete; pinned dependencies and their tracked source state verified; no active sorry/admit/axiom/native_decide/implemented_by/sorryAx token in the frozen Lean sources. |
| G4 | Main Lake build succeeds (8460 tasks, including cached/replayed tasks), all six verification commands succeed, and supplementary imports are explicitly rebuilt and re-audited. |
| G5 | Bilingual formulas match modulo the explicitly enumerated translated text inside six displays; literal Lean blocks and heading structure match. |
| G6 | Final TeX/PDF binding, clean layout logs and original hash-bound visual QA preserved; 41 Spanish and 40 English pages. No PDF regenerated in this packaging step. |
| G8 | Single active draft; no credentials, cached binaries or obsolete research directories in the publication surface. |

G7, independent mathematical/novelty review, is not performed here and is not
assigned PASS. Earlier papers' independent audit reports are not transferred
to this package.

## Formal evidence

The direct main audit prints 83 axiom footprints; the cone audit checks 57
named results. The supplementary audit prints seven footprints. The bounded
library checks 632 declarations and prints five additional named footprints.
Four printed final-contract footprints overlap with the main audit. These
counts must not be added as if they represented disjoint collections.

All queried axiom sets are subsets of `propext`, `Classical.choice`,
`Quot.sound`. Public type-checking examples fix the all-orders additive,
all-orders linear and sharp eventual statements without supplying an
unproved rounding, near-case or LP interface. The definitions printed beside
them expose exact edge coverage, edge disjointness, minimum piece size,
chordality and the integer target.

The source freeze is unchanged before and after the runs. The nine Git
dependencies match their pinned revisions and have no tracked local edits.
The build is author-side and cache-assisted; no independent clean-room
reproduction is claimed. Every command, exit code and log hash is retained.

The namespace veto checks the root namespace `Erdos81`; it does not identify
copied and renamed code. Neither the code's originality nor priority is
deduced from the axiom or namespace audit.

## Findings and corrections in the checking procedure

The first pass ran while the Lean sequence was unfinished; missing future
logs were correctly reported as incomplete rather than silently passing.
Two harness assumptions also required correction: Tectonic records an XDV
output before `xdvipdfmx` writes the PDF, and language-bearing `text` fields
inside six displays differ between translations. The harness now checks the
complete compiler chain and only the explicitly approved text substitutions.
No mathematical source, manuscript, figure or frozen archive changed.

Git's whitespace diagnostic flags preserved CRLF line endings and existing
Markdown hard-break spaces in imported artifacts. These are not silently
normalized: the package uses byte-preserving attributes so that the reviewed
manuscripts and frozen proof sources keep their original hashes.

Repository-wide sealing initially encountered the Windows legacy path-length
limit in an existing Paper III historical archive. Extended-length path access
was added to the manifest reader; the archive was present and was not altered.

The initial result remains in `FIRST_PASS_DURING_BUILD.json`. Warnings about
unused variables or redundant tactics in Lean are retained in the logs.
They are distinguished from errors and `sorry` warnings.

## Publication recommendation

The curated package may be shared as an **author draft**, with the remaining
independent-audit and peer-review limitations stated. This report does not
promote it to the final independently audited status of Papers I–III. The
enclosing public Git commit and package manifest identify the exact draft
offered for subsequent review.

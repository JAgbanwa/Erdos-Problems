# Paper II v1.2 package-residual internal audit report

> **Overall verdict:** `PASS`  
> **Audit class:** internal / author-side / not external  
> **Protocol:** `PAPER_II_INTERNAL_PACKAGE_RESIDUAL_v1.0`  
> **Date:** 2026-08-21  
> **Lean execution:** no  
> **Manuscript/PDF regeneration:** no; all six artifacts are byte-identical

## Target

The audit covers Paper II `preprint_draft_v1.2` after a package-only correction
to the stale integrity directory identified by the external
`PASS_WITH_RESIDUALS` report.

| Anchor | SHA-256 |
|---|---|
| English Markdown | `7215e14bbea8ab2bf208dcdd1efa050cd2b72c997eee2efe504a1e6817c68882` |
| Spanish Markdown | `d0d1df05eb267a51db2ccc100dd9725dcde9b03dbb95c8a730742e357eb0f4dc` |
| English LaTeX | `bb5f76c3ce56dbb0bff11242a3a8787f9c8ba3d9f0ad23973fc2f26cc5fc3cf0` |
| Spanish LaTeX | `d3f0c6301a48d6553ebad222fa685f152119cb61b5efd3e8be55e389f9d606ae` |
| English PDF | `d05c4cab1262357fddd21e4aab399bdb92d5bcf139172897c80595e781049052` |
| Spanish PDF | `d525d02a6e911cb23f7e1f28e1de7648441eccea6de206e76e5321161c86c2db` |
| Lean archive | `ee2d05cc40d943ca92f8f7bf3e5dd83c2692518ddea5e2ca4f7686ccb1ac3895` |
| Previous external report | `1e7afd3e9394bf83beb7e33ce19ff5227072fcd6b0eb3fd21e571329564e3ded` |

The corrected package freeze, excluding external-audit output and this
residual run, contains 200 files and 3,417,038 bytes. The canonical LF-only
manifest has SHA-256
`ddc50d1cb1fd16a788d03738806a381043134f1df7a0262808379892902b96ec`.
The exact manifest construction algorithm is published in the R0 summary.

## External findings

### EXT-PII-M-001 — PASS/CLOSED INTERNALLY

The stale v1.1 integrity directory was replaced. `INITIAL_SOURCE_SHA256.txt`
now contains three present, matching v1.2 paths; `INITIALIZATION_DIFF.md`
documents v1.1 to v1.2; and `README.md` describes the current integrity
perimeter. A current-target sidecar, semantic-integrity report and residual
matrix were added. Both supplied sidecars are LF-only and verify completely.

### EXT-P2-I-001 — NOTE PRESERVED

The external auditor received HTTP 403 from the Erdős Problems page. This is a
nonblocking access limitation, not a manuscript defect. The open-status claim
remains supported by the primary EOZ source verified in the external audit.

## Gate results

| Gate | Verdict | Evidence |
|---|---|---|
| R0 Package correction | `PASS` | 17/17 controls; sidecars, anchors and hygiene pass |
| R1 Static/general | `PASS` | 58/58 canonical static controls |
| R2 Mathematics | `PASS` | 195 LP; 5,000 maximization; 6,667 argmax; 139 atlas; 931 copy; 22 terminal checks |
| R3 Duplicates | `PASS` | zero exact or near duplicate blocks across all six artifacts |
| R4 Formal reuse | `PASS_RECORDED_AND_EXTERNAL_REUSE` | unchanged archive; external 8,063-job build and 16 axiom surfaces; no Lean run |
| R5 Artifacts | `PASS_UNCHANGED_ARTIFACTS` | six unchanged hashes; prior 47-page rendered QA reused |
| R6 Seal | `PASS` | gate manifests, report and audit archive verified and sealed |

## Semantic integrity

No manuscript, theorem, definition, assumption, quantifier, constant,
equation, proof step, citation, novelty claim, translation, figure, LaTeX
source, PDF, Lean source or formal archive changed. The correction affects only
package integrity, audit status and the new residual evidence.

## Verdict

`PASS`. All seven internal residual gates pass. There are zero unresolved
blockers, majors or minors. This author-side result is not human peer review
and does not prove global novelty. A narrow independent external residual
re-audit must close `EXT-PII-M-001` and issue its own plain `PASS` before Paper
II is externally closed.

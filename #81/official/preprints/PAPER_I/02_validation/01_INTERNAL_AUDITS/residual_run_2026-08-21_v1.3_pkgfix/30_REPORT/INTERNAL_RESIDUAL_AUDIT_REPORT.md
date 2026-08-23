# Paper I v1.3 package-residual internal audit report

> **Overall verdict:** `PASS`  
> **Audit class:** internal / author-side / not external  
> **Protocol:** `PAPER_I_INTERNAL_PACKAGE_RESIDUAL_v1.0`  
> **Date:** 2026-08-21  
> **Lean execution:** no  
> **Manuscript/PDF regeneration:** no; all six artifacts are byte-identical

## Target

The audit covers the same Paper I `preprint_draft_v1.3` manuscript and formal
artifacts, with two package-only corrections after the external
`PASS_WITH_RESIDUALS` report.

| Anchor | SHA-256 |
|---|---|
| English Markdown | `f3094b670c93ff622c3f573cdab61bdd0f5d84007f04b1888b364e0183565bea` |
| Spanish Markdown | `57ba967fc2de805b7bbb4cf5f937727bde43c2ada80fa794bcbb5a727db05b8b` |
| English LaTeX | `1a87de70548879ca90a714ec9e1b10c8576b380a749785916e5d59176e479465` |
| Spanish LaTeX | `f83ee709c1168b5b9afe504e6b6a43763bf3bb2a08f674f2031f83670ba9bb56` |
| English PDF | `7d04c47692b613c8d6e2cc4471f0205128b4ae06ca11d581a08d020eb2236db0` |
| Spanish PDF | `3ad16ae86e8fcad358bf964a6ae98ae053b0bde2fdf3140e008cedab78b90c2a` |
| Lean archive | `0181506408644fc1f8872d711de5a98a500f4052aa295bcd6f8c82776694fd3a` |
| External report | `f2ad1605f0a802932c07503bfad429a98b08af26844dd968aad6e3f145aee495` |

The package-fix input freeze contains 219 files and 24,495,011 bytes, excluding
external audit output and this running audit. Its aggregate path/hash-list
SHA-256 is
`402fe23d5538851b290c749927ea75052efadc8c5df5cda5aba5fdbe0495a325`.

## Corrections

### RES-V13-001 — PASS

The active package no longer contains `tmp/internal_report_v1.3/`. No
directory named `tmp`, forbidden TeX scratch extension, zero-byte file or
stray `$o` occurs in the frozen target. The three scratch files were moved
outside the target to a recoverable agent-work location rather than being used
as evidence.

### RES-V13-002 — PASS

`CHANGELOG_v1.3.md` now names `PaperI.assembly_sharp` and
`PaperI.Split.residual_duality`. Each occurs exactly once; the transposed
forms `PaperI.Split.assembly_sharp` and `PaperI.residual_duality` are absent.
The corrected names agree with manuscript Appendix C, `FreezeAxioms.lean` and
the recorded axiom output.

`RES-V13-003` was already closed by the external primary-source verification.
`RES-V13-004` remains a nonblocking NOTE about a third-party expired
certificate; it is not represented as repaired.

## Gate results

| Gate | Verdict | Evidence |
|---|---|---|
| R0 Package corrections | `PASS_AFTER_HARNESS_CORRECTION` | 20/20 final checks; both open MINOR findings closed |
| R1 Static/general | `PASS` | 95/95 canonical static checks |
| R2 Mathematics | `PASS` | 5 identities; 561 boundary; 480 orbit; 99,671 assembly; 1,179 split-LP; 9 sharpness instances |
| R3 Bilingual/duplicates | `PASS` | zero exact/near duplicate blocks across all six artifacts |
| R4 Formal reuse | `PASS_RECORDED_AND_EXTERNAL_REUSE` | unchanged archive; recorded 8,034-job build and 15-surface axiom gate; no Lean rerun |
| R5 Artifacts | `PASS_UNCHANGED_ARTIFACTS` | unchanged hashes; 19/20 pages, embedded fonts, 39 fresh renders inspected |
| R6 Seal | `PASS` | gate manifests, audit archive and sidecar generated last and verified |

## Diagnostic transparency

The first R0 harness run used the wrong base for
`CURRENT_TARGET_SHA256.txt`; the harness was corrected and rerun. An attempted
nested execution of the R1 static script also derived the wrong repository root;
the canonical script location was then used. Neither diagnostic changed the
target. Both final runs pass.

## Semantic integrity

No manuscript, theorem, definition, assumption, quantifier, constant, equation,
proof step, citation claim, figure, LaTeX source, PDF or Lean source changed.
The protected mathematical and formal surfaces therefore remain exactly those
that passed the external v1.3 regression. Rebuilding unchanged PDFs or Lean
would add operational risk without testing either corrected defect.

## Verdict

`PASS`. All seven residual internal gates pass. There are zero unresolved
blockers, majors or minors from the external report. This author-side result is
not human peer review and does not prove global novelty. A final external
residual re-audit must verify the new package target and issue its own plain
`PASS` before Paper I is considered externally closed.


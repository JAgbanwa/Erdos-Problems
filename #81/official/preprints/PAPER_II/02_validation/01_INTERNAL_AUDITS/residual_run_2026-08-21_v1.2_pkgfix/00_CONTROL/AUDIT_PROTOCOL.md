# Paper II v1.2 internal package-residual audit protocol

**Protocol ID:** `PAPER_II_INTERNAL_PACKAGE_RESIDUAL_v1.0`  
**Audit class:** internal; not external adversarial audit  
**Target:** active `preprint_draft_v1.2` after correction of `EXT-PII-M-001`

## Objective

Verify that the package-integrity correction closes the sole external MINOR,
introduces no unannounced target delta, preserves all scientific and formal
anchors byte-for-byte, and leaves Paper II ready for a narrow independent
external residual re-audit.

## Authorized delta

Only these changes are authorized:

1. replacement of stale v1.1 records in `04_integrity/`;
2. addition of a current-target manifest, semantic-integrity report and
   external residual matrix;
3. package status updates and this internal residual-audit evidence.

No manuscript, translation, figure, LaTeX, PDF, Lean source, toolchain,
dependency or formal archive change is authorized.

## Gates

| Gate | Requirement |
|---|---|
| R0 | `EXT-PII-M-001` correction, sidecars and protected anchors |
| R1 | full static package regression |
| R2 | exact mathematical regression on the unchanged manuscript |
| R3 | duplicate-block regression across MD, TeX and PDF |
| R4 | recorded and external Lean evidence reuse under byte identity; no Lean execution |
| R5 | bilingual and artifact-chain reuse under byte identity |
| R6 | manifests, report and sealed internal residual package |

Every gate must pass. Any manuscript or Lean-anchor mismatch is a blocker. A
late file change invalidates dependent manifests and the sealed package.

## Evidence-reuse rule

The external v1.2 audit may be reused only after the six manuscript anchors,
the Lean archive and the previous external report match their frozen hashes.
Lean must not be rebuilt in this internal audit. PDF compilation and rendered
inspection need not be repeated because the artifacts are unchanged; their
prior internal and external QA is reused by byte identity.

## Verdict rule

`PASS` requires zero unresolved blocker, major or minor findings. The external
HTTP 403 observation `EXT-P2-I-001` remains a disclosed nonblocking NOTE.

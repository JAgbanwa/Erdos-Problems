# Open risks and residuals - PAPER_II, preprint_draft_v1.2

**Protocol:** `EXTERNAL_AI_ADVERSARIAL_AUDIT_INSTRUCTIONS_v1.1`
**Verdict:** `PASS_WITH_RESIDUALS`. No mathematical or formal defect was found.

## Findings

| ID | Severity | Summary | Fix |
|---|---|---|---|
| `EXT-PII-M-001` | MINOR | `04_integrity/` is stale v1.1 content; 1 of 2 sidecar entries names a v1.1 manuscript absent from the package, so it cannot verify; no documented v1.1 to v1.2 initialization diff | regenerate the integrity baseline for v1.2, or state that the directory is a retained historical record |
| `EXT-P2-I-001` | NOTE | the official Erdos Problems page for #81 could not be retrieved (HTTP 403 to this auditor) | none required; the open status is corroborated by the verified primary source [1] |

## Coverage limits - what this audit did not establish

| Item | Status |
|---|---|
| **termination** of the repeated-copy process | not independently verified; the single-step inequality was, exhaustively |
| the **discrete-convexity lift** from single vertices to clone classes | not independently verified |
| the **two-variable orbit reduction** on `S_{p,q}` | not rederived; tested through its consequences |
| the stronger claim that every chordal extremizer is complete-split up to isomorphism | not tested - and **not claimed** by the manuscript |
| exhaustive enumeration beyond `n = 6` | `n = 7` was attempted; the claim is for all `n >= 1` |
| modules outside the seven protocol build targets | never compiled, no verdict |
| novelty | evidence-bounded negative result only; no institutional database, no citation-graph traversal, no non-English search |
| PDFs recompiled from the delivered TeX | not done; producer strings and source-to-PDF tracking checked instead |

## Risks specific to this audit's configuration

- Both reasoning contexts used in this series are the **same model family**, so correlated
  blind spots are possible. For Paper II specifically, the adversarial challenger was run
  against Paper I only; Paper II's findings come from the primary auditor alone.
- The **same operator** launched the audit and authored the work.

## What would raise confidence most, in order

1. Regenerate `04_integrity` for v1.2 - the only open defect.
2. Have an independent challenger, ideally a different model family, attack the termination
   and clone-class-lift steps this audit could not reach.
3. Obtain specialist confirmation of novelty.

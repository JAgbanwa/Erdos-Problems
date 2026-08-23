# Claim and finding map - PAPER_II v1.2 pkgfix, run_2026-08-21_v1.2_pkgfix

**Specification:** `FINAL_RESIDUAL_AUDIT_REQUEST_SPEC.md`
**Verdict:** `PASS`

## What this run did and did not do

This is a **package-residual** re-audit. It verified the correction of one package-integrity
MINOR and ran a package-level regression. It did **not** re-examine the mathematics, the
formalization, the citations, the translation or the rendered artifacts: those were
established in `run_2026-08-21_v1.2` and are reused here under byte identity, which the
specification authorizes once the nine protected anchors match. They do.

## Findings

| ID | Severity | Status | Where verified |
|---|---|---|---|
| `EXT-PII-M-001` | MINOR | **CLOSED** | Control A, `20_EVIDENCE/CONTROL_A_INTEGRITY/` |
| `EXT-P2-I-001` | NOTE | OPEN, preserved | not resolvable by this auditor; see the report |

No new finding of any severity was opened.

## Claim surfaces, and where their evidence lives now

| Claim ID | Status in this run |
|---|---|
| `P2-MAIN-V1_2` exact chordal maximum | **reused**, byte-identical. Anchor: EN Markdown `7215e14b…8882` unchanged. Prior evidence: 19,048 chordal graphs enumerated exhaustively, formula exact at every n, always attained by a complete-split graph. |
| `P2-EXTREMIZER` maximizers, level sets, copy defects | **reused**. Prior evidence: 251,085 copy instances, 0 violations. Termination and the clone-class lift remain **unverified** in every run. |
| `P2-ASYM-COR` asymptotic, modular, Paper I comparison | **reused**. All four corollaries confirmed over n in [-20000, 20000]; the `n >= 1` hypothesis shown necessary. |
| `P2-FORMAL-CONFORMANCE` v1.2 surface and reusable components | **reused**, and independently cross-checked in this run: the internal R4 gate's copied build and axiom logs are byte-identical to this auditor's own external logs, and confirm exit 0, 8,063 jobs, 16 axiom surfaces, 0 sorryAx, 0 project axioms, with 2 surfaces carrying the smaller `[propext, Quot.sound]` footprint. |

## Fresh work in this run

| Area | Evidence |
|---|---|
| target freeze and canonical manifest, 245 files / 3,940,779 bytes / manifest `4b41f7e2…8c1e` | `20_EVIDENCE/TARGET_FREEZE/` |
| Control A, closing `EXT-PII-M-001` | `20_EVIDENCE/CONTROL_A_INTEGRITY/` |
| Control B, inspecting the internal R0-R6 raw evidence | `20_EVIDENCE/CONTROL_B_INTERNAL_EVIDENCE/` |
| Control C, hygiene, authorized delta, self-containment, status | `20_EVIDENCE/CONTROL_C_REGRESSION/` |
| byte-identity reuse record | `20_EVIDENCE/BYTE_IDENTITY_REUSE/` |

## Standing limitations, carried forward rather than dropped

Termination of the copy process; the discrete-convexity lift to clone classes; the
two-variable orbit reduction; enumeration beyond n = 6; Lean modules outside the seven
protocol targets; independent PDF recompilation; novelty; and the fact that **Paper II has
never been audited by an adversarial challenger** — every Paper II finding, in both runs,
comes from a single reasoning context.

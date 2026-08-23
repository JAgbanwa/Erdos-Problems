# Audit index - PAPER_II, preprint_draft_v1.2, run_2026-08-21_v1.2

**Protocol:** `EXTERNAL_AI_ADVERSARIAL_AUDIT_INSTRUCTIONS_v1.1`
**Overall verdict:** `PASS_WITH_RESIDUALS` - no mathematical or formal defect found;
0 blocker, 0 major, 1 minor, 1 note.

## Where to look

| I want | Path |
|---|---|
| the verdict and full reasoning | `30_REPORT/FINAL_AUDIT_REPORT.md` (also `.tex`, `.pdf`) |
| machine-readable summary | `30_REPORT/FINAL_AUDIT_SUMMARY.json` |
| findings ledger | `10_CONTROL/FINDINGS.csv` |
| per-gate verdicts | `10_CONTROL/GATE_STATUS.json` |
| who audited, with what, what was unavailable | `00_REQUEST/AUDITOR_DECLARATION.md` |
| frozen input identity | `00_REQUEST/INPUT_INVENTORY.json`, `INPUT_FREEZE_MANIFEST.sha256` |
| environment and clean room | `10_CONTROL/ENVIRONMENT.md` |
| residual risk | `10_CONTROL/OPEN_RISKS.md` |

## Evidence map

| Gate | Directory | Verdict |
|---|---|---|
| G0 target, identity, independence | `20_EVIDENCE/G0_TARGET_INDEPENDENCE/` | PASS |
| A definitions and claims | `20_EVIDENCE/A_DEFINITIONS_CLAIMS/` | PASS |
| B definitions, conventions, the functional | `20_EVIDENCE/B_PROOF_CHAIN/` | PASS |
| C vertex-copy inequality and symmetrization | `20_EVIDENCE/C_PROOF_CHAIN/` | PASS |
| D monotonicity, ties, level sets | `20_EVIDENCE/D_PROOF_CHAIN/` | PASS; termination not independently verified |
| E complete-split value | `20_EVIDENCE/E_PROOF_CHAIN/` | PASS |
| F integer maximization and corollaries | `20_EVIDENCE/F_PROOF_CHAIN/` | PASS |
| G exhaustive falsification | `20_EVIDENCE/G_FALSIFICATION/` | PASS |
| H Lean reproduction and conformance | `20_EVIDENCE/H_LEAN_REPRODUCTION/` | PASS |
| I citations and problem status | `20_EVIDENCE/I_CITATIONS_STATUS/` | PASS_WITH_RESIDUALS |
| J scope and overclaim | `20_EVIDENCE/J_SCOPE_OVERCLAIM/` | PASS |
| K prior art and novelty | `20_EVIDENCE/K_PRIOR_ART_NOVELTY/` | PASS_WITH_RESIDUALS |
| L bilingual and artifact consistency | `20_EVIDENCE/L_BILINGUAL_ARTIFACTS/` | PASS_WITH_RESIDUALS |
| M package integrity | `20_EVIDENCE/M_PACKAGE_INTEGRITY/` | PASS_WITH_RESIDUALS |

## Headline numbers

- **19,048** chordal graphs enumerated exhaustively; `max Phi_tau = floor((2n+1)^2/24)`
  exact at every `n` in 1..6, always attained by a complete-split graph.
- **251,085** copy instances; the vertex-copy inequality never violated.
- **270,133** graphs in total on which `nu_3^* = tau_3^*` was computed by two separate
  linear programs, with **zero** mismatches.
- Lean: `Build completed successfully (8063 jobs)`, exit 0, 30m05s, zero errors; 16
  declarations queried, no `sorryAx`, no project axiom, **0** escape hatches in active code.

## Reproducing

Scripts are Python 3.14 needing only the standard library plus `Pillow` for page analysis;
each gate record states its invocation. All arithmetic is exact and no random seeds are
used. The Lean reproduction needs Lean 4.28.0 (commit `7e01a1bf...`) and Mathlib
`8f9d9cff...`; on Windows set `git config --global core.longpaths true` and use a short
clean-room root.

## What this package is not

Not human peer review, and no proof of global novelty. See the final report's closing
section for the explicit list of what the audit does not establish.

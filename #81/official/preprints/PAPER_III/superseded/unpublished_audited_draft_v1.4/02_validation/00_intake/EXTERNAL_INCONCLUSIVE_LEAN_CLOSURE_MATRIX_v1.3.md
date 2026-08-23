# Paper III v1.3 — external inconclusive Lean-closure matrix

Date: 2026-08-22  
External baseline: `C:\gcr\30_REPORT\CONSOLIDATED_FINAL_AUDIT_REPORT.md`  
Baseline SHA-256: `2bf8eb1566657ddcbf764bd48a580e391f258fdc9418bb2bb0b6825fb6a5bfdb`  
Purpose: internal-audit intake; not an external re-audit

## Status vocabulary

- `CLOSED_BY_V1.3_TARGET`: the missing target-side Lean surface identified by the
  auditor is now part of v1.3 and must pass the v1.3 build and axiom gates.
- `FORMAL_SURFACE_PRESENT`: the load-bearing obligation has named Lean declarations
  in the target and will be queried explicitly.
- `INDEPENDENT_REDERIVATION_OPEN`: the prior external auditor did not rederive the
  underlying mathematics; compilation or `#print axioms` does not close that external
  obligation.

## Matrix

| External item | v1.3 target surface | Internal disposition before final gates | Required residual external work |
|---|---|---|---|
| `EXT-P3-C1-001` — no bridge between the fractional feasible-set encodings | `PaperIII.isFracPacking_iff_yuster`; `PaperIII.nu3Star_eq_yuster`; `PaperIII.tau3Star_eq_nu3Star`; `PaperIII.AX1Assumption_iff_packing_form` | `CLOSED_BY_V1.3_TARGET`, conditional on consolidated build and axiom record | confirm the declarations from the sealed v1.3 archive and compare them with the auditor's independent bridge |
| `K-EPS` — complete AX1 loss budget | `Nibble.AX1.boxAllocationResidual_holds`; `Nibble.AX1.blockCoverResidualCoupled_holds`; `Nibble.AX1.ax1_of_boxAllocation`; `Nibble.AX1.ax1Statement_holds`; `PaperIII.AX1_holds`; `PaperIII.E_4_3_of_AX1` | `FORMAL_SURFACE_PRESENT`; `INDEPENDENT_REDERIVATION_OPEN` | trace the 102-module active proof-term closure and independently rederive the full epsilon ledger, exceptional sets, rounding and branch coverage |
| `K-CORRIDOR` — Sections 5–7 boundary machinery | `PaperIII.E_5_1`; `PaperIII.cor_5_3`; `PaperIII.E_5_2`; `PaperIII.Prop_10_1_low`; `PaperIII.Prop_10_1_mid` | `FORMAL_SURFACE_PRESENT`; `INDEPENDENT_REDERIVATION_OPEN` | parity and boundary rederivation for one-factor, double-factor, polarization and shifted-center estimates |
| `K-SPARSE` — Section 8 corrections and `0.91p` threshold | `PaperIII.E_8_clique_packing_of_AX2`; `PaperIII.E_8_of_AX1_AX2`; `PaperIII.AX2_holds` | `FORMAL_SURFACE_PRESENT`; `INDEPENDENT_REDERIVATION_OPEN` | independently check divisibility corrections, degree loss, original clique order and the `0.91` versus `0.9 + eps` arithmetic |
| `K-COVER` — exhaustiveness of the Section 9 case split | `PaperIII.eventual_bound_of_high_degree_of_AX1_AX2`; `PaperIII.Prop_10_1_low`; `PaperIII.Prop_10_1_mid` | `FORMAL_SURFACE_PRESENT`; `INDEPENDENT_REDERIVATION_OPEN` | independently check every integer branch, strict join and threshold conversion |
| `K-GLOBAL` — eventual-to-all-orders induction | `PaperIII.global_bound_from_eventual_high_degree`; `PaperIII.Theorem_1_1_of_AX1_AX2`; `PaperIII.Theorem_1_1` | `FORMAL_SURFACE_PRESENT`; `INDEPENDENT_REDERIVATION_OPEN` | independently rederive the base, high-degree and deletion branches and the uniform constant |

## Internal gate rule

The v1.3 internal audit may pass formal-conformance and recorded-build gates only if
the named surfaces exist, the v1.3 build exits zero, each admitted axiom query is
recorded, and no project axiom or prohibited escape hatch appears. Such a PASS is
author-side evidence only. It must not be reported as closing the five external kill
switches that were never attacked.

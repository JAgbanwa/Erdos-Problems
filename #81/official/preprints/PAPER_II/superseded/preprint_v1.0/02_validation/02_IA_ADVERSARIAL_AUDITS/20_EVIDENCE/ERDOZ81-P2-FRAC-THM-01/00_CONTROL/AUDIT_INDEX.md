# Paper II External Adversarial Audit — Index

**Executive status: PASS** (with two provenance residuals on Gate H).
Canonical report: `10_REPORT/FINAL_AUDIT_REPORT.md` (+ `.pdf`).

## Target (the only claim of Paper II)
`max over chordal G on n vertices of (|E(G)| − 2·τ₃*(G)) = ⌊(2n+1)²/24⌋`,
attained by a complete-split `S_{p,q} = K_p ∨ K̄_q`.

## Layout
```
PAPER_II_EXT_AUDIT/
  00_CONTROL/   ENVIRONMENT.md, CLAIM_MAP.md, AUDIT_INDEX.md, OPEN_RISKS.md, audit_lib.py
  10_REPORT/    FINAL_AUDIT_REPORT.md/.pdf, make_final_pdf.py
  20_TESTS/     P1..P5 + H  (each: script + results + English PDF + zip + zip.sha256)
```

## Gate → test map
| Gate | Test folder | Verdict |
|------|-------------|---------|
| B (Lemma 3.1) | `20_TESTS/P2_vertex_copy/` | VERIFIED |
| C,D (Lemma 4.3/5.1 + C₄) | `20_TESTS/P5_terminal_characterization/` | VERIFIED |
| E (Prop 6.2/Cor 6.3) | `20_TESTS/P3_completesplit_closedform/` | VERIFIED |
| F (Prop 7.1) | `20_TESTS/P4_integer_maximization/` | VERIFIED |
| F,G (main kill-switch) | `20_TESTS/P1_max_phitau/` | VERIFIED (exhaustive n≤6) |
| H (Lean) | `20_TESTS/H_lean_verification/` | VERIFIED_WITH_RESIDUAL_RISK |
| A, I, J | read (see report) | VERIFIED |

## Headline
The exact fractional-cover theorem is **corroborated on all three axes**: analytic
proof reproduced, Lean certificate re-elaborated (build OK, `IsChordal`,
sorry-free), and exhaustive small-case computation finds the max `= ⌊(2n+1)²/24⌋`
attained by a complete-split, with **no** counterexample. No over-claim
(`cp`/#81 out of scope). Residuals: clean-room Mathlib rebuild and commit-
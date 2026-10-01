# Gate E5 report — run_v1.21_r1 (Paper IV v1.21)

Verdict: **PASS**. Evidence: `20_EVIDENCE/E5/`.

---

## E5 — Falsification revalidation (no compilation)

**Repeated in this cycle (new evidence):** `e5_v121_numerics.py` → `E5_V121_NUMERICS.json`, log
`10_LOGS/E5_v121_numerics.log`. 21 exact or rigorous checks of the numerics added in v1.21, all PASS. Every
predeclared negative control was rejected.
- C.2 bilateral cleaning (C2-1…C2-3): 33δ ≤ vu²a₃³ and 138δ ≤ vu²a₄³, with a₃ ≥ a³/2 and a₄ ≥ a⁶/2, on a grid
  of a ≤ 1/10 that includes the η₀ schedule a = (9·10¹⁹)⁻¹. Also 138/2208 = 1/16, and 3·11 = 33, 6·23 = 138.
  Negative controls: the constant ×17 fails; 138/2208 = 1/8 is false.
- C.3 chain (C3-1…C3-16): β₀ ≥ 2⁻⁶⁶, L_T ≤ 46, M_T ≤ 5153, 8·5153+1 ≤ 59480 ln 2, 4a₀+5 ≤ 2¹⁸,
  (12/7)(5153+1/8) ≤ 12748 ln 2, D₀ ≤ 2^{a₀+146}, Z = 191424, U = Y+191432, 2·10¹⁷·392 ≤ 2⁶⁷, U+67 ≤ 2^59517.
  Negative controls: M ≤ 5100, 59470, 2¹⁷, 12740, 2^{a₀+144}, Z = 191432 and 2⁶⁶ are each rejected. Logarithms
  are evaluated with mpmath at 60 digits, used only in monotone comparisons whose margins are ≥ 10⁻³.
- E.1 normalization (E1-1): identities and bounds for h ∈ {1, 2, 3, 7, 50} with exact rationals.
- (E.2d) error ≤ n/9 (E2d-1). The negative control n/12 is rejected.

**Reused (not repeated):** the 24 predeclared tests T01–T24 of run_v1.2_r1 (`run_v1.2_r1/20_EVIDENCE/E5/`).
E0 shows their files are unchanged. The mathematics they test is unchanged in v1.21 apart from the renamed
subscripts. The T25/Certo item stays as audited (feasibility-only certificate, valid).

**Detector regression (mandate §3 E5):** `20_EVIDENCE/E8/e8_detector_check.py`. The corrected pattern
recognises the real captured Lean 4.28 warning (backticks), single, double and curly quotes, `sorryAx`, and a
line break inside the phrase. It does not fire on standard axiom lists, on identifiers containing "sorry", or
on `sorryish`.

**E5 verdict: PASS** (finite and numeric scope; no universal claim is established by these tests).

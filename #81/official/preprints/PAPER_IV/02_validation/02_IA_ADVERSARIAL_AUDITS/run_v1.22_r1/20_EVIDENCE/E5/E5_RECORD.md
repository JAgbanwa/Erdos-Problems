# E5 — Exact arithmetic (no Lean)

| Script | Status this cycle | Result |
|---|---|---|
| `e5_v122_c3.py` → `E5_V122_C3.json` (new, auditor-written) | **Executed** | 14 checks (C3a–C3n) of the new C.3 text: all PASS. 8 of them carry an inline negative control. 7 of those controls were rejected; the C3m control was mis-specified, because its variant 2^{29R} is also true (CORRECTIONS C2-01). |
| `e5_v122_c3_negfix.py` → `E5_V122_C3_negfix.json` | **Executed** | Corrected C3m control: (R·16^R)⁶ ≤ 2^{24R} is false on 1..50 and is rejected as required. |
| `e5_v122_c3_neg_supplement.py` → `E5_V122_C3_neg_supplement.json` | **Executed** | Negative controls for the six checks that had none (C3c, C3e, C3g, C3j, C3l, C3n): all 6 perturbed claims are false and rejected. With this file, every C.3 check has a rejected negative control. |
| `e5_v121_numerics.py` → `E5_V121_RERUN.json` (copied from run_v1.21_r1) | **Repeated** | The 21 v1.21 checks (C.2, the C.3 schedule and selector chain, E.1, E.2d): all PASS, all negatives rejected. Table C.1 of C.3 is unchanged. |
| run_v1.2_r1 T01–T24 | **Inherited** | The covered text is unchanged (diff). |

## Typing of the evidence
- C3a–C3g are exact rational and integer identities and inequalities at the fixed parameters, computed with `fractions.Fraction` and Python big integers.
- C3h, C3i, C3l, C3m and C3n check elementary universal lemmas only on finite ranges: x·4^x ≥ 2^x, 16^x ≥ 4x, 8q ≤ 2^q (q ≥ 6), 256B² ≤ B⁶ (B ≥ 4), 4x·4^x ≤ 2^{4x}, R⁶ ≤ 2^{6R}, and 30R ≤ 8q given 4R ≤ q. **This is a finite regression, not a universal proof.**
  - The universal statements were proved by hand in E2; they are one-line inductions or monotonicity arguments.
  - They are also covered by the frozen E19 theorems, whose build E4 confirms by reuse.
- Quantities such as R, B and T(h+7) are never materialised; the argument works on exponents.

**E5 verdict: PASS.**

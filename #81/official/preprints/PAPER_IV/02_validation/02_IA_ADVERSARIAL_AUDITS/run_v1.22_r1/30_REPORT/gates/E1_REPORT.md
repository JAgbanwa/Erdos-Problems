# Gate E1 report — run_v1.22_r1 (Paper IV v1.22-r1)

Verdict: **PASS**. Evidence: `20_EVIDENCE/E1/`. Auditor: Claude Opus 5.5, same session as run_v1.2_r1/run_v1.21_r1; no Lean executed.

---

# E1 — Statements, constants and tags (regression)

The basis is the auditor's own diff (`20_EVIDENCE/E2/auditor_diff_*.diff`) and `E6_PARITY.json`.

- No theorem, proposition, lemma or corollary statement changed in either language; the theorem-heading line counts are unchanged (33 EN, 34 ES).
- Equation tags are identical to v1.21 in both languages, and no display formula was removed. The 7 added displays are the C.3 derivation (EN and ES identical).
- The final constants are unchanged: k₀ = 3·10¹⁹+1, h, N = T(h+7), b = N² ≤ T(h+8), c_poly, c_far, c_T, P(s), γ_s, A_s and the thresholds of (F.1). C.3 now derives T(h+7) (E2), and the value is not modified.
- NEW-01 (EN 5.1 heading, A.2 row, ES Lemma 3.2 heading) is fixed. The remaining ES §7.2 `Model` formatting residual is recorded under E6.
- X-17 and X-18 are kept as OBSERVATIONS (unchanged; the author made no change).

**E1 verdict: PASS.**

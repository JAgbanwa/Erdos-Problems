/-
  Part A — Dross's A7 extremization step (7) → (8), δ = 1/10.

  SELF-CORRECTION NOTICE. An earlier version of this file claimed inequality (7) was "vacuous"
  (`dross_ineq7_vacuous`). That claim was based on OUR OWN mis-transcription of (7): we had
  written the right-hand side as `2m − (T_B(T_B−δn) − (3n(1−δ)−3)·T_B)`, flipping the sign of
  the linear term to `+`. The published inequality (7) (Dross, SIAM J. Discrete Math. 30 (2016),
  eq. (7)) has BOTH right-hand terms subtracted:
      (7)  T_A(T_A − δn) − (3n(1−δ) − 3)·T_A  <  2m − T_B(T_B − δn) − (3n(1−δ) − 3)·T_B.
  With the correct signs, (7) is informative and the step (7) → (8) is valid. Dross's proof is
  correct; the earlier "vacuity finding" was our error and is retracted.

  We formalize the correct extremization below.
-/
import Mathlib

namespace Ax2

/-- **Dross A7, step (7) → (8) (δ = 1/10).** With `n ≥ 20`, `T_A, T_B ∈ [n − 2δn, n]`, and the
(correctly transcribed) inequality (7), we obtain (8): `(2 − 12δ + 12δ²)n² < 2m − 6δn`.

Proof of the extremization: on `[0.8n, n]` the left summand `f(T) = T(T−δn) − (3n(1−δ)−3)T` is
decreasing (so `f(T_A) ≥ f(n)`), and the subtracted right summand
`s(T) = T(T−δn) + (3n(1−δ)−3)T` is increasing (so `s(T_B) ≥ s(0.8n)`, i.e. the RHS `2m − s(T_B)`
is maximized at `T_B = 0.8n`). Chaining, `f(n) < 2m − s(0.8n)`, which is exactly (8). -/
theorem dross_7_to_8 (n m T_A T_B : ℝ) (hn : 20 ≤ n)
    (hTA1 : (8 / 10) * n ≤ T_A) (hTA2 : T_A ≤ n)
    (hTB1 : (8 / 10) * n ≤ T_B) (hTB2 : T_B ≤ n)
    (h7 : T_A * (T_A - (1/10 : ℝ) * n) - (3 * n * (1 - 1/10) - 3) * T_A
        < 2 * m - T_B * (T_B - (1/10 : ℝ) * n) - (3 * n * (1 - 1/10) - 3) * T_B) :
    (2 - 12 * (1/10 : ℝ) + 12 * (1/10)^2) * n ^ 2 < 2 * m - 6 * (1/10) * n := by
  -- f(T_A) ≥ f(n):  (n − T_A)·(1.8n − 3 − T_A) ≥ 0
  have hf : 0 ≤ (n - T_A) * ((18/10) * n - 3 - T_A) :=
    mul_nonneg (by linarith) (by nlinarith)
  -- s(T_B) ≥ s(0.8n):  (T_B − 0.8n)·(T_B + 3.4n − 3) ≥ 0
  have hs : 0 ≤ (T_B - (8/10) * n) * (T_B + (34/10) * n - 3) :=
    mul_nonneg (by linarith) (by nlinarith)
  nlinarith [h7, hf, hs]

end Ax2

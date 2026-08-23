/-
# ρ-reconciliation for discharging BKLO Lemma 10.10 via the codegree regime

Local verification that the parameter choice `ρ = 1/(625 k²)` simultaneously
* satisfies the CODEGREE regime of `BKLO.Lemma1010K3Dense` (`1/(648 k²) < ρ`, since `625 < 648`), and
* keeps every numerical bound of the §10.12 hierarchy (`Section1012Assembly`), which the analysis
  shows only needs `ρ² ≤ 1` / `ρ ≤ ε`, not the specific `ρ = 1/(10000 k²)`.

`√ρ = 1/(25 k)` is clean, so `eighteen_sqrt` becomes the analogous identity `18 k √ρ³ = (18/25) ρ`.
This de-risks the full assembly rework: the ρ window `(1/648k², ·)` is nonempty and this point sits
in it while preserving the hierarchy.
-/
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Real.StarOrdered
import Mathlib.Tactic.Bound
import Mathlib.Tactic.Positivity

namespace BKLO.RhoReconcile625

variable {kk ε ρ γ α : ℝ}

theorem rho_pos (hk : 30 ≤ kk) (hρ : ρ = 1 / (625 * kk ^ 2)) : 0 < ρ := by
  have : (0:ℝ) < kk := by linarith
  rw [hρ]; positivity

/-- The codegree regime condition of `Lemma1010K3Dense`: `1/(648 k²) < ρ`. -/
theorem codegree_regime (hk : 30 ≤ kk) (hρ : ρ = 1 / (625 * kk ^ 2)) :
    1 / (648 * kk ^ 2) < ρ := by
  have hk0 : (0:ℝ) < kk := by linarith
  rw [hρ]
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith only [sq_nonneg kk, hk0]

theorem rho_le (hk : 30 ≤ kk) (hρ : ρ = 1 / (625 * kk ^ 2)) : ρ ≤ 1 / 562500 := by
  have hk0 : (0:ℝ) < kk := by linarith
  rw [hρ]
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith only [sq_nonneg kk, hk]

theorem rho_lt_one (hk : 30 ≤ kk) (hρ : ρ = 1 / (625 * kk ^ 2)) : ρ < 1 := by
  have := rho_le hk hρ; linarith

theorem rho_sq_le (hk : 30 ≤ kk) (hρ : ρ = 1 / (625 * kk ^ 2)) : ρ ^ 2 ≤ ρ := by
  have h0 : 0 < ρ := rho_pos hk hρ
  have h1 : ρ < 1 := rho_lt_one hk hρ
  nlinarith

/-- The clean square-root identity for `ρ = 1/(625 k²)`: `√ρ = 1/(25 k)`. -/
theorem sqrt_rho (hk : 30 ≤ kk) (hρ : ρ = 1 / (625 * kk ^ 2)) :
    Real.sqrt ρ = 1 / (25 * kk) := by
  have hk0 : (0:ℝ) < kk := by linarith
  have hsq : ρ = (1 / (25 * kk)) ^ 2 := by rw [hρ]; field_simp; norm_num
  rw [hsq, Real.sqrt_sq (by positivity)]

/-- The analogue of `eighteen_sqrt`: `18 k √ρ³ = (18/25) ρ`. -/
theorem eighteen_sqrt (hk : 30 ≤ kk) (hρ : ρ = 1 / (625 * kk ^ 2)) :
    18 * kk * Real.sqrt ρ ^ 3 = 18 / 25 * ρ := by
  have hk0 : (0:ℝ) < kk := by linarith
  rw [sqrt_rho hk hρ, hρ]; field_simp; ring

theorem rho_le_eps (hk : 30 ≤ kk) (hkε : 1 / kk ≤ ε) (hρ : ρ = 1 / (625 * kk ^ 2)) : ρ ≤ ε := by
  have hk0 : (0:ℝ) < kk := by linarith
  have h1 : ρ ≤ 1 / kk := by
    rw [hρ]; rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith only [hk]
  linarith

/-- The final degree bound survives (it only needs `ρ² ≤ 1`). -/
theorem final_bound (hk : 30 ≤ kk) (hε : 0 < ε) (hρ : ρ = 1 / (625 * kk ^ 2))
    (hγ : γ = ρ ^ 2 * ε / (1000 * kk ^ 2)) (hα : α = ε / (16 * kk ^ 2)) :
    3 * γ + 2 * α ≤ ε / (2 * kk ^ 2) := by
  have hk0 : (0:ℝ) < kk := by linarith
  have hρ0 : 0 < ρ := rho_pos hk hρ
  have hρ1 : ρ < 1 := rho_lt_one hk hρ
  have hρsq : ρ ^ 2 ≤ 1 := by nlinarith
  have hc : (0:ℝ) < ε / kk ^ 2 := by positivity
  have h1 : γ ≤ ε / kk ^ 2 / 1000 := by
    have he : γ = ρ ^ 2 * (ε / kk ^ 2) / 1000 := by rw [hγ]; field_simp
    have h2 : ρ ^ 2 * (ε / kk ^ 2) ≤ ε / kk ^ 2 := by nlinarith
    rw [he]; linarith
  have h2 : α = ε / kk ^ 2 / 16 := by rw [hα]; field_simp
  have h3 : ε / (2 * kk ^ 2) = ε / kk ^ 2 / 2 := by field_simp
  rw [h2, h3]; linarith

end BKLO.RhoReconcile625

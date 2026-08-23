/-
# The §10.12 assembly at a hierarchy-correct `ρ`

`BKLO/Section1012Reconcile.lean` runs the proof of BKLO Lemma 10.12 (`r = 2`, `F = K₃`, dense
regime) from the corrected §7.2 and §9.3 inputs with the sparsity parameter `ρ` free, and
instantiates it at `ρ = 1/(10000k²)`.  That value of `ρ` violates the paper's hierarchy
`ρ ≪ α`: the assembly applies Corollary 10.11 at `α = ε/(16k²) ≤ 1/(480k²)`, while
`2kρ = 1/(5000k)`, so `2kρ ≤ α` fails for `k ≥ 30`.  Consequently the instantiation could only be
fed by the over-strong Corollary 10.11 valid for *every* `α`, and **not** by the
hierarchy-restored `BKLO.Cor1011K3Hier` of `BKLO/Section1010Sparse.lean`.

This file re-parametrises the assembly at

  `ρ = ε/(32k³)`,

for which `2kρ = ε/(16k²) = α` *exactly*, so the hierarchy hypothesis of `Cor1011K3Hier` holds
(with equality, the largest ρ the hierarchy allows).  All the ρ-dependent side conditions of the
assembly become easier at this smaller ρ:

* `0 < ρ` and `ρ ≤ ε` (`BKLO.Lemma1012ParamsHier.rho_pos`, `.rho_le_eps`);
* the codegree slack of condition (ii) of Lemma 10.10, `18k√ρ³ ≤ ρ/4`
  (`BKLO.Lemma1012ParamsHier.slack`): here `√ρ ≤ 1/(72k)` with room to spare, since
  `ρ ≤ 1/(960k³) ≤ 1/(5184k²)` for `k ≥ 30`;
* the final degree budget `3γ + 2α ≤ ε/(2k²)` at `γ = ρ²ε/(1000k²)`, which only needs `0 < ρ ≤ 1`
  and is supplied by `BKLO.Lemma1012ParamsGen.final_bound` as before.

The outcome is

  `BKLO.lemma1012K3'_dense_of_hier :
      ApproxTriDecompMinDeg (9/10) → Cor1011K3Hier → Lemma1012K3' (9/10)`,

i.e. Lemma 10.12 in the dense regime from the `δ_F^η` input and Corollary 10.11 **only where the
paper's hierarchy holds**.  Everything here is `sorry`-free.
-/
import BKLO.Section1012Reconcile
import BKLO.Section1010Sparse

open Finset

namespace BKLO

/-! ### The hierarchy-correct sparsity parameter `ρ = ε/(32k³)` -/

namespace Lemma1012ParamsHier

variable {kk ε ρ : ℝ}

theorem rho_pos (hk : 30 ≤ kk) (hε : 0 < ε) (hρ : ρ = ε / (32 * kk ^ 3)) : 0 < ρ := by
  have hk0 : (0 : ℝ) < kk := by linarith only [hk]
  rw [hρ]; positivity

theorem cube_le (hk : 30 ≤ kk) : (27000 : ℝ) ≤ kk ^ 3 := by
  have hk0 : (0 : ℝ) < kk := by linarith only [hk]
  nlinarith [mul_nonneg (sub_nonneg.2 hk) (sq_nonneg kk), mul_nonneg (sub_nonneg.2 hk) hk0.le]

theorem rho_le_eps (hk : 30 ≤ kk) (hε : 0 < ε) (hρ : ρ = ε / (32 * kk ^ 3)) : ρ ≤ ε := by
  have hk0 : (0 : ℝ) < kk := by linarith only [hk]
  have hcube : (27000 : ℝ) ≤ kk ^ 3 := cube_le hk
  rw [hρ, div_le_iff₀ (by positivity)]
  nlinarith only [hε, hcube]

/-- The hierarchy hypothesis of `BKLO.Cor1011K3Hier` holds with equality:
`2kρ = ε/(16k²) = α`. -/
theorem two_k_rho_le_alpha (hk : 30 ≤ kk) (hρ : ρ = ε / (32 * kk ^ 3)) :
    2 * kk * ρ ≤ ε / (16 * kk ^ 2) := by
  have hk0 : (0 : ℝ) < kk := by linarith only [hk]
  rw [hρ]
  have : 2 * kk * (ε / (32 * kk ^ 3)) = ε / (16 * kk ^ 2) := by field_simp; ring
  rw [this]

/-- `ρ ≤ 1/(5184k²)`, the form of (SLACK) after clearing the square root:
`ρ = ε/(32k³) ≤ 1/(960k³) ≤ 1/(5184k²)` for `k ≥ 30`. -/
theorem rho_le_sqrt_bound_sq (hk : 30 ≤ kk) (hε : 0 < ε) (hε30 : ε ≤ 1 / 30)
    (hρ : ρ = ε / (32 * kk ^ 3)) : ρ ≤ (1 / (72 * kk)) ^ 2 := by
  have hk0 : (0 : ℝ) < kk := by linarith only [hk]
  have hsq : (1 / (72 * kk)) ^ 2 = 1 / (5184 * kk ^ 2) := by field_simp; ring
  rw [hρ, hsq, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith only [mul_nonneg (sq_nonneg kk) (by linarith : (0 : ℝ) ≤ 32 * kk - 5184 * ε)]

/-- **The codegree slack of condition (ii) at the hierarchy-correct `ρ`.**  `√ρ ≤ 1/(72k)`, hence
`18k√ρ³ = 18kρ√ρ ≤ ρ/4`. -/
theorem slack (hk : 30 ≤ kk) (hε : 0 < ε) (hε30 : ε ≤ 1 / 30)
    (hρ : ρ = ε / (32 * kk ^ 3)) : 18 * kk * Real.sqrt ρ ^ 3 ≤ ρ / 4 := by
  have hk0 : (0 : ℝ) < kk := by linarith only [hk]
  have hρ0 : 0 < ρ := rho_pos hk hε hρ
  have hle : ρ ≤ (1 / (72 * kk)) ^ 2 := rho_le_sqrt_bound_sq hk hε hε30 hρ
  have hsqrt : Real.sqrt ρ ≤ 1 / (72 * kk) := by
    have h := Real.sqrt_le_sqrt hle
    rwa [Real.sqrt_sq (by positivity)] at h
  have hcube : Real.sqrt ρ ^ 3 = ρ * Real.sqrt ρ := by
    rw [show Real.sqrt ρ ^ 3 = Real.sqrt ρ ^ 2 * Real.sqrt ρ by ring, Real.sq_sqrt hρ0.le]
  have hmul : 18 * kk * (ρ * Real.sqrt ρ) ≤ 18 * kk * (ρ * (1 / (72 * kk))) := by
    have : ρ * Real.sqrt ρ ≤ ρ * (1 / (72 * kk)) :=
      mul_le_mul_of_nonneg_left hsqrt hρ0.le
    nlinarith only [hk0, this]
  have heq : 18 * kk * (ρ * (1 / (72 * kk))) = ρ / 4 := by field_simp; ring
  rw [hcube]
  linarith only [hmul, heq.le, heq.ge]

/-- **The old parameter `ρ = 1/(10000k²)` violates the hierarchy.**  At that `ρ` one has
`2kρ = 1/(5000k)`, while `α = ε/(16k²) ≤ 1/(480k²)`, so `2kρ ≤ α` fails for every `k ≥ 30`.
This is why the instantiation of `BKLO/Section1012Reconcile.lean` needed Corollary 10.11 at *every*
`α`, and could not be fed by `BKLO.Cor1011K3Hier`. -/
theorem two_k_rho_gt_alpha_at_ten_thousand (hk : 30 ≤ kk) (hε : 0 < ε) (hε30 : ε ≤ 1 / 30)
    (hρ : ρ = 1 / (10000 * kk ^ 2)) : ε / (16 * kk ^ 2) < 2 * kk * ρ := by
  have hk0 : (0 : ℝ) < kk := by linarith only [hk]
  have hlhs : ε / (16 * kk ^ 2) ≤ 1 / (480 * kk ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg kk]
  have hrhs : 2 * kk * ρ = 1 / (5000 * kk) := by
    rw [hρ]; field_simp; ring
  have hcmp : (1 : ℝ) / (480 * kk ^ 2) < 1 / (5000 * kk) := by
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith only [hk]
  rw [hrhs]
  linarith only [hlhs, hcmp]

end Lemma1012ParamsHier

/-! ### Corollary 10.11 with the hierarchy, at the single triple the assembly uses -/

/-- `BKLO.Cor1011K3Hier` supplies Corollary 10.11 at any single triple `(α, ρ, k)` obeying the
paper's hierarchy `2kρ ≤ α`. -/
theorem cor1011K3AtAlphaRho_of_hier {α ρ : ℝ} {k : ℕ} (h : Cor1011K3Hier) (hα : 0 < α)
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hk : 0 < k) (hhier : 2 * (k : ℝ) * ρ ≤ α) :
    Cor1011K3AtAlphaRho α ρ k :=
  h α ρ k hα hρ hρ1 hk hhier

/-! ### The assembly at the hierarchy-correct `ρ` -/

/-- **BKLO Lemma 10.12 for `r = 2` (repaired), hard case, from the corrected §7.2 and §9.3 inputs
and the hierarchy-correct Corollary 10.11.**  The sparsity parameter is `ρ = ε/(32k³)`, for which
`2kρ = ε/(16k²) = α`, so `BKLO.Cor1011K3Hier` applies at the one triple `(α, ρ, k)` the assembly
uses. -/
theorem lemma1012K3'At_of_hier {δ ε : ℝ} {k : ℕ}
    (hδ : (9 : ℝ) / 10 ≤ δ) (hk30 : 30 ≤ k) (hε : 0 < ε)
    (hkε : 1 / (k : ℝ) ≤ ε) (hsum : δ + 3 * ε ≤ 1)
    (h1011 : Cor1011K3Hier) (h106 : Lemma106K3Set δ) :
    Lemma1012K3'At δ k ε := by
  have hk0 : 0 < k := by omega
  have hkR : (30 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk30
  have hε30 : ε ≤ 1 / 30 := by linarith only [hδ, hsum]
  set ρ : ℝ := ε / (32 * (k : ℝ) ^ 3) with hρdef
  have hρpos : 0 < ρ := Lemma1012ParamsHier.rho_pos hkR hε hρdef
  have hρε : ρ ≤ ε := Lemma1012ParamsHier.rho_le_eps hkR hε hρdef
  have hρ1 : ρ < 1 := by linarith only [hε30, hρε]
  have h18 : 18 * (k : ℝ) * Real.sqrt ρ ^ 3 ≤ ρ / 4 :=
    Lemma1012ParamsHier.slack hkR hε hε30 hρdef
  have hαpos : 0 < ε / (16 * (k : ℝ) ^ 2) := by
    have : (0 : ℝ) < (k : ℝ) := by linarith only [hkR]
    positivity
  have hhier : 2 * (k : ℝ) * ρ ≤ ε / (16 * (k : ℝ) ^ 2) :=
    Lemma1012ParamsHier.two_k_rho_le_alpha hkR hρdef
  exact lemma1012K3'At_of_true_inputs_atAlpha hδ hk30 hε hkε hsum hρpos hρε h18
    lemma72K3'_holds lemma93K3S_holds
    (cor1011K3AtAlphaRho_of_hier h1011 hαpos hρpos hρ1 hk0 hhier) h106

/-- **BKLO Lemma 10.12 for `r = 2` (repaired), `δ ≥ 9/10`, from the hierarchy-correct
Corollary 10.11 and Lemma 10.6 on a vertex set.** -/
theorem lemma1012K3'_of_hier {δ : ℝ} (hδ : (9 : ℝ) / 10 ≤ δ)
    (h1011 : Cor1011K3Hier) (h106 : Lemma106K3Set δ) : Lemma1012K3' δ :=
  lemma1012K3'_of_hard_case hδ fun _ _ hk30 hε hkε hsum =>
    lemma1012K3'At_of_hier hδ hk30 hε hkε hsum h1011 h106

/-- **BKLO Lemma 10.12 for `r = 2` (repaired) in the dense regime `δ = 9/10`, from the `δ_F^η`
input and the hierarchy-correct Corollary 10.11.**  This is `BKLO.lemma1012K3'_dense_of_inputs`
with the over-strong `BKLO.Cor1011K3Sparse` — Corollary 10.11 at `ρ = 1/(10000k²)`, hence at
`α` far below `2kρ` — replaced by `BKLO.Cor1011K3Hier`, Corollary 10.11 restricted to the paper's
hierarchy `2kρ ≤ α`. -/
theorem lemma1012K3'_dense_of_hier (happ : ApproxTriDecompMinDeg (9 / 10))
    (h1011 : Cor1011K3Hier) : Lemma1012K3' (9 / 10) :=
  lemma1012K3'_of_hier le_rfl h1011 (lemma106K3Set_dense happ)

/-- The same, from Lemma 10.10 with the hierarchy, and hence (by
`BKLO.lemma1010K3Hier_of_lemma107K2`) from the single residual input `BKLO.Lemma107K2`. -/
theorem lemma1012K3'_dense_of_lemma1010Hier (happ : ApproxTriDecompMinDeg (9 / 10))
    (h1010 : Lemma1010K3Hier) : Lemma1012K3' (9 / 10) :=
  lemma1012K3'_dense_of_hier happ (cor1011K3Hier_of_lemma1010K3Hier h1010)

/-- The same, from `BKLO.Lemma107K2`: the §10.12 assembly in the dense regime now rests on the
hierarchy-correct §10.2 input alone. -/
theorem lemma1012K3'_dense_of_lemma107 (happ : ApproxTriDecompMinDeg (9 / 10))
    (h107 : Lemma107K2) : Lemma1012K3' (9 / 10) :=
  lemma1012K3'_dense_of_lemma1010Hier happ (lemma1010K3Hier_of_lemma107K2 h107)

end BKLO

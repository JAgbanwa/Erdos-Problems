/-
# Nibble — feasibility of the degree-adaptive (round-dependent) schedule

Standalone, Mathlib-only.  This is the positive counterpart of the obstructions in
`Nibble.FreedmanParamsObstruction`:

* with ONE fixed retention probability `p`, the total per-round gain of the nibble is capped by
  `(1-μ)d/(rΔ) ≤ 1/r` (`Nibble.total_gain_le`), so neither the absolute crux
  (`crux_telescope_false`) nor the relative crux (`crux_relative_telescope_false`) can be satisfied
  for `β < 1/2`;
* with a retention probability re-tuned each round to the *current* degree scale,
  `p_k = x / (r·Δ_k)`, the per-round covering fraction is a CONSTANT `≥ x(1-x)/(2r)`, so the
  covering demand is satisfiable for every target `β` — this file proves exactly that.

Two results:

* `adaptive_degree_schedule_pos` — with a relative per-round slack `c_k ≤ ε·d_k` (what a
  concentration bound of the form `c_k ≈ √(d_k log |V|)` supplies once `d_k` is large), the residual
  degree schedule stays positive and decays only geometrically: `d_k ≥ d_0 (1-x-ε)^k`.
* `adaptive_crux_satisfiable` — there are `x`, `lam < 1` and a round count `T` with `lam ^ T ≤ β`
  such that in every round the covering demand `1 - lam ≤ (1-η)·(d_k·p_k·(1-p_k)^{rΔ_k})` holds,
  uniformly over all degree scales `d_k > 0` with `d_k ≤ Δ_k ≤ 2 d_k`.

Together with `Nibble.DischargeSeq` (the round-dependent outer loop) this identifies the corrected
architecture for the nibble outer layer.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Real.StarOrdered
import Mathlib.Tactic.Bound
import Mathlib.Tactic.Positivity

namespace Nibble

/-- **The adaptive degree schedule stays positive.**  If each round loses a `x`-fraction of the
degree plus an additive slack `c k ≤ ε · d k` (a *relative* slack, which is what a concentration
bound `c_k ≈ √(d_k log |V|)` provides in the large-degree regime), then
`d k ≥ d 0 · (1 - x - ε) ^ k > 0` for all `k`. -/
theorem adaptive_degree_schedule_pos {d c : ℕ → ℝ} {x ε : ℝ}
    (hxε : x + ε < 1) (hd0 : 0 < d 0)
    (hslack : ∀ k, c k ≤ ε * d k)
    (hstep : ∀ k, d k * (1 - x) - c k ≤ d (k + 1)) :
    ∀ k, d 0 * (1 - x - ε) ^ k ≤ d k := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      have hpos : 0 ≤ (1 - x - ε) ^ k := pow_nonneg (by linarith) k
      have hdk : 0 ≤ d k := le_trans (mul_nonneg (le_of_lt hd0) hpos) ih
      have h1 : d k * (1 - x) - c k ≤ d (k + 1) := hstep k
      have h2 : c k ≤ ε * d k := hslack k
      have h3 : d k * (1 - x - ε) ≤ d (k + 1) := by nlinarith
      calc d 0 * (1 - x - ε) ^ (k + 1) = (d 0 * (1 - x - ε) ^ k) * (1 - x - ε) := by ring
        _ ≤ d k * (1 - x - ε) := mul_le_mul_of_nonneg_right ih (by linarith)
        _ ≤ d (k + 1) := h3

/-- Bernoulli bound for the survival factor: `(1-p)^m ≥ 1 - m·p`. -/
theorem one_sub_mul_le_pow_one_sub {p : ℝ} (hp1 : p ≤ 1) (m : ℕ) :
    1 - (m : ℝ) * p ≤ (1 - p) ^ m := by
  have h := one_add_mul_le_pow (a := -p) (by linarith) m
  simpa [sub_eq_add_neg, mul_comm, mul_neg] using h

/-- **The degree-adaptive covering demand is satisfiable.**  Choosing the retention probability of
round `k` as `p_k = 1 / (2 r Δ_k)` — i.e. re-tuned to the *current* degree bound `Δ_k` — the fraction
of the remaining vertices covered in round `k` is at least the CONSTANT `1/(8r)`, uniformly in the
round.  Hence for every target `β > 0` there is a decay factor `lam < 1` and a round count `T` with
`lam ^ T ≤ β` for which the per-round covering demand
`1 - lam ≤ (1-η)·(d_k · p_k · (1-p_k)^{r Δ_k})` holds in every round.

This is the exact statement that fails for a fixed retention probability
(`Nibble.crux_relative_telescope_false`): there the covering fraction decays like `(1-rΔp)^k` and
sums to at most `1/r`, here it is constant. -/
theorem adaptive_crux_satisfiable {r : ℕ} (hr : 2 ≤ r) {β η : ℝ} (hβ : 0 < β)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 2) :
    ∃ (lam : ℝ) (T : ℕ), 0 < lam ∧ lam < 1 ∧ lam ^ T ≤ β ∧
      ∀ (dk : ℝ) (Δk : ℕ), 0 < dk → dk ≤ (Δk : ℝ) → (Δk : ℝ) ≤ 2 * dk →
        1 - lam ≤ (1 - η) *
          (dk * (1 / (2 * (r : ℝ) * Δk)) * (1 - 1 / (2 * (r : ℝ) * Δk)) ^ (r * Δk)) := by
  have hrR : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hrpos : (0 : ℝ) < (r : ℝ) := by linarith
  set lam : ℝ := 1 - (1 - η) / (8 * (r : ℝ)) with hlam_def
  have hηpos : (1 : ℝ) / 2 ≤ 1 - η := by linarith
  have hη1' : 1 - η ≤ 1 := by linarith
  have hfrac_pos : 0 < (1 - η) / (8 * (r : ℝ)) := by positivity
  have hfrac_small : (1 - η) / (8 * (r : ℝ)) ≤ 1 / 16 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hlam0 : 0 < lam := by simp only [hlam_def]; linarith
  have hlam1 : lam < 1 := by simp only [hlam_def]; linarith
  obtain ⟨T, hT⟩ := exists_pow_lt_of_lt_one hβ hlam1
  refine ⟨lam, T, hlam0, hlam1, le_of_lt hT, ?_⟩
  intro dk Δk hdk hdΔ hΔd
  have hΔpos : (0 : ℝ) < (Δk : ℝ) := lt_of_lt_of_le hdk hdΔ
  have hΔ1 : (1 : ℝ) ≤ (Δk : ℝ) := by
    have hne : Δk ≠ 0 := by
      intro h
      rw [h] at hΔpos
      simp at hΔpos
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hne
  set p : ℝ := 1 / (2 * (r : ℝ) * Δk) with hp_def
  have hppos : 0 < p := by positivity
  have hp1 : p ≤ 1 := by
    rw [hp_def, div_le_one (by positivity)]
    nlinarith
  -- the survival factor is at least `1/2`
  have hrΔ : ((r * Δk : ℕ) : ℝ) = (r : ℝ) * (Δk : ℝ) := by push_cast; ring
  have hsurv : (1 : ℝ) / 2 ≤ (1 - p) ^ (r * Δk) := by
    have hb := one_sub_mul_le_pow_one_sub (p := p) hp1 (r * Δk)
    have hval : ((r * Δk : ℕ) : ℝ) * p = 1 / 2 := by
      rw [hrΔ, hp_def]
      field_simp
    rw [hval] at hb
    linarith
  -- the covering fraction is at least `1/(8r)`
  have hdkp : (1 : ℝ) / (4 * (r : ℝ)) ≤ dk * p := by
    rw [hp_def]
    rw [div_le_iff₀ (by positivity)]
    have h : dk * (1 / (2 * (r : ℝ) * (Δk : ℝ))) * (4 * (r : ℝ))
        = 2 * dk / (Δk : ℝ) := by
      field_simp
      ring
    rw [h, le_div_iff₀ hΔpos]
    linarith
  have hgain : (1 : ℝ) / (8 * (r : ℝ)) ≤ dk * p * (1 - p) ^ (r * Δk) := by
    have hdkp0 : (0 : ℝ) < dk * p := by positivity
    calc (1 : ℝ) / (8 * (r : ℝ)) = (1 / (4 * (r : ℝ))) * (1 / 2) := by ring
      _ ≤ (dk * p) * ((1 - p) ^ (r * Δk)) := by
          refine mul_le_mul hdkp hsurv (by norm_num) (le_of_lt hdkp0)
  have hfinal : (1 - η) * (1 / (8 * (r : ℝ)))
      ≤ (1 - η) * (dk * p * (1 - p) ^ (r * Δk)) :=
    mul_le_mul_of_nonneg_left hgain (by linarith)
  have hlhs : 1 - lam = (1 - η) / (8 * (r : ℝ)) := by simp only [hlam_def]; ring
  rw [hlhs]
  calc (1 - η) / (8 * (r : ℝ)) = (1 - η) * (1 / (8 * (r : ℝ))) := by ring
    _ ≤ (1 - η) * (dk * p * (1 - p) ^ (r * Δk)) := hfinal

end Nibble

/-
# Local: geometric density banding.

The bridge from the near-uniform coupled block cover (`blockCoverResidualCoupledNearUniform_holds`)
to general cluster densities partitions the density range `[δ, 1]` into geometric bands
`[δ(1+ρ)^i, δ(1+ρ)^{i+1}]`, each near-uniform with ratio `1 + ρ`.  This file proves the two
self-contained facts that partition needs:

* `exists_density_band` — every `x ∈ [δ, 1]` lies in some band;
* `density_band_count_le` — only finitely many bands meet `[δ, 1]`: the band index of any such `x`
  is `< N` for `N` with `1 ≤ δ (1+ρ)^N`.

No probability, no graph theory — pure ordered-field / archimedean arithmetic.
-/
import Mathlib.Analysis.RCLike.Basic

namespace Nibble.AX1

/-- **Every density in `[δ, 1]` lies in a geometric band.**  For `0 < δ` and `0 < ρ`, and any
`δ ≤ x ≤ 1`, there is an index `i` with `δ(1+ρ)^i ≤ x ≤ δ(1+ρ)^{i+1}`. -/
theorem exists_density_band {δ ρ : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ) {x : ℝ}
    (hx : δ ≤ x) :
    ∃ i : ℕ, δ * (1 + ρ) ^ i ≤ x ∧ x < δ * (1 + ρ) ^ (i + 1) := by
  have h1ρ : 1 < 1 + ρ := by linarith
  -- the ratio `y = x / δ ≥ 1`
  set y : ℝ := x / δ with hy
  have hy1 : 1 ≤ y := by
    rw [hy, le_div_iff₀ hδ]; linarith
  -- some power of `1+ρ` exceeds `y`
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt y h1ρ
  -- the least such power
  classical
  have hex : ∃ n : ℕ, y < (1 + ρ) ^ n := ⟨N, hN⟩
  set i₀ : ℕ := Nat.find hex with hi₀
  have hi₀spec : y < (1 + ρ) ^ i₀ := Nat.find_spec hex
  have hi₀pos : 0 < i₀ := by
    rcases Nat.eq_zero_or_pos i₀ with h | h
    · rw [h, pow_zero] at hi₀spec; linarith
    · exact h
  -- so `i₀ - 1` does not overshoot
  set i : ℕ := i₀ - 1 with hidef
  have hii : i₀ = i + 1 := by omega
  have hle : (1 + ρ) ^ i ≤ y := by
    have hlt : i < i₀ := by omega
    have := Nat.find_min hex hlt
    push_neg at this
    exact this
  rw [hii] at hi₀spec
  refine ⟨i, ?_, ?_⟩
  · rw [hy, le_div_iff₀ hδ] at hle; linarith only [hle]
  · rw [hy, div_lt_iff₀ hδ] at hi₀spec
    linarith only [hi₀spec]

/-- **Only finitely many bands meet `[δ, 1]`.**  If `1 ≤ δ (1+ρ)^N` then the band index of any
`x ≤ 1` produced by `exists_density_band` is `< N`. -/
theorem density_band_count_le {δ ρ : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ) {N : ℕ}
    (hN : (1 : ℝ) ≤ δ * (1 + ρ) ^ N) {x : ℝ} (hx1 : x ≤ 1) {i : ℕ}
    (hi : δ * (1 + ρ) ^ i ≤ x) : i ≤ N := by
  have h1ρ : (1 : ℝ) < 1 + ρ := by linarith
  by_contra h
  push_neg at h
  -- `N < i` ⇒ `(1+ρ)^N ≤ (1+ρ)^i`, so `1 ≤ δ(1+ρ)^N ≤ δ(1+ρ)^i ≤ x ≤ 1` forces monotone strict gap
  have hmono : (1 + ρ) ^ N < (1 + ρ) ^ i :=
    pow_lt_pow_right₀ h1ρ h
  have : δ * (1 + ρ) ^ N < δ * (1 + ρ) ^ i :=
    mul_lt_mul_of_pos_left hmono hδ
  linarith only [hi, hx1, this, hN]

end Nibble.AX1

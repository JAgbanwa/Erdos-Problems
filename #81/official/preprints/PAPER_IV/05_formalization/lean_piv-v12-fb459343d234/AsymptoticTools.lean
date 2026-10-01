import Mathlib

/-! Rational epsilon bounds and literal real-valued little-o statements. -/
namespace PaperIV.SublinearResearch
open Filter Asymptotics

theorem rational_isLittleO_iff (f g : ℕ → ℚ) :
    (fun n => (f n : ℝ)) =o[atTop] (fun n => (g n : ℝ)) ↔
      ∀ ε : ℚ, 0 < ε → ∀ᶠ n in atTop, |f n| ≤ ε*|g n| := by
  constructor
  · intro h ε hε
    have he : (0 : ℝ) < ε := by exact_mod_cast hε
    filter_upwards [h.bound he] with n hn
    simpa only [Real.norm_eq_abs, ← Rat.cast_abs, ← Rat.cast_mul,
      Rat.cast_le] using hn
  · intro h
    apply IsLittleO.of_bound
    intro ε hε
    obtain ⟨q,hq0,hqε⟩ := exists_rat_btwn hε
    have hq : (0 : ℚ) < q := by exact_mod_cast hq0
    filter_upwards [h q hq] with n hn
    have hn' : |(f n : ℝ)| ≤ (q : ℝ)*|(g n : ℝ)| := by exact_mod_cast hn
    simpa only [Real.norm_eq_abs] using
      hn'.trans (mul_le_mul_of_nonneg_right hqε.le (abs_nonneg _))

end PaperIV.SublinearResearch

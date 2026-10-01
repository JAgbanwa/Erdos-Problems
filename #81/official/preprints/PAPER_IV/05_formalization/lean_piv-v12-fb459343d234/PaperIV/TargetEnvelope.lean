import PaperIV.SharpEnvelope

/-!
# Integral target below the sharp envelope

The sharp quadratic envelope is deliberately π/24 above the continuous
quantity `n(n+1)/6`.  This module records the exact one-way comparison needed
when a rational estimate is converted to the integral target size.
-/

namespace PaperIV

def targetSize (n : ℕ) : ℕ := n * (n + 1) / 6

theorem targetSize_cast_le_continuous (n : ℕ) :
    (targetSize n : ℚ) ≤ (n : ℚ) * ((n : ℚ) + 1) / 6 := by
  have hnat : (n * (n + 1) / 6) * 6 ≤ n * (n + 1) :=
    Nat.div_mul_le_self _ _
  have hcast :
      ((n * (n + 1) / 6 : ℕ) : ℚ) * 6 ≤ ((n * (n + 1) : ℕ) : ℚ) := by
    exact_mod_cast hnat
  unfold targetSize
  apply (le_div_iff₀ (by norm_num : (0 : ℚ) < 6)).2
  simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] using hcast

theorem continuous_lt_sharpEnvelope (n : ℕ) :
    (n : ℚ) * ((n : ℚ) + 1) / 6 < sharpEnvelope n := by
  unfold sharpEnvelope
  have : (0 : ℚ) < 1 / 24 := by norm_num
  nlinarith

theorem targetSize_cast_lt_sharpEnvelope (n : ℕ) :
    (targetSize n : ℚ) < sharpEnvelope n :=
  lt_of_le_of_lt (targetSize_cast_le_continuous n) (continuous_lt_sharpEnvelope n)

end PaperIV

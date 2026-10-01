import Nibble.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Tactic.Positivity

/-!
# The elementary mass bound for fractional hypergraph matchings

This small module isolates the only declaration from the historical
`Nibble.WeightedNibble` file used by Paper IV.
-/

open Finset Hypergraph

namespace Nibble

/-- Every fractional matching of an `r`-uniform hypergraph has total weight at most `|W|/r`. -/
theorem fracMatching_sum_le {W : Type} [Fintype W] [DecidableEq W] {H : Finset (Finset W)}
    {r : ℕ} (hr : IsUniform H r) {w : Finset W → ℝ}
    (hcon : ∀ v : W, ∑ T ∈ H.filter (fun T => v ∈ T), w T ≤ 1) :
    (r : ℝ) * (∑ T ∈ H, w T) ≤ (Fintype.card W : ℝ) := by
  classical
  have expand : ∀ T ∈ H, ∑ v : W, (if v ∈ T then w T else 0) = (r : ℝ) * w T := by
    intro T hT
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, hr T hT, nsmul_eq_mul]
  calc (r : ℝ) * (∑ T ∈ H, w T)
      = ∑ T ∈ H, ∑ v : W, (if v ∈ T then w T else 0) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun T hT => (expand T hT).symm)
    _ = ∑ v : W, ∑ T ∈ H, (if v ∈ T then w T else 0) := Finset.sum_comm
    _ = ∑ v : W, ∑ T ∈ H.filter (fun T => v ∈ T), w T :=
        Finset.sum_congr rfl (fun v _ => by rw [Finset.sum_filter])
    _ ≤ ∑ _v : W, (1 : ℝ) := Finset.sum_le_sum (fun v _ => hcon v)
    _ = (Fintype.card W : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ]

end Nibble

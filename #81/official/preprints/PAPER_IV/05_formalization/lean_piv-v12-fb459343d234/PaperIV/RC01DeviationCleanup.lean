import PaperIV.CopyCleanup
import PaperIV.RC01CanonicalNormalization

/-!
# RC01: two-sided rooted cleanup and physical spread

This module packages the exact bridge between the rooted second-moment estimate
and the slack canonical fractional packing.  A root is removed when its count
deviates from the reference value `A` by more than `u * A`.  Every surviving
root therefore has both the lower and upper count bounds.  The upper bound,
after multiplication by the physical volume of the root pair, is precisely the
spread hypothesis used by `budgetPacking`.

The statements are abstract: the K3 and K4 rooted-counting modules instantiate
`c`, `A`, and the physical pair volume separately.
-/

namespace PaperIV.RC01DeviationCleanup

open Finset
open PaperIV.RootedCountingBridge
open PaperIV.CopyCleanup

variable {κ ρ ι : Type*} [DecidableEq κ] [DecidableEq ρ]
  [Fintype ι] [DecidableEq ι]

/-- Roots whose count differs from its reference value by more than the
relative tolerance `u`.  This is deliberately two-sided. -/
def deviationBad (E : Finset ρ) (c : ρ → ℚ) (A u : ℚ) : Finset ρ :=
  E.filter (fun e => u * A < |c e - A|)

theorem mem_deviationBad_iff {E : Finset ρ} {c : ρ → ℚ} {A u : ℚ} {e : ρ} :
    e ∈ deviationBad E c A u ↔ e ∈ E ∧ u * A < |c e - A| := by
  simp [deviationBad]

/-- The generic Chebyshev estimate, exposed with the RC01 bad-root name. -/
theorem card_deviationBad_mul_le (E : Finset ρ) (c : ρ → ℚ) (A u S : ℚ)
    (hu : 0 < u) (hA : 0 < A)
    (hsecond : ∑ e ∈ E, (c e - A) ^ 2 ≤ S) :
    ((deviationBad E c A u).card : ℚ) * (u * A) ^ 2 ≤ S := by
  simpa [deviationBad] using
    PaperIV.RootedCounting.card_bad_roots_le E c A u S hu hA hsecond

/-- A root outside the two-sided exceptional set is within relative error `u`
of the reference count. -/
theorem abs_count_sub_le_of_notMem_deviationBad
    {E : Finset ρ} {c : ρ → ℚ} {A u : ℚ} {e : ρ}
    (he : e ∈ E) (hgood : e ∉ deviationBad E c A u) :
    |c e - A| ≤ u * A := by
  rw [deviationBad, Finset.mem_filter, not_and, not_lt] at hgood
  exact hgood he

/-- Both pointwise count inequalities supplied by a good root. -/
theorem count_bounds_of_notMem_deviationBad
    {E : Finset ρ} {c : ρ → ℚ} {A u : ℚ} {e : ρ}
    (he : e ∈ E) (hgood : e ∉ deviationBad E c A u) :
    (1 - u) * A ≤ c e ∧ c e ≤ (1 + u) * A := by
  have h := abs_le.1 (abs_count_sub_le_of_notMem_deviationBad he hgood)
  constructor <;> nlinarith

/-- Cleaning on all root positions preserves the two-sided upper count bound.
Only the upper half is needed for fractional feasibility. -/
theorem cleaned_count_le_of_deviationGood
    (Cs : Finset κ) (rt : ι → κ → ρ) (E : ι → Finset ρ)
    (c : ι → ρ → ℚ) (A u : ι → ℚ)
    (hc : ∀ i e, c i e = ((fiber Cs (rt i) e).card : ℚ))
    {i : ι} {e : ρ} (he : e ∈ E i)
    (hgood : e ∉ deviationBad (E i) (c i) (A i) (u i)) :
    ((fiber (cleaned Cs rt
      (fun j => deviationBad (E j) (c j) (A j) (u j))) (rt i) e).card : ℚ)
      ≤ (1 + u i) * A i := by
  apply cleaned_count_le Cs rt
    (fun j => deviationBad (E j) (c j) (A j) (u j)) i e
  rw [← hc i e]
  exact (count_bounds_of_notMem_deviationBad he hgood).2

/-- Physical spread after cleanup.  This is the literal hypothesis expected by
`RC01CanonicalNormalization.budgetPacking` when the budget is
`(1+u) * A * pairVolume`. -/
theorem cleaned_count_mul_volume_le_budget
    (Cs : Finset κ) (rt : ι → κ → ρ) (E : ι → Finset ρ)
    (c : ι → ρ → ℚ) (A u : ι → ℚ)
    (hc : ∀ i e, c i e = ((fiber Cs (rt i) e).card : ℚ))
    {i : ι} {e : ρ} {pairVolume : ℚ} (hvolume : 0 ≤ pairVolume)
    (he : e ∈ E i)
    (hgood : e ∉ deviationBad (E i) (c i) (A i) (u i)) :
    ((fiber (cleaned Cs rt
      (fun j => deviationBad (E j) (c j) (A j) (u j))) (rt i) e).card : ℚ)
        * pairVolume
      ≤ (1 + u i) * (A i * pairVolume) := by
  have hcount := cleaned_count_le_of_deviationGood Cs rt E c A u hc he hgood
  have := mul_le_mul_of_nonneg_right hcount hvolume
  nlinarith

/-- A bound on the number of removed copies becomes the corresponding lower
bound on the clean fibre.  Keeping the reference scale explicit avoids any
renormalization by the random clean cardinality. -/
theorem cleaned_card_ge_of_removed_le
    (Cs : Finset κ) (rt : ι → κ → ρ) (Bad : ι → Finset ρ)
    {reference v : ℚ}
    (href : reference ≤ (Cs.card : ℚ))
    (hremoved : ((removed Cs rt Bad).card : ℚ) ≤ v * reference) :
    (1 - v) * reference ≤ ((cleaned Cs rt Bad).card : ℚ) := by
  have hpartition := card_cleaned_add_removed Cs rt Bad
  have hpartitionQ : ((cleaned Cs rt Bad).card : ℚ)
      + ((removed Cs rt Bad).card : ℚ) = (Cs.card : ℚ) := by
    exact_mod_cast hpartition
  nlinarith

end PaperIV.RC01DeviationCleanup

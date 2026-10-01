import PaperIV.RC01CanonicalFiberProfile
import PaperIV.RC01CleanedGate

/-!
# RC01: exact aggregate value of the canonical mixed pool

The canonical K3/K4 fibres are now known to be literal, pairwise disjoint
profile fibres.  This module performs the remaining exact bookkeeping before
any regularity estimate: the value carried by their union is precisely the
weighted sum of their raw masses.  It also splits `x.value` into that canonical
value and one explicit nonnegative off-pool remainder.

Thus the quantitative remainder of RC01 is reduced to bounding
`offCanonicalValue`; there is no longer a multiplicity or tag-forgetting loss.
-/

namespace PaperIV.RC01CanonicalValueAccounting

open Finset
open PaperIV.FarRounding
open PaperIV.RegularityFormat
open PaperIV.PartitionBridge
open PaperIV.RC01CleanFiber
open PaperIV.RC01CleanedGate
open PaperIV.RC01MixedPatterns
open PaperIV.RC01CanonicalProfile
open PaperIV.RC01CanonicalFiberProfile
open PaperIV.RC01PatternCapacity

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The literal LP value carried by a selected family of canonical fibres. -/
noncomputable def canonicalValue {δ : ℚ} (R : EqualRegularity G δ)
    (x : FracPacking G ℚ) (Active : Finset (MixedPattern V)) : ℚ :=
  ∑ K ∈ Active.biUnion (mixedFiber R), gainF ℚ K * x.weight K

/-- The complementary LP value outside the selected canonical fibres. -/
noncomputable def offCanonicalValue {δ : ℚ} (R : EqualRegularity G δ)
    (x : FracPacking G ℚ) (Active : Finset (MixedPattern V)) : ℚ :=
  ∑ K ∈ (items G).filter (fun K => K ∉ Active.biUnion (mixedFiber R)),
    gainF ℚ K * x.weight K

/-- Every item of a selected canonical family is a literal mixed item. -/
theorem canonicalUnion_subset_items {δ : ℚ} (R : EqualRegularity G δ)
    (Active : Finset (MixedPattern V)) (hActive : Active ⊆ mixedPatterns R) :
    Active.biUnion (mixedFiber R) ⊆ items G := by
  intro K hK
  obtain ⟨σ, hσ, hKσ⟩ := Finset.mem_biUnion.1 hK
  exact mixedFiber_subset_items R (hActive hσ) hKσ

/-- Exact aggregate owner/value identity.  K3 profiles contribute gain `2`
and K4 profiles gain `5`, expressed uniformly by `patternGain`. -/
theorem canonicalValue_eq_sum_rawMass {δ : ℚ} (R : EqualRegularity G δ)
    (x : FracPacking G ℚ) (Active : Finset (MixedPattern V))
    (hActive : Active ⊆ mixedPatterns R) :
    canonicalValue R x Active =
      ∑ σ ∈ Active,
        patternGain (profileOfMixed σ) * rawMass x (mixedFiber R) σ := by
  classical
  rw [canonicalValue,
    Finset.sum_biUnion (mixedFiber_pairwiseDisjoint_of_subset R Active hActive)]
  refine Finset.sum_congr rfl ?_
  intro σ hσ
  rw [rawMass, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro K hK
  have hprof : K ∈ profileFiber G (partOf R) (profileOfMixed σ) :=
    (mem_mixedFiber_iff_mem_profileFiber R (hActive hσ)).1 hK
  have hcard := (mem_profileFiber.1 hprof).2.2
  rw [gainF, patternGain, hcard]

/-- The canonical value is nonnegative. -/
theorem canonicalValue_nonneg {δ : ℚ} (R : EqualRegularity G δ)
    (x : FracPacking G ℚ) (Active : Finset (MixedPattern V))
    (hActive : Active ⊆ mixedPatterns R) :
    0 ≤ canonicalValue R x Active := by
  rw [canonicalValue]
  refine Finset.sum_nonneg fun K hK => ?_
  exact mul_nonneg
    (PaperIV.PatternMass.gainF_nonneg
      (mem_items.1 (canonicalUnion_subset_items R Active hActive hK)))
    (x.weight_nonneg K)

/-- The off-pool remainder is nonnegative. -/
theorem offCanonicalValue_nonneg {δ : ℚ} (R : EqualRegularity G δ)
    (x : FracPacking G ℚ) (Active : Finset (MixedPattern V)) :
    0 ≤ offCanonicalValue R x Active := by
  rw [offCanonicalValue]
  refine Finset.sum_nonneg fun K hK => ?_
  exact mul_nonneg
    (PaperIV.PatternMass.gainF_nonneg (mem_items.1 (Finset.mem_filter.1 hK).1))
    (x.weight_nonneg K)

/-- If every item outside the canonical pool touches a discarded physical
edge, the whole residual value is paid by five times the discard count.  This
is the exact interface between the new one-residual formulation and the
already proved incidence budget of `PatternMass`. -/
theorem offCanonicalValue_le_five_mul_discards {δ : ℚ}
    (R : EqualRegularity G δ) (x : FracPacking G ℚ)
    (Active : Finset (MixedPattern V)) (B : Finset (Sym2 V))
    (hB : ∀ e ∈ B, e ∈ G.edgeFinset)
    (hmeet : ∀ K ∈ (items G).filter
        (fun K => K ∉ Active.biUnion (mixedFiber R)),
      ∃ e ∈ B, e ∈ pairs K) :
    offCanonicalValue R x Active ≤ 5 * (B.card : ℚ) := by
  rw [offCanonicalValue]
  exact PaperIV.PatternMass.gain_of_discards_le x B hB _
    (fun K hK => (Finset.mem_filter.1 hK).1) hmeet

/-- Exact partition of the original objective into canonical and off-pool
value. -/
theorem value_eq_canonical_add_off {δ : ℚ} (R : EqualRegularity G δ)
    (x : FracPacking G ℚ) (Active : Finset (MixedPattern V))
    (hActive : Active ⊆ mixedPatterns R) :
    x.value = canonicalValue R x Active + offCanonicalValue R x Active := by
  classical
  let U := Active.biUnion (mixedFiber R)
  have hsub : U ⊆ items G := canonicalUnion_subset_items R Active hActive
  have hfilter : (items G).filter (fun K => K ∈ U) = U := by
    ext K
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hsub h, h⟩⟩
  rw [FracPacking.value, canonicalValue, offCanonicalValue]
  calc
    (∑ K ∈ items G, gainF ℚ K * x.weight K) =
        (∑ K ∈ (items G).filter (fun K => K ∈ U), gainF ℚ K * x.weight K) +
          ∑ K ∈ (items G).filter (fun K => K ∉ U), gainF ℚ K * x.weight K :=
      (Finset.sum_filter_add_sum_filter_not (items G)
        (fun K => K ∈ U) (fun K => gainF ℚ K * x.weight K)).symm
    _ = (∑ K ∈ U, gainF ℚ K * x.weight K) +
          ∑ K ∈ (items G).filter (fun K => K ∉ U), gainF ℚ K * x.weight K := by
      rw [hfilter]

end PaperIV.RC01CanonicalValueAccounting

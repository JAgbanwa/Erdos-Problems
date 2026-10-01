import PaperIV.RC01ResidualTransferClosure
import PaperIV.CleanedTriangleMass

/-!
# RC01: the triangular half of the residual transfer

`RC01ResidualTransferClosure.value_sub_dense_regularity_budget_le_profiles`
transfers the **whole** objective to the dense active profiles.  The cleaned
physical gate also needs the *triangular* half of that statement, because its
only remaining hypothesis is a lower bound on the triangle mass of the cleaned
packing, and `CleanedTriangleMass.cleanedPacking_triMass_ge` expresses that mass
through the transferred masses of the three-part profiles.

The proof needs no new geometry.  A triangle carries gain `2 ≥ 1`, so the
triangular mass living outside the selected canonical fibres is dominated by the
residual *value* already bounded in `RC01ResidualCoverage`; and every canonical
fibre is a literal profile fibre (`RC01CanonicalFiberProfile`), transversal, so
the triangles it contains are exactly the items of a three-part profile.
-/

namespace PaperIV.RC01TriangleTransfer

open Finset
open MixedRounding
open PaperIV.RegularityFormat
open PaperIV.PartitionBridge
open PaperIV.PatternTransfer
open PaperIV.RC01CleanFiber
open PaperIV.RC01MixedPatterns
open PaperIV.RC01CanonicalProfile
open PaperIV.RC01CanonicalFiberProfile
open PaperIV.RC01CanonicalValueAccounting
open PaperIV.RC01ResidualCoverage
open PaperIV.RC01ResidualTransferClosure

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {G : SimpleGraph α} [DecidableRel G.Adj]

/-- The mass of the triangles of one canonical fibre is at most the transferred
mass of its profile. -/
theorem sum_mixedFiber_weight_le_psiT {δ : ℚ} (R : EqualRegularity G δ)
    (x : FracPacking G) {σ : MixedPattern α} (hσ : σ ∈ mixedPatterns R) :
    ∑ K ∈ mixedFiber R σ, x.weight K ≤ psiT x (partOf R) (profileOfMixed σ) := by
  classical
  rw [psiT, mixedFiber_eq_profileFiber R hσ]
  calc ∑ K ∈ profileFiber G (partOf R) (profileOfMixed σ), x.weight K
      = ∑ K ∈ profileFiber G (partOf R) (profileOfMixed σ),
          (if K.image (partOf R) = profileOfMixed σ then x.weight K else 0) :=
        Finset.sum_congr rfl fun K hK => by
          rw [if_pos (mem_profileFiber.1 hK).2.1]
    _ ≤ ∑ K ∈ items G,
          (if K.image (partOf R) = profileOfMixed σ then x.weight K else 0) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg
          (profileFiber_subset_items (partOf R) _) ?_
        intro K _ _
        split
        · exact x.weight_nonneg K
        · exact le_rfl

/-- **The triangular transfer.**  The triangle mass of `x` is carried by the
three-part dense active profiles, up to the residual value already charged by
`RC01ResidualCoverage`. -/
theorem triMass_le_denseActive_triangles_add_offCanonical {δ : ℚ}
    (R : EqualRegularity G δ) (x : FracPacking G) (d θ : ℚ) :
    PaperIV.LowTriangleReduction.triMass x ≤
      (∑ H ∈ (denseActiveProfiles R x d θ).filter (fun H => H.card = 3),
        psiT x (partOf R) H)
      + offCanonicalValue R (PaperIV.MixedRoundingAdapter.toFarFrac x)
          (denseHeavyPatterns R (PaperIV.MixedRoundingAdapter.toFarFrac x) d θ) := by
  classical
  set x' := PaperIV.MixedRoundingAdapter.toFarFrac x with hx'
  set Active := denseHeavyPatterns R x' d θ with hActiveDef
  have hsub : Active ⊆ mixedPatterns R := denseHeavyPatterns_subset R x' d θ
  set U := Active.biUnion (mixedFiber R) with hU
  set T := (items G).filter (fun K => K.card = 3) with hT
  have hsplit : PaperIV.LowTriangleReduction.triMass x
      = (∑ K ∈ T.filter (fun K => K ∈ U), x.weight K)
        + ∑ K ∈ T.filter (fun K => ¬ K ∈ U), x.weight K := by
    rw [PaperIV.LowTriangleReduction.triMass, ← hT]
    exact (Finset.sum_filter_add_sum_filter_not T _ _).symm
  -- (a) the triangles inside the selected canonical fibres
  set Act3 := Active.filter (fun σ => (profileOfMixed σ).card = 3) with hAct3
  have hsubset : T.filter (fun K => K ∈ U) ⊆ Act3.biUnion (mixedFiber R) := by
    intro K hK
    have hKT : K ∈ T := (Finset.mem_filter.1 hK).1
    have hKU : K ∈ U := (Finset.mem_filter.1 hK).2
    have hK3 : K.card = 3 := (Finset.mem_filter.1 hKT).2
    obtain ⟨σ, hσ, hKσ⟩ := Finset.mem_biUnion.1 hKU
    refine Finset.mem_biUnion.2 ⟨σ, Finset.mem_filter.2 ⟨hσ, ?_⟩, hKσ⟩
    have hKprof : K ∈ profileFiber G (partOf R) (profileOfMixed σ) := by
      rwa [← mixedFiber_eq_profileFiber R (hsub hσ)]
    have hcard := (mem_profileFiber.1 hKprof).2.2
    omega
  have hAnn : ∀ K ∈ Act3.biUnion (mixedFiber R), 0 ≤ x.weight K :=
    fun K _ => x.weight_nonneg K
  have hdisj : (Act3 : Set (MixedPattern α)).PairwiseDisjoint (mixedFiber R) := by
    intro σ hσ τ hτ hne
    exact mixedFiber_pairwiseDisjoint R
      (hsub (Finset.mem_filter.1 hσ).1) (hsub (Finset.mem_filter.1 hτ).1) hne
  have hA : (∑ K ∈ T.filter (fun K => K ∈ U), x.weight K)
      ≤ ∑ H ∈ (denseActiveProfiles R x d θ).filter (fun H => H.card = 3),
          psiT x (partOf R) H := by
    have hda : denseActiveProfiles R x d θ = Active.image profileOfMixed := rfl
    have himg : (denseActiveProfiles R x d θ).filter (fun H => H.card = 3)
        = Act3.image profileOfMixed := by
      rw [hda, Finset.filter_image, ← hAct3]
    rw [himg, Finset.sum_image
      (fun σ hσ τ hτ h => profileOfMixed_injOn R
        (hsub (Finset.mem_filter.1 hσ).1) (hsub (Finset.mem_filter.1 hτ).1) h)]
    calc (∑ K ∈ T.filter (fun K => K ∈ U), x.weight K)
        ≤ ∑ K ∈ Act3.biUnion (mixedFiber R), x.weight K :=
          Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun K hK _ => hAnn K hK)
      _ = ∑ σ ∈ Act3, ∑ K ∈ mixedFiber R σ, x.weight K :=
          Finset.sum_biUnion hdisj
      _ ≤ ∑ σ ∈ Act3, psiT x (partOf R) (profileOfMixed σ) :=
          Finset.sum_le_sum fun σ hσ =>
            sum_mixedFiber_weight_le_psiT R x (hsub (Finset.mem_filter.1 hσ).1)
  -- (b) the triangles outside them are paid by the residual value
  have hB : (∑ K ∈ T.filter (fun K => ¬ K ∈ U), x.weight K)
      ≤ offCanonicalValue R x' Active := by
    rw [offCanonicalValue]
    have hstep : ∀ K ∈ T.filter (fun K => ¬ K ∈ U),
        x.weight K ≤ PaperIV.FarRounding.gainF ℚ K * x'.weight K := by
      intro K hK
      have hK3 : K.card = 3 := (Finset.mem_filter.1 (Finset.mem_filter.1 hK).1).2
      have hw : x'.weight K = x.weight K := rfl
      have hg : PaperIV.FarRounding.gainF ℚ K = 2 := by
        rw [PaperIV.FarRounding.gainF, hK3]
        norm_num
      rw [hw, hg]
      have := x.weight_nonneg K
      linarith
    have hsub2 : T.filter (fun K => ¬ K ∈ U)
        ⊆ (PaperIV.FarRounding.items G).filter (fun K => ¬ K ∈ U) := by
      intro K hK
      have hKT : K ∈ T := (Finset.mem_filter.1 hK).1
      refine Finset.mem_filter.2 ⟨?_, (Finset.mem_filter.1 hK).2⟩
      rw [← PaperIV.MixedRoundingAdapter.items_eq]
      exact (Finset.mem_filter.1 hKT).1
    calc (∑ K ∈ T.filter (fun K => ¬ K ∈ U), x.weight K)
        ≤ ∑ K ∈ T.filter (fun K => ¬ K ∈ U),
            PaperIV.FarRounding.gainF ℚ K * x'.weight K := Finset.sum_le_sum hstep
      _ ≤ ∑ K ∈ (PaperIV.FarRounding.items G).filter (fun K => ¬ K ∈ U),
            PaperIV.FarRounding.gainF ℚ K * x'.weight K := by
          refine Finset.sum_le_sum_of_subset_of_nonneg hsub2 ?_
          intro K hK _
          have hitem : K ∈ PaperIV.FarRounding.items G := (Finset.mem_filter.1 hK).1
          exact mul_nonneg
            (PaperIV.PatternMass.gainF_nonneg (PaperIV.FarRounding.mem_items.1 hitem))
            (x'.weight_nonneg K)
  rw [hsplit]
  linarith

/-- The triangular transfer with the literal `(15.1)` budget. -/
theorem triMass_le_denseActive_triangles_add_budget {δ : ℚ} (hδ : 0 ≤ δ)
    (R : EqualRegularity G δ) (x : FracPacking G) (d θ : ℚ)
    (hd : 0 ≤ d) (hθ : 0 ≤ θ) {k₀ : ℕ} (hk₀ : 0 < k₀)
    (hk : k₀ ≤ R.parts.card) :
    PaperIV.LowTriangleReduction.triMass x ≤
      (∑ H ∈ (denseActiveProfiles R x d θ).filter (fun H => H.card = 3),
        psiT x (partOf R) H)
      + (5 * ((3 * δ + 1 / (k₀ : ℚ) + d) * (Fintype.card α : ℚ) ^ 2)
          + 5 * (((mixedPatterns R).card : ℚ) * θ)) := by
  have h1 := triMass_le_denseActive_triangles_add_offCanonical R x d θ
  have h2 := offCanonicalValue_le_dense_regularity_budget hδ R
    (PaperIV.MixedRoundingAdapter.toFarFrac x) d θ hd hθ hk₀ hk
  linarith

end PaperIV.RC01TriangleTransfer


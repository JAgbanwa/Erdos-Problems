import PaperIV.RC01RootwiseRetention
import PaperIV.RC01ResidualTransferClosure
import PaperIV.RootedK3Pool

/-!
# RC01: rootwise retention for every active dense profile

This is the geometric adapter between the canonical dense-profile family and
the simultaneous root-cleanup theorem.  It introduces no rounding assumption:
membership in `denseHeavyPatterns` supplies density, while membership in the
canonical K3/K4 pools supplies regularity of every pair.
-/

namespace PaperIV.RC01DenseRootwiseRetention

open Finset
open MixedRounding
open PaperIV.OneStepEstimate
open PaperIV.PatternCounting
open PaperIV.PatternPoolGeometry
open PaperIV.RegularityFormat
open PaperIV.PartitionBridge
open PaperIV.RC01Candidates
open PaperIV.RC01CandidatePool
open PaperIV.RC01CanonicalSlots
open PaperIV.RC01K3Pool
open PaperIV.RC01MixedPatterns
open PaperIV.RC01CanonicalProfile
open PaperIV.RC01CleanFiber
open PaperIV.RC01RootwiseReference
open PaperIV.RC01RegularVolume
open PaperIV.RC01ResidualCoverage
open PaperIV.RC01ResidualTransferClosure

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
variable {G : SimpleGraph α} [DecidableRel G.Adj]

private theorem canonicalTriple_mem_slot {δ : ℚ} (R : EqualRegularity G δ)
    {S : Finset (Finset α)} (hS : S ∈ goodK3Slots R) (i : Fin 3) :
    canonicalTripleOf R S i ∈ S := by
  have hmem : canonicalTripleOf R S i ∈ partImageOf (canonicalTripleOf R S) :=
    Finset.mem_image.2 ⟨i, Finset.mem_univ i, rfl⟩
  rwa [(canonicalTripleOf_spec R hS).2] at hmem

private theorem canonicalTuple_mem_slot {δ : ℚ} (R : EqualRegularity G δ)
    {S : Finset (Finset α)} (hS : S ∈ goodK4Slots R) (i : Fin 4) :
    canonicalTuple R S i ∈ S := by
  have hmem : canonicalTuple R S i ∈ partImage (canonicalTuple R S) :=
    Finset.mem_image.2 ⟨i, Finset.mem_univ i, rfl⟩
  rwa [(canonicalTuple_spec R hS).2] at hmem

/-- Literal lower volume of a dense-heavy canonical pattern.  The disjunction
keeps the two physical scales (`t^3` and `t^4`) separate. -/
theorem denseHeavyPattern_profileVolume_lower {δ d θ : ℚ}
    (hδ : 0 ≤ δ) (hd : 0 ≤ d)
    (R : EqualRegularity G δ) (x : FracPacking G)
    {σ : MixedPattern α}
    (hσ : σ ∈ denseHeavyPatterns R (PaperIV.MixedRoundingAdapter.toFarFrac x) d θ) :
    ((profileOfMixed σ).card = 3 ∧
      (d ^ 3 - 3 * δ) * (R.size : ℚ) ^ 3 ≤
        profileVolume (G := G) (partOf R) (profileOfMixed σ)) ∨
    ((profileOfMixed σ).card = 4 ∧
      (d ^ 6 - 6 * δ) * (R.size : ℚ) ^ 4 ≤
        profileVolume (G := G) (partOf R) (profileOfMixed σ)) := by
  classical
  have hσdata : σ ∈ mixedPatterns R ∧
      IsDensePattern G R d σ ∧
        θ ≤ PaperIV.RC01PatternCapacity.rawMass
          (PaperIV.MixedRoundingAdapter.toFarFrac x) (mixedFiber R) σ := by
    simpa [denseHeavyPatterns] using hσ
  rcases (mem_mixedPatterns_iff.1 hσdata.1) with ⟨S, hS, rfl⟩ | ⟨S, hS, rfl⟩
  · left
    refine ⟨by
      simpa using card_profileOfMixed R
        (mem_mixedPatterns_iff.2 (Or.inl ⟨S, hS, rfl⟩)), ?_⟩
    have hgood := (mem_goodK3Tuples.1 (canonicalTripleOf_spec R hS).1).2.2
    have hdense : ∀ e ∈ patK3,
        d ≤ G.edgeDensity (canonicalTripleOf R S e.1) (canonicalTripleOf R S e.2) := by
      intro e he
      exact hσdata.2.1 _ (canonicalTriple_mem_slot R hS e.1) _
        (canonicalTriple_mem_slot R hS e.2)
        (canonicalTripleOf_ne R hS (patK3_ne e he))
    have hvolume : (d ^ 3 - 3 * δ) * (R.size : ℚ) ^ 3 ≤
        profileVolume (G := G) (partOf R)
          (regularPattern (canonicalTripleOf R S)) := by
      calc
        (d ^ 3 - 3 * δ) * (R.size : ℚ) ^ 3
            ≤ patCount G (canonicalTripleOf R S) patK3 :=
              patCount_K3_ge hδ hd R (canonicalTripleOf R S)
                (canonicalTripleOf_mem_parts R hS)
                (fun e he hEq => patK3_ne e he
                  ((PaperIV.RC01CanonicalFiberProfile.canonicalTripleOf_injective R hS) hEq))
                hgood hdense
        _ ≤ profileVolume (G := G) (partOf R)
              (regularPattern (canonicalTripleOf R S)) := by
              rw [profileVolume_eq_card]
              exact patCount_K3_le_profileFiber R (canonicalTripleOf R S)
                (canonicalTripleOf_mem_parts R hS)
                (PaperIV.RC01CanonicalFiberProfile.canonicalTripleOf_injective R hS)
    simpa [regularPattern_canonicalTriple R hS] using hvolume
  · right
    refine ⟨by
      simpa using card_profileOfMixed R
        (mem_mixedPatterns_iff.2 (Or.inr ⟨S, hS, rfl⟩)), ?_⟩
    have hdata := mem_goodK4Tuples.1 (canonicalTuple_spec R hS).1
    have hdense : ∀ e ∈ patK4,
        d ≤ G.edgeDensity (canonicalTuple R S e.1) (canonicalTuple R S e.2) := by
      intro e he
      exact hσdata.2.1 _ (canonicalTuple_mem_slot R hS e.1) _
        (canonicalTuple_mem_slot R hS e.2)
        (PaperIV.RootedK4Degree.canonicalTuple_ne R hS (patK4_ne e he))
    have hvolume : (d ^ 6 - 6 * δ) * (R.size : ℚ) ^ 4 ≤
        profileVolume (G := G) (partOf R) (regularPattern (canonicalTuple R S)) := by
      calc
        (d ^ 6 - 6 * δ) * (R.size : ℚ) ^ 4
            ≤ patCount G (canonicalTuple R S) patK4 :=
              patCount_K4_ge hδ hd R (canonicalTuple R S) hdata.1
                (fun e he hEq => patK4_ne e he
                  ((PaperIV.RC01CanonicalFiberProfile.canonicalTuple_injective R hS) hEq))
                hdata.2.2 hdense
        _ ≤ profileVolume (G := G) (partOf R) (regularPattern (canonicalTuple R S)) := by
              rw [profileVolume_eq_card]
              exact patCount_K4_le_profileFiber R (canonicalTuple R S) hdata.1
                (PaperIV.RC01CanonicalFiberProfile.canonicalTuple_injective R hS)
    simpa [regularPattern_canonicalTuple R hS] using hvolume

/-- Every active dense profile has positive literal physical volume once both
regular counting coefficients are positive. -/
theorem denseActiveProfiles_profileVolume_pos {δ d θ : ℚ}
    (hδ : 0 ≤ δ) (hd : 0 ≤ d)
    (hc3 : 0 < d ^ 3 - 3 * δ) (hc4 : 0 < d ^ 6 - 6 * δ)
    (R : EqualRegularity G δ) (x : FracPacking G) :
    ∀ H ∈ denseActiveProfiles R x d θ,
      0 < profileVolume (G := G) (partOf R) H := by
  classical
  intro H hH
  obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.1 hH
  rcases denseHeavyPattern_profileVolume_lower hδ hd R x hσ with h3 | h4
  · have ht : (0 : ℚ) < R.size := by exact_mod_cast R.size_pos
    exact lt_of_lt_of_le (mul_pos hc3 (pow_pos ht 3)) h3.2
  · have ht : (0 : ℚ) < R.size := by exact_mod_cast R.size_pos
    exact lt_of_lt_of_le (mul_pos hc4 (pow_pos ht 4)) h4.2

/-- Untagged lower-volume form used by the physical gate. -/
theorem denseActiveProfiles_profileVolume_lower {δ d θ : ℚ}
    (hδ : 0 ≤ δ) (hd : 0 ≤ d)
    (R : EqualRegularity G δ) (x : FracPacking G) :
    ∀ H ∈ denseActiveProfiles R x d θ,
      (H.card = 3 ∧ (d ^ 3 - 3 * δ) * (R.size : ℚ) ^ 3 ≤
        profileVolume (G := G) (partOf R) H) ∨
      (H.card = 4 ∧ (d ^ 6 - 6 * δ) * (R.size : ℚ) ^ 4 ≤
        profileVolume (G := G) (partOf R) H) := by
  classical
  intro H hH
  obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.1 hH
  exact denseHeavyPattern_profileVolume_lower hδ hd R x hσ

/-- Every dense-heavy tagged canonical pattern retains a `(1-v)` fraction of
its literal physical fibre after all of its roots are cleaned simultaneously. -/
theorem denseHeavyPattern_clean_retention {δ d u v θ : ℚ}
    (hδ : 0 ≤ δ) (hd : 0 ≤ d) (hu : 0 < u) (hv : 0 ≤ v)
    (hc3 : 0 < d ^ 3 - 3 * δ) (hc4 : 0 < d ^ 6 - 6 * δ)
    (hchoice3 : 33 * δ ≤ v * u ^ 2 * (d ^ 3 - 3 * δ) ^ 3)
    (hchoice4 : 138 * δ ≤ v * u ^ 2 * (d ^ 6 - 6 * δ) ^ 3)
    (R : EqualRegularity G δ) (x : FracPacking G)
    {σ : MixedPattern α}
    (hσ : σ ∈ denseHeavyPatterns R (PaperIV.MixedRoundingAdapter.toFarFrac x) d θ) :
    (1 - v) * profileVolume (G := G) (partOf R) (profileOfMixed σ) ≤
      ((cleanFiber G (partOf R) (rootwiseReference (G := G) (partOf R)) u
        (profileOfMixed σ)).card : ℚ) := by
  classical
  have hσdata : σ ∈ mixedPatterns R ∧
      IsDensePattern G R d σ ∧
        θ ≤ PaperIV.RC01PatternCapacity.rawMass
          (PaperIV.MixedRoundingAdapter.toFarFrac x) (mixedFiber R) σ := by
    simpa [denseHeavyPatterns] using hσ
  rcases (mem_mixedPatterns_iff.1 hσdata.1) with ⟨S, hS, rfl⟩ | ⟨S, hS, rfl⟩
  · have hgood := (mem_goodK3Tuples.1 (canonicalTripleOf_spec R hS).1).2.2
    have hdense : ∀ e ∈ patK3,
        d ≤ G.edgeDensity (canonicalTripleOf R S e.1) (canonicalTripleOf R S e.2) := by
      intro e he
      exact hσdata.2.1 _ (canonicalTriple_mem_slot R hS e.1) _
        (canonicalTriple_mem_slot R hS e.2)
        (canonicalTripleOf_ne R hS (patK3_ne e he))
    simpa [regularPattern_canonicalTriple R hS] using
      (PaperIV.RC01RootwiseRetention.cleanFiber_card_ge_regular_K3
        hδ hd hu hv hc3 R (canonicalTripleOf R S)
        (canonicalTripleOf_mem_parts R hS)
        (PaperIV.RC01CanonicalFiberProfile.canonicalTripleOf_injective R hS)
        (canonicalTripleOf_card R hS)
        (fun i j hij => PaperIV.RootedK3Degree.canonicalTripleOf_discrep R hS hij)
        hgood hdense hchoice3)
  · have hdata := mem_goodK4Tuples.1 (canonicalTuple_spec R hS).1
    have hdense : ∀ e ∈ patK4,
        d ≤ G.edgeDensity (canonicalTuple R S e.1) (canonicalTuple R S e.2) := by
      intro e he
      exact hσdata.2.1 _ (canonicalTuple_mem_slot R hS e.1) _
        (canonicalTuple_mem_slot R hS e.2)
        (PaperIV.RootedK4Degree.canonicalTuple_ne R hS (patK4_ne e he))
    simpa [regularPattern_canonicalTuple R hS] using
      (PaperIV.RC01RootwiseRetention.cleanFiber_card_ge_regular_K4
        hδ hd hu hv hc4 R (canonicalTuple R S)
        hdata.1
        (PaperIV.RC01CanonicalFiberProfile.canonicalTuple_injective R hS)
        (fun i => R.card_part _ (hdata.1 i))
        (fun i j hij => PaperIV.RootedK4Degree.canonicalTuple_discrep R hS hij)
        hdata.2.2 hdense hchoice4)

/-- Untagged form consumed directly by `RC01CleanedGate`: the same retention
bound holds uniformly for every profile in `denseActiveProfiles`. -/
theorem denseActiveProfiles_clean_retention {δ d u v θ : ℚ}
    (hδ : 0 ≤ δ) (hd : 0 ≤ d) (hu : 0 < u) (hv : 0 ≤ v)
    (hc3 : 0 < d ^ 3 - 3 * δ) (hc4 : 0 < d ^ 6 - 6 * δ)
    (hchoice3 : 33 * δ ≤ v * u ^ 2 * (d ^ 3 - 3 * δ) ^ 3)
    (hchoice4 : 138 * δ ≤ v * u ^ 2 * (d ^ 6 - 6 * δ) ^ 3)
    (R : EqualRegularity G δ) (x : FracPacking G) :
    ∀ H ∈ denseActiveProfiles R x d θ,
      (1 - v) * profileVolume (G := G) (partOf R) H ≤
        ((cleanFiber G (partOf R) (rootwiseReference (G := G) (partOf R)) u H).card : ℚ) := by
  classical
  intro H hH
  obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.1 hH
  exact denseHeavyPattern_clean_retention hδ hd hu hv hc3 hc4 hchoice3 hchoice4 R x hσ

end PaperIV.RC01DenseRootwiseRetention

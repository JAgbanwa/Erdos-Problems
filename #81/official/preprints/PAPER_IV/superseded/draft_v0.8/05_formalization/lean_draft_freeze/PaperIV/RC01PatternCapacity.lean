import PaperIV.PatternMass
import PaperIV.WeightedPatternCoins

/-!
# RC01: fractional capacity for colours indexed by reduced patterns

This is the graph-side bridge missing from `WeightedPatternCoins`.  A reduced
pattern `σ` owns a disjoint fibre of literal fractional `K₃/K₄` items.  Its
colour mass is that fibre mass divided by the common part scale `t²`.

For every physical resource we only need to identify the two regularity parts
containing its endpoints.  If all items in every active fibre cross that pair,
the original fractional edge capacities imply that the sum of the active
pattern masses is at most the pair density.  Consequently the weighted owner
coin is a genuine probability distribution.
-/

namespace PaperIV.RC01PatternCapacity

open Finset
open PaperIV.FarRounding PaperIV.PatternMass PaperIV.WeightedPatternCoins

variable {V W Pat : Type*}
variable [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
variable [Fintype Pat] [DecidableEq Pat]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Fractional mass of one reduced-pattern fibre, normalized by the common
regularity scale `t²`. -/
noncomputable def slotMass (x : FracPacking G ℚ) (t : ℕ)
    (fiber : Pat → Finset (Finset V)) (σ : Pat) : ℚ :=
  (∑ K ∈ fiber σ, x.weight K) / (t : ℚ) ^ 2

theorem slotMass_nonneg (x : FracPacking G ℚ) (t : ℕ)
    (fiber : Pat → Finset (Finset V)) (σ : Pat) :
    0 ≤ slotMass x t fiber σ := by
  apply div_nonneg
  · exact Finset.sum_nonneg fun K _ => x.weight_nonneg K
  · positivity

/-- Unnormalized fractional mass of one literal pattern fibre. -/
noncomputable def rawMass (x : FracPacking G ℚ)
    (fiber : Pat → Finset (Finset V)) (σ : Pat) : ℚ :=
  ∑ K ∈ fiber σ, x.weight K

theorem rawMass_nonneg (x : FracPacking G ℚ)
    (fiber : Pat → Finset (Finset V)) (σ : Pat) :
    0 ≤ rawMass x fiber σ :=
  Finset.sum_nonneg fun K _ => x.weight_nonneg K

/-- Raw version of (15.5).  The resource budget is the physical pair volume
`density(A,B) * t^2`, rather than the normalized density. -/
theorem sum_rawMass_le_pairVolume
    (x : FracPacking G ℚ) (t : ℕ) (ht : 0 < t)
    (fiber : Pat → Finset (Finset V)) (Active : Finset Pat)
    (hdisj : Set.PairwiseDisjoint (Active : Set Pat) fiber)
    (A B : Finset V) (hAB : Disjoint A B)
    (hA : A.card = t) (hB : B.card = t)
    (hitems : ∀ K ∈ Active.biUnion fiber, K ∈ items G)
    (hmeet : ∀ K ∈ Active.biUnion fiber,
      ∃ e ∈ crossEdges G A B, e ∈ pairs K) :
    ∑ σ ∈ Active, rawMass x fiber σ
      ≤ G.edgeDensity A B * (t : ℚ) ^ 2 := by
  have hraw := mass_le_density x A B hAB (Active.biUnion fiber) hitems hmeet
  rw [hA, hB] at hraw
  change (∑ σ ∈ Active, ∑ K ∈ fiber σ, x.weight K)
    ≤ G.edgeDensity A B * (t : ℚ) ^ 2
  rw [← Finset.sum_biUnion hdisj]
  nlinarith

/-- Capacity for the unnormalized masses, with the physical pair volume as
denominator.  This is the form consumed by safe post-cleaning spreading. -/
theorem rawPatternCapacity_of_grouped_fibers
    (x : FracPacking G ℚ) (t : ℕ) (ht : 0 < t)
    (fiber : Pat → Finset (Finset V))
    (Act : W → Finset Pat) (left right : W → Finset V)
    (hdisj : ∀ e, Set.PairwiseDisjoint (Act e : Set Pat) fiber)
    (hparts : ∀ e, Disjoint (left e) (right e) ∧
      (left e).card = t ∧ (right e).card = t)
    (hdensity : ∀ e, 0 < G.edgeDensity (left e) (right e))
    (hitems : ∀ e, ∀ K ∈ (Act e).biUnion fiber, K ∈ items G)
    (hmeet : ∀ e, ∀ K ∈ (Act e).biUnion fiber,
      ∃ f ∈ crossEdges G (left e) (right e), f ∈ pairs K) :
    PatternCapacity Act (rawMass x fiber)
      (fun e => G.edgeDensity (left e) (right e) * (t : ℚ) ^ 2) := by
  apply patternCapacity_of_sum_mass_le
  · intro e
    exact mul_pos (hdensity e) (by positivity)
  · intro e
    exact sum_rawMass_le_pairVolume x t ht fiber (Act e) (hdisj e)
      (left e) (right e) (hparts e).1 (hparts e).2.1 (hparts e).2.2
      (hitems e) (hmeet e)

/-- The literal grouped form of RC01 (15.5).  No probability or asymptotic
argument occurs here: this is just the fractional capacity of the real edges
between `A` and `B`, after summing pairwise-disjoint pattern fibres. -/
theorem sum_slotMass_le_density
    (x : FracPacking G ℚ) (t : ℕ) (ht : 0 < t)
    (fiber : Pat → Finset (Finset V)) (Active : Finset Pat)
    (hdisj : Set.PairwiseDisjoint (Active : Set Pat) fiber)
    (A B : Finset V) (hAB : Disjoint A B)
    (hA : A.card = t) (hB : B.card = t)
    (hitems : ∀ K ∈ Active.biUnion fiber, K ∈ items G)
    (hmeet : ∀ K ∈ Active.biUnion fiber,
      ∃ e ∈ crossEdges G A B, e ∈ pairs K) :
    ∑ σ ∈ Active, slotMass x t fiber σ ≤ G.edgeDensity A B := by
  have hraw := mass_le_density x A B hAB (Active.biUnion fiber) hitems hmeet
  rw [hA, hB] at hraw
  have htq : (0 : ℚ) < (t : ℚ) ^ 2 := by positivity
  change (∑ σ ∈ Active, (∑ K ∈ fiber σ, x.weight K) / (t : ℚ) ^ 2)
    ≤ G.edgeDensity A B
  rw [← Finset.sum_div, ← Finset.sum_biUnion hdisj]
  calc
    (∑ K ∈ Active.biUnion fiber, x.weight K) / (t : ℚ) ^ 2
        ≤ (G.edgeDensity A B * (t : ℚ) * (t : ℚ)) / (t : ℚ) ^ 2 :=
      div_le_div_of_nonneg_right hraw (le_of_lt htq)
    _ = G.edgeDensity A B := by
      field_simp

/-- **Capacity adapter for the weighted RC01 schedule.**  Once each physical
resource has been assigned its ordered pair of regularity parts, (15.5)
discharges `PatternCapacity` simultaneously on every resource. -/
theorem patternCapacity_of_grouped_fibers
    (x : FracPacking G ℚ) (t : ℕ) (ht : 0 < t)
    (fiber : Pat → Finset (Finset V))
    (Act : W → Finset Pat) (left right : W → Finset V)
    (hdisj : ∀ e, Set.PairwiseDisjoint (Act e : Set Pat) fiber)
    (hparts : ∀ e, Disjoint (left e) (right e) ∧
      (left e).card = t ∧ (right e).card = t)
    (hdensity : ∀ e, 0 < G.edgeDensity (left e) (right e))
    (hitems : ∀ e, ∀ K ∈ (Act e).biUnion fiber, K ∈ items G)
    (hmeet : ∀ e, ∀ K ∈ (Act e).biUnion fiber,
      ∃ f ∈ crossEdges G (left e) (right e), f ∈ pairs K) :
    PatternCapacity Act (slotMass x t fiber)
      (fun e => G.edgeDensity (left e) (right e)) := by
  apply patternCapacity_of_sum_mass_le
  · exact hdensity
  · intro e
    exact sum_slotMass_le_density x t ht fiber (Act e)
      (hdisj e) (left e) (right e) (hparts e).1
      (hparts e).2.1 (hparts e).2.2 (hitems e) (hmeet e)

end PaperIV.RC01PatternCapacity

import PaperIV.WeightedMoments

/-!
# RC01: weighted coins indexed by reduced patterns

The failed `WeightedCoin` construction indexed a colour by one physical item;
then a colour class contained at most one candidate.  Here colours are reduced
patterns.  A resource `e` gives pattern `σ` probability `mass σ / density e`
when `σ` is active at `e`, and the remaining probability goes to `none`.

This is the exact finite probability space used by the weighted RC01 schedule.
The module is deliberately generic: the later graph-specific adapter only has
to define the active-pattern incidence and discharge its capacity inequality.
-/

namespace PaperIV.WeightedPatternCoins

open Finset
open PaperIV.OwnerCoins
open PaperIV.WeightedMoments

variable {W Pat : Type*} [Fintype W] [DecidableEq W] [Fintype Pat] [DecidableEq Pat]

/-- The weighted owner coin on one physical resource. -/
def patternCoin (Act : W → Finset Pat) (mass : Pat → ℚ) (density : W → ℚ)
    (e : W) : Option Pat → ℚ :=
  ownerDist (Act e) (fun σ => mass σ / density e)

/-- The local capacity inequality which makes `patternCoin` a probability
distribution.  It is the literal form of RC01 (15.5). -/
def PatternCapacity (Act : W → Finset Pat) (mass : Pat → ℚ) (density : W → ℚ) : Prop :=
  ∀ e, ∑ σ ∈ Act e, mass σ / density e ≤ 1

/-- It is enough to prove the un-divided incidence inequality.  This is the
form supplied by the fractional edge capacities after grouping items by their
reduced pattern. -/
theorem patternCapacity_of_sum_mass_le
    (Act : W → Finset Pat) (mass : Pat → ℚ) (density : W → ℚ)
    (hdensity : ∀ e, 0 < density e)
    (hload : ∀ e, ∑ σ ∈ Act e, mass σ ≤ density e) :
    PatternCapacity Act mass density := by
  intro e
  rw [← Finset.sum_div]
  exact (div_le_one (hdensity e)).2 (hload e)

theorem patternCoin_nonneg
    (Act : W → Finset Pat) (mass : Pat → ℚ) (density : W → ℚ)
    (hmass : ∀ σ, 0 ≤ mass σ) (hdensity : ∀ e, 0 < density e)
    (hcap : PatternCapacity Act mass density) :
    ∀ e c, 0 ≤ patternCoin Act mass density e c := by
  intro e
  apply ownerDist_nonneg
  · intro σ
    exact div_nonneg (hmass σ) (le_of_lt (hdensity e))
  · exact hcap e

theorem patternCoin_sum
    (Act : W → Finset Pat) (mass : Pat → ℚ) (density : W → ℚ) :
    ∀ e, ∑ c : Option Pat, patternCoin Act mass density e c = 1 := by
  intro e
  exact ownerDist_sum (Act e) (fun σ => mass σ / density e)

/-- Independent weighted pattern choices over all resources. -/
noncomputable def patternCoins
    (Act : W → Finset Pat) (mass : Pat → ℚ) (density : W → ℚ)
    (hmass : ∀ σ, 0 ≤ mass σ) (hdensity : ∀ e, 0 < density e)
    (hcap : PatternCapacity Act mass density) :
    PaperIV.EighthMoment.FinProb (W → Option Pat) :=
  coinSpace (patternCoin Act mass density)
    (patternCoin_nonneg Act mass density hmass hdensity hcap)
    (patternCoin_sum Act mass density)

@[simp] theorem patternCoin_some_of_mem
    (Act : W → Finset Pat) (mass : Pat → ℚ) (density : W → ℚ)
    {e : W} {σ : Pat} (hσ : σ ∈ Act e) :
    patternCoin Act mass density e (some σ) = mass σ / density e := by
  simp [patternCoin, ownerDist, hσ]

@[simp] theorem patternCoin_some_of_not_mem
    (Act : W → Finset Pat) (mass : Pat → ℚ) (density : W → ℚ)
    {e : W} {σ : Pat} (hσ : σ ∉ Act e) :
    patternCoin Act mass density e (some σ) = 0 := by
  simp [patternCoin, ownerDist, hσ]

/-- **Weighted cancellation for one physical candidate.**  If pattern `σ`
is active on every resource of `S`, the probability that all of `S` receives
colour `σ` is the expected product `mass^|S| / ∏ density`. -/
theorem prob_all_owned
    (Act : W → Finset Pat) (mass : Pat → ℚ) (density : W → ℚ)
    (hmass : ∀ σ, 0 ≤ mass σ) (hdensity : ∀ e, 0 < density e)
    (hcap : PatternCapacity Act mass density)
    (S : Finset W) (σ : Pat) (hactive : ∀ e ∈ S, σ ∈ Act e) :
    (patternCoins Act mass density hmass hdensity hcap).expect
        (fun ω => ∏ e ∈ S, (if ω e = some σ then (1 : ℚ) else 0))
      = (mass σ) ^ S.card / ∏ e ∈ S, density e := by
  apply PaperIV.OwnerCoins.prob_all_owned
    (patternCoin Act mass density)
    (patternCoin_nonneg Act mass density hmass hdensity hcap)
    (patternCoin_sum Act mass density)
  intro e he
  exact patternCoin_some_of_mem Act mass density (hactive e he)

/-- The generic block weight used by `WeightedMoments` has the same closed
form on a candidate of an active pattern. -/
theorem blockWeight_some
    (Act : W → Finset Pat) (mass : Pat → ℚ) (density : W → ℚ)
    (S : Finset W) (σ : Pat) (hactive : ∀ e ∈ S, σ ∈ Act e) :
    blockWeight (patternCoin Act mass density) (some σ) S
      = (mass σ) ^ S.card / ∏ e ∈ S, density e := by
  rw [blockWeight]
  rw [Finset.prod_congr rfl (fun e he =>
    patternCoin_some_of_mem Act mass density (hactive e he))]
  rw [Finset.prod_div_distrib, Finset.prod_const]

/-- Expected size of one pattern layer, before concentration. -/
theorem expect_layer_count
    {I : Type*} [DecidableEq I]
    (Act : W → Finset Pat) (mass : Pat → ℚ) (density : W → ℚ)
    (hmass : ∀ σ, 0 ≤ mass σ) (hdensity : ∀ e, 0 < density e)
    (hcap : PatternCapacity Act mass density)
    (support : I → Finset W) (T : Finset I) (σ : Pat)
    (hactive : ∀ i ∈ T, ∀ e ∈ support i, σ ∈ Act e) :
    (patternCoins Act mass density hmass hdensity hcap).expect
        (PaperIV.OwnerCoinMoments.blockCount support (some σ) T)
      = ∑ i ∈ T, (mass σ) ^ (support i).card /
          ∏ e ∈ support i, density e := by
  rw [patternCoins, expect_count_gen (patternCoin Act mass density)
    (patternCoin_nonneg Act mass density hmass hdensity hcap)
    (patternCoin_sum Act mass density) (some σ) support T]
  exact Finset.sum_congr rfl fun i hi =>
    blockWeight_some Act mass density (support i) σ (hactive i hi)

/-- **Variance interface for weighted pattern layers.**  Once the graph-side
counting lemma bounds every candidate probability by `B`, the old uniform
coin hypothesis is no longer needed. -/
theorem variance_layer_le
    {I : Type*} [DecidableEq I]
    (Act : W → Finset Pat) (mass : Pat → ℚ) (density : W → ℚ)
    (hmass : ∀ σ, 0 ≤ mass σ) (hdensity : ∀ e, 0 < density e)
    (hcap : PatternCapacity Act mass density)
    (support : I → Finset W) (T : Finset I) (σ : Pat) (B : ℚ)
    (hB : ∀ i ∈ T,
      (mass σ) ^ (support i).card / ∏ e ∈ support i, density e ≤ B)
    (hactive : ∀ i ∈ T, ∀ e ∈ support i, σ ∈ Act e) :
    (patternCoins Act mass density hmass hdensity hcap).expect
        (fun ω => (PaperIV.OwnerCoinMoments.blockCount support (some σ) T ω
          - ∑ i ∈ T, (mass σ) ^ (support i).card /
              ∏ e ∈ support i, density e) ^ 2)
      ≤ ((PaperIV.OwnerCoinMoments.meetingPairs support T).card : ℚ) * B := by
  have hweights :
      ∑ i ∈ T, blockWeight (patternCoin Act mass density) (some σ) (support i)
        = ∑ i ∈ T, (mass σ) ^ (support i).card /
            ∏ e ∈ support i, density e :=
    Finset.sum_congr rfl fun i hi =>
      blockWeight_some Act mass density (support i) σ (hactive i hi)
  rw [← hweights, patternCoins]
  apply variance_le_gen
    (patternCoin Act mass density)
    (patternCoin_nonneg Act mass density hmass hdensity hcap)
    (patternCoin_sum Act mass density)
  intro i hi
  rw [blockWeight_some Act mass density (support i) σ (hactive i hi)]
  exact hB i hi

end PaperIV.WeightedPatternCoins

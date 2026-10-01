import MixedRounding.Defs

/-!
# RC01: fractional packing assembled from canonical pattern fibres

This is the deterministic adapter between the regularity side of RC01 and the
slack mixed nibble.  A reduced pattern `σ` is assigned a nonnegative constant
weight `c σ`; every literal item in its canonical fibre receives that weight.
Fibres need not be disjoint for the construction: overlaps are added, so all
identities below remain valid without a hidden uniqueness assumption.

The graph-specific work is isolated in two finite inequalities:

* the sum of the one-edge fibre counts times `c σ` is at most one;
* the sum of the two-edge fibre counts times `c σ` is small.

Once those are supplied, `canonicalPacking` is a literal feasible mixed
fractional packing and its weighted codegrees are exactly the displayed
two-edge sums.  The value identity is also exact when every fibre has a fixed
gain (as happens for the tagged K3/K4 fibres of RC01).
-/

namespace PaperIV.RC01CanonicalFractional

open Finset
open MixedRounding

variable {V Pat : Type*} [Fintype V] [DecidableEq V]
variable [Fintype Pat] [DecidableEq Pat]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Add the constant weight of every active pattern whose fibre contains `K`. -/
noncomputable def canonicalWeight (Active : Finset Pat)
    (fiber : Pat → Finset (Finset V)) (c : Pat → ℚ) (K : Finset V) : ℚ :=
  ∑ σ ∈ Active, if K ∈ fiber σ then c σ else 0

theorem canonicalWeight_nonneg (Active : Finset Pat)
    (fiber : Pat → Finset (Finset V)) (c : Pat → ℚ)
    (hc : ∀ σ ∈ Active, 0 ≤ c σ) (K : Finset V) :
    0 ≤ canonicalWeight Active fiber c K := by
  unfold canonicalWeight
  exact Finset.sum_nonneg fun σ hσ => by
    by_cases hK : K ∈ fiber σ
    · simpa [hK] using hc σ hσ
    · simp [hK]

/-- Number of items of a fibre using one physical edge. -/
def oneCount (fiber : Pat → Finset (Finset V)) (σ : Pat) (e : Sym2 V) : ℕ :=
  ((fiber σ).filter fun K => e ∈ pairs K).card

/-- Number of items of a fibre using two prescribed physical edges. -/
def twoCount (fiber : Pat → Finset (Finset V))
    (σ : Pat) (e f : Sym2 V) : ℕ :=
  ((fiber σ).filter fun K => e ∈ pairs K ∧ f ∈ pairs K).card

/-- Removing copies from every fibre cannot increase a one-edge count. -/
theorem oneCount_mono {fiber fiber' : Pat → Finset (Finset V)}
    (hsub : ∀ σ, fiber σ ⊆ fiber' σ) (σ : Pat) (e : Sym2 V) :
    oneCount fiber σ e ≤ oneCount fiber' σ e := by
  apply Finset.card_le_card
  intro K hK
  rw [Finset.mem_filter] at hK ⊢
  exact ⟨hsub σ hK.1, hK.2⟩

/-- Removing copies from every fibre cannot increase a two-edge count. -/
theorem twoCount_mono {fiber fiber' : Pat → Finset (Finset V)}
    (hsub : ∀ σ, fiber σ ⊆ fiber' σ) (σ : Pat) (e f : Sym2 V) :
    twoCount fiber σ e f ≤ twoCount fiber' σ e f := by
  apply Finset.card_le_card
  intro K hK
  rw [Finset.mem_filter] at hK ⊢
  exact ⟨hsub σ hK.1, hK.2⟩

/-- Weighted codegree bounds proved for the raw fibres automatically descend
to any simultaneous cleanup, provided the coefficients are nonnegative. -/
theorem sum_twoCount_mul_le_of_subset
    (Active : Finset Pat) {fiber fiber' : Pat → Finset (Finset V)}
    (hsub : ∀ σ, fiber σ ⊆ fiber' σ) (c : Pat → ℚ)
    (hc : ∀ σ ∈ Active, 0 ≤ c σ) (e f : Sym2 V) :
    ∑ σ ∈ Active, (twoCount fiber σ e f : ℚ) * c σ
      ≤ ∑ σ ∈ Active, (twoCount fiber' σ e f : ℚ) * c σ := by
  apply Finset.sum_le_sum
  intro σ hσ
  exact mul_le_mul_of_nonneg_right
    (by exact_mod_cast twoCount_mono hsub σ e f) (hc σ hσ)

private theorem sum_indicator_of_subset {α : Type*} [DecidableEq α]
    (U F : Finset α) (p : α → Prop) [DecidablePred p] (a : ℚ)
    (hFU : F ⊆ U) :
    ∑ x ∈ U, (if x ∈ F ∧ p x then a else 0) = ((F.filter p).card : ℚ) * a := by
  have hfilter : U.filter (fun x => x ∈ F ∧ p x) = F.filter p := by
    ext x
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨_, hxF, hpx⟩
      exact ⟨hxF, hpx⟩
    · rintro ⟨hxF, hpx⟩
      exact ⟨hFU hxF, hxF, hpx⟩
  rw [← Finset.sum_filter]
  rw [hfilter]
  simp

theorem load_eq (Active : Finset Pat) (fiber : Pat → Finset (Finset V))
    (c : Pat → ℚ) (hitems : ∀ σ ∈ Active, fiber σ ⊆ items G) (e : Sym2 V) :
    ∑ K ∈ items G,
        (if e ∈ pairs K then canonicalWeight Active fiber c K else 0)
      = ∑ σ ∈ Active, (oneCount fiber σ e : ℚ) * c σ := by
  classical
  unfold canonicalWeight
  calc
    ∑ K ∈ items G, (if e ∈ pairs K then ∑ σ ∈ Active,
        (if K ∈ fiber σ then c σ else 0) else 0)
        = ∑ K ∈ items G, ∑ σ ∈ Active,
            (if K ∈ fiber σ ∧ e ∈ pairs K then c σ else 0) := by
              apply Finset.sum_congr rfl
              intro K _
              by_cases he : e ∈ pairs K <;> simp [he]
    _ = ∑ σ ∈ Active, ∑ K ∈ items G,
          (if K ∈ fiber σ ∧ e ∈ pairs K then c σ else 0) := by
            rw [Finset.sum_comm]
    _ = ∑ σ ∈ Active, (oneCount fiber σ e : ℚ) * c σ := by
          apply Finset.sum_congr rfl
          intro σ hσ
          simpa [oneCount] using
            (sum_indicator_of_subset (items G) (fiber σ)
              (fun K => e ∈ pairs K) (c σ) (hitems σ hσ))

theorem codegree_eq (Active : Finset Pat) (fiber : Pat → Finset (Finset V))
    (c : Pat → ℚ) (hitems : ∀ σ ∈ Active, fiber σ ⊆ items G)
    (e f : Sym2 V) :
    ∑ K ∈ items G,
        (if e ∈ pairs K ∧ f ∈ pairs K then canonicalWeight Active fiber c K else 0)
      = ∑ σ ∈ Active, (twoCount fiber σ e f : ℚ) * c σ := by
  classical
  unfold canonicalWeight
  calc
    ∑ K ∈ items G, (if e ∈ pairs K ∧ f ∈ pairs K then ∑ σ ∈ Active,
        (if K ∈ fiber σ then c σ else 0) else 0)
        = ∑ K ∈ items G, ∑ σ ∈ Active,
            (if K ∈ fiber σ ∧ (e ∈ pairs K ∧ f ∈ pairs K) then c σ else 0) := by
              apply Finset.sum_congr rfl
              intro K _
              by_cases hef : e ∈ pairs K ∧ f ∈ pairs K <;> simp [hef]
    _ = ∑ σ ∈ Active, ∑ K ∈ items G,
          (if K ∈ fiber σ ∧ (e ∈ pairs K ∧ f ∈ pairs K) then c σ else 0) := by
            rw [Finset.sum_comm]
    _ = ∑ σ ∈ Active, (twoCount fiber σ e f : ℚ) * c σ := by
          apply Finset.sum_congr rfl
          intro σ hσ
          simpa [twoCount] using
            (sum_indicator_of_subset (items G) (fiber σ)
              (fun K => e ∈ pairs K ∧ f ∈ pairs K) (c σ) (hitems σ hσ))

/-- The literal mixed fractional packing obtained from canonical fibres. -/
noncomputable def canonicalPacking (Active : Finset Pat)
    (fiber : Pat → Finset (Finset V)) (c : Pat → ℚ)
    (hc : ∀ σ ∈ Active, 0 ≤ c σ)
    (hitems : ∀ σ ∈ Active, fiber σ ⊆ items G)
    (hload : ∀ e ∈ G.edgeFinset,
      ∑ σ ∈ Active, (oneCount fiber σ e : ℚ) * c σ ≤ 1) : FracPacking G where
  weight := canonicalWeight Active fiber c
  weight_nonneg := canonicalWeight_nonneg Active fiber c hc
  capacity := by
    intro e he
    rw [load_eq Active fiber c hitems e]
    exact hload e he

theorem canonicalPacking_codegree
    (Active : Finset Pat) (fiber : Pat → Finset (Finset V)) (c : Pat → ℚ)
    (hc : ∀ σ ∈ Active, 0 ≤ c σ)
    (hitems : ∀ σ ∈ Active, fiber σ ⊆ items G)
    (hload : ∀ e ∈ G.edgeFinset,
      ∑ σ ∈ Active, (oneCount fiber σ e : ℚ) * c σ ≤ 1)
    (e f : Sym2 V) :
    ∑ K ∈ items G, (if e ∈ pairs K ∧ f ∈ pairs K then
        (canonicalPacking Active fiber c hc hitems hload).weight K else 0)
      = ∑ σ ∈ Active, (twoCount fiber σ e f : ℚ) * c σ := by
  exact codegree_eq Active fiber c hitems e f

private theorem sum_weighted_indicator_of_subset {α : Type*} [DecidableEq α]
    (U F : Finset α) (w : α → ℚ) (a b : ℚ) (hFU : F ⊆ U)
    (hw : ∀ x ∈ F, w x = b) :
    ∑ x ∈ U, w x * (if x ∈ F then a else 0) = (F.card : ℚ) * (b * a) := by
  have hfilter : U.filter (fun x => x ∈ F) = F := by
    ext x
    simp only [Finset.mem_filter]
    constructor
    · exact fun hx => hx.2
    · exact fun hx => ⟨hFU hx, hx⟩
  calc
    ∑ x ∈ U, w x * (if x ∈ F then a else 0)
        = ∑ x ∈ U, (if x ∈ F then w x * a else 0) := by
            apply Finset.sum_congr rfl
            intro x _
            by_cases hx : x ∈ F <;> simp [hx]
    _ = ∑ x ∈ U.filter (fun x => x ∈ F), w x * a := by
          rw [Finset.sum_filter]
    _ = ∑ x ∈ F, w x * a := by rw [hfilter]
    _ = ∑ _x ∈ F, b * a := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [hw x hx]
    _ = (F.card : ℚ) * (b * a) := by simp

/-- Exact value of the canonical packing when each pattern fibre has one gain. -/
theorem canonicalPacking_value_eq
    (Active : Finset Pat) (fiber : Pat → Finset (Finset V)) (c reward : Pat → ℚ)
    (hc : ∀ σ ∈ Active, 0 ≤ c σ)
    (hitems : ∀ σ ∈ Active, fiber σ ⊆ items G)
    (hload : ∀ e ∈ G.edgeFinset,
      ∑ σ ∈ Active, (oneCount fiber σ e : ℚ) * c σ ≤ 1)
    (hreward : ∀ σ ∈ Active, ∀ K ∈ fiber σ, gainF ℚ K = reward σ) :
    (canonicalPacking Active fiber c hc hitems hload).value
      = ∑ σ ∈ Active, ((fiber σ).card : ℚ) * (reward σ * c σ) := by
  classical
  rw [FracPacking.value]
  unfold canonicalPacking canonicalWeight
  calc
    ∑ K ∈ items G, gainF ℚ K * (∑ σ ∈ Active,
        (if K ∈ fiber σ then c σ else 0))
        = ∑ K ∈ items G, ∑ σ ∈ Active,
            gainF ℚ K * (if K ∈ fiber σ then c σ else 0) := by
              apply Finset.sum_congr rfl
              intro K _
              rw [Finset.mul_sum]
    _ = ∑ σ ∈ Active, ∑ K ∈ items G,
          gainF ℚ K * (if K ∈ fiber σ then c σ else 0) := by
            rw [Finset.sum_comm]
    _ = ∑ σ ∈ Active, ((fiber σ).card : ℚ) * (reward σ * c σ) := by
          apply Finset.sum_congr rfl
          intro σ hσ
          exact sum_weighted_indicator_of_subset (items G) (fiber σ)
            (gainF ℚ) (c σ) (reward σ) (hitems σ hσ) (hreward σ hσ)

end PaperIV.RC01CanonicalFractional

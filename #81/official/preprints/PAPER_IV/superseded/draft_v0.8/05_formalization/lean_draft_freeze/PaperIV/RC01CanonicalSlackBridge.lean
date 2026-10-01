import PaperIV.RC01CanonicalNormalization
import PaperIV.JointTwoQuotaPhysical

/-!
# RC01: canonical packing to the slack marked-quota codegree

The slack nibble is phrased on the joint support hypergraph, whereas the
canonical construction computes codegrees by literal K3/K4 fibres.  This file
proves that these are exactly the same finite sum.  Consequently the remaining
codegree obligation is purely the `twoCount` estimate for the cleaned fibres.
-/

namespace PaperIV.RC01CanonicalSlackBridge

open Finset
open MixedRounding
open PaperIV.RC01CanonicalFractional
open PaperIV.RC01CanonicalNormalization
open PaperIV.JointTypedNibbleGate
open PaperIV.JointTwoQuotaPhysical
open PaperIV.WeightedPatternCoins

variable {V Pat : Type*} [Fintype V] [DecidableEq V]
variable [Fintype Pat] [DecidableEq Pat]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Joint-support codegree equals the corresponding weighted sum over literal
items. -/
theorem joint_codegree_eq_items (x : FracPacking G) (e f : Sym2 V) :
    ∑ S ∈ (jointSupports G).filter (fun S => e ∈ S ∧ f ∈ S), inducedWeight x S
      = ((∑ K ∈ items G,
          (if e ∈ pairs K ∧ f ∈ pairs K then x.weight K else 0) : ℚ) : ℝ) := by
  classical
  rw [jointSupports_eq_supports]
  have hset : (supports G).filter (fun S => e ∈ S ∧ f ∈ S)
      = ((items G).filter (fun K => e ∈ pairs K ∧ f ∈ pairs K)).image pairs := by
    ext S
    simp only [supports, Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨K, hK, rfl⟩, heS, hfS⟩
      exact ⟨K, ⟨hK, heS, hfS⟩, rfl⟩
    · rintro ⟨K, ⟨hK, heK, hfK⟩, rfl⟩
      exact ⟨⟨K, hK, rfl⟩, heK, hfK⟩
  rw [hset]
  rw [Finset.sum_image]
  · rw [Finset.sum_filter]
    push_cast
    apply Finset.sum_congr rfl
    intro K hK
    by_cases h : e ∈ pairs K ∧ f ∈ pairs K
    · simp [h, inducedWeight_pairs x (mem_items.1 hK)]
    · simp [h]
  · intro K hK L hL hEq
    simp only [Finset.mem_coe, Finset.mem_filter] at hK hL
    exact pairs_injOn_items (mem_items.1 hK.1) (mem_items.1 hL.1) hEq

/-- Exact codegree of the arbitrary-budget canonical packing in the real-valued
form consumed by the slack marked-quota gate. -/
theorem budgetPacking_joint_codegree_eq
    (Active : Finset Pat) (fiber : Pat → Finset (Finset V))
    (mass budget : Pat → ℚ) (Act : Sym2 V → Finset Pat)
    (density : Sym2 V → ℚ)
    (hmass : ∀ σ, 0 ≤ mass σ) (hdensity : ∀ e, 0 < density e)
    (hcap : PatternCapacity Act mass density)
    (hAct : ∀ e, Act e ⊆ Active)
    (hbudget : ∀ σ ∈ Active, 0 < budget σ)
    (hitems : ∀ σ ∈ Active, fiber σ ⊆ items G)
    (hactive : ∀ e σ, σ ∈ Active → 0 < oneCount fiber σ e → σ ∈ Act e)
    (hspread : ∀ e σ, σ ∈ Act e →
      (oneCount fiber σ e : ℚ) * density e ≤ budget σ)
    (e f : Sym2 V) :
    ∑ S ∈ (jointSupports G).filter (fun S => e ∈ S ∧ f ∈ S),
        inducedWeight (budgetPacking Active fiber mass budget Act density
          hmass hdensity hcap hAct hbudget hitems hactive hspread) S
      = ((∑ σ ∈ Active, (twoCount fiber σ e f : ℚ) *
          budgetCoefficient mass budget σ : ℚ) : ℝ) := by
  let x := budgetPacking Active fiber mass budget Act density
    hmass hdensity hcap hAct hbudget hitems hactive hspread
  rw [joint_codegree_eq_items x e f]
  congr 1
  exact codegree_eq Active fiber (budgetCoefficient mass budget) hitems e f

/-- Inequality form used verbatim by `exists_packing_loss_le_of_slackMarkedQuota`.
Thus a rational bound on the explicit `twoCount` sum discharges the real
joint-support codegree premise without further graph reasoning. -/
theorem budgetPacking_joint_codegree_le
    (Active : Finset Pat) (fiber : Pat → Finset (Finset V))
    (mass budget : Pat → ℚ) (Act : Sym2 V → Finset Pat)
    (density : Sym2 V → ℚ)
    (hmass : ∀ σ, 0 ≤ mass σ) (hdensity : ∀ e, 0 < density e)
    (hcap : PatternCapacity Act mass density)
    (hAct : ∀ e, Act e ⊆ Active)
    (hbudget : ∀ σ ∈ Active, 0 < budget σ)
    (hitems : ∀ σ ∈ Active, fiber σ ⊆ items G)
    (hactive : ∀ e σ, σ ∈ Active → 0 < oneCount fiber σ e → σ ∈ Act e)
    (hspread : ∀ e σ, σ ∈ Act e →
      (oneCount fiber σ e : ℚ) * density e ≤ budget σ)
    (γ : ℚ)
    (hcodeg : ∀ e f : Sym2 V, e ≠ f →
      ∑ σ ∈ Active, (twoCount fiber σ e f : ℚ) *
        budgetCoefficient mass budget σ ≤ γ) :
    ∀ e f : Sym2 V, e ≠ f →
      ∑ S ∈ (jointSupports G).filter (fun S => e ∈ S ∧ f ∈ S),
          inducedWeight (budgetPacking Active fiber mass budget Act density
            hmass hdensity hcap hAct hbudget hitems hactive hspread) S
        ≤ (γ : ℝ) := by
  intro e f hef
  rw [budgetPacking_joint_codegree_eq Active fiber mass budget Act density
    hmass hdensity hcap hAct hbudget hitems hactive hspread e f]
  exact_mod_cast hcodeg e f hef

/-- Common-denominator arithmetic for the final mixed K3/K4 codegree.  Certo
0.7 independently certified this statement and found that positivity of the
three denominator factors is the only sign information required. -/
theorem mixed_codegree_of_scaled_threshold
    {den mixed γ codeg : ℚ}
    (hden : 0 < den)
    (hscaled : codeg * den ≤ mixed)
    (hthreshold : mixed ≤ γ * den) :
    codeg ≤ γ := by
  exact le_of_mul_le_mul_right (hscaled.trans hthreshold) hden

/-- Common-denominator arithmetic for the final mixed K3/K4 codegree.  Certo
0.8 audited the denominator-free core above: all three hypotheses are needed.
The present form is the convenient adapter from the two literal fibre bounds. -/
theorem mixed_codegree_of_common_threshold
    {k3 k4 a2 a5 t γ codeg : ℚ}
    (ht : 0 < t) (ha2 : 0 < a2) (ha5 : 0 < a5)
    (hsplit : codeg ≤ k3 / (a2 * t) + k4 / (a5 * t))
    (hthreshold : k3 * a5 + k4 * a2 ≤ γ * a2 * a5 * t) :
    codeg ≤ γ := by
  have hden : 0 < a2 * a5 * t := by positivity
  have hmul := mul_le_mul_of_nonneg_right hsplit hden.le
  have hsimp : (k3 / (a2 * t) + k4 / (a5 * t)) * (a2 * a5 * t)
      = k3 * a5 + k4 * a2 := by
    field_simp [ne_of_gt ht, ne_of_gt ha2, ne_of_gt ha5]
    <;> ring
  rw [hsimp] at hmul
  by_contra hnot
  have hlt : γ < codeg := lt_of_not_ge hnot
  have hpos : 0 < (codeg - γ) * (a2 * a5 * t) :=
    mul_pos (sub_pos.mpr hlt) hden
  nlinarith

end PaperIV.RC01CanonicalSlackBridge

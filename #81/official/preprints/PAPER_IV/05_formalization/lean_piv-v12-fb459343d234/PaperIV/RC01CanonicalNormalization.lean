import PaperIV.RC01CanonicalFractional
import PaperIV.WeightedPatternCoins

/-!
# RC01: normalized canonical fibres

This module connects the literal capacity inequality on reduced patterns with
the canonical fractional packing.  Pattern `σ` carries mass `mass σ`, spread
uniformly over its literal fibre.  The only graph-side hypothesis is the local
spread inequality

```
oneCount(σ,e) * density(e) <= card(fibre σ).
```

It may be verified after deleting the exceptional heavy resources.  No global
rounding statement is assumed here.
-/

namespace PaperIV.RC01CanonicalNormalization

open Finset
open MixedRounding
open PaperIV.RC01CanonicalFractional
open PaperIV.WeightedPatternCoins

variable {V Pat : Type*} [Fintype V] [DecidableEq V]
variable [Fintype Pat] [DecidableEq Pat]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Uniform weight assigned to every literal copy of a reduced pattern. -/
noncomputable def normalizedCoefficient (mass : Pat → ℚ)
    (fiber : Pat → Finset (Finset V)) (σ : Pat) : ℚ :=
  mass σ / ((fiber σ).card : ℚ)

theorem normalizedCoefficient_nonneg (mass : Pat → ℚ)
    (fiber : Pat → Finset (Finset V))
    (hmass : ∀ σ, 0 ≤ mass σ) (σ : Pat) :
    0 ≤ normalizedCoefficient mass fiber σ := by
  exact div_nonneg (hmass σ) (by positivity)

/-- The local spread inequality is precisely what makes one normalized fibre
fit below its share `mass σ / density e` of a resource. -/
theorem normalized_one_term_le
    (mass density : ℚ) (count card : ℕ)
    (hmass : 0 ≤ mass) (hdensity : 0 < density) (hcard : 0 < card)
    (hspread : (count : ℚ) * density ≤ (card : ℚ)) :
    (count : ℚ) * (mass / (card : ℚ)) ≤ mass / density := by
  have hcardQ : (0 : ℚ) < (card : ℚ) := by exact_mod_cast hcard
  have hmul := mul_le_mul_of_nonneg_left hspread hmass
  calc
    (count : ℚ) * (mass / (card : ℚ))
        = ((count : ℚ) * mass) / (card : ℚ) := by ring
    _ ≤ mass / density := by
      rw [div_le_div_iff₀ hcardQ hdensity]
      nlinarith

private theorem sum_indicator_eq_of_subset
    (Active A : Finset Pat) (f : Pat → ℚ) (hA : A ⊆ Active) :
    ∑ σ ∈ Active, (if σ ∈ A then f σ else 0) = ∑ σ ∈ A, f σ := by
  classical
  rw [← Finset.sum_filter]
  congr 1
  ext σ
  simp only [Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨hA h, h⟩

/-- Pattern capacity plus the local spread inequalities discharge every
one-edge capacity inequality required by `canonicalPacking`. -/
theorem normalized_load_le_one
    (Active : Finset Pat) (fiber : Pat → Finset (Finset V))
    (mass : Pat → ℚ) (Act : Sym2 V → Finset Pat) (density : Sym2 V → ℚ)
    (hmass : ∀ σ, 0 ≤ mass σ) (hdensity : ∀ e, 0 < density e)
    (hcap : PatternCapacity Act mass density)
    (hAct : ∀ e, Act e ⊆ Active)
    (hne : ∀ σ ∈ Active, (fiber σ).Nonempty)
    (hactive : ∀ e σ, σ ∈ Active → 0 < oneCount fiber σ e → σ ∈ Act e)
    (hspread : ∀ e σ, σ ∈ Act e →
      (oneCount fiber σ e : ℚ) * density e ≤ ((fiber σ).card : ℚ))
    (e : Sym2 V) :
    ∑ σ ∈ Active, (oneCount fiber σ e : ℚ) *
        normalizedCoefficient mass fiber σ ≤ 1 := by
  classical
  calc
    ∑ σ ∈ Active, (oneCount fiber σ e : ℚ) *
          normalizedCoefficient mass fiber σ
        ≤ ∑ σ ∈ Active, (if σ ∈ Act e then mass σ / density e else 0) := by
          apply Finset.sum_le_sum
          intro σ hσ
          by_cases ha : σ ∈ Act e
          · rw [if_pos ha]
            exact normalized_one_term_le (mass σ) (density e)
              (oneCount fiber σ e) (fiber σ).card (hmass σ) (hdensity e)
              (Finset.card_pos.2 (hne σ hσ)) (hspread e σ ha)
          · rw [if_neg ha]
            have hz : oneCount fiber σ e = 0 := by
              by_contra hnz
              have hp : 0 < oneCount fiber σ e := Nat.pos_of_ne_zero hnz
              exact ha (hactive e σ hσ hp)
            simp [hz]
    _ = ∑ σ ∈ Act e, mass σ / density e :=
      sum_indicator_eq_of_subset Active (Act e) (fun σ => mass σ / density e) (hAct e)
    _ ≤ 1 := hcap e

/-- The normalized canonical packing.  Its feasibility is now a consequence,
not a parameter of the definition. -/
noncomputable def normalizedPacking
    (Active : Finset Pat) (fiber : Pat → Finset (Finset V))
    (mass : Pat → ℚ) (Act : Sym2 V → Finset Pat) (density : Sym2 V → ℚ)
    (hmass : ∀ σ, 0 ≤ mass σ) (hdensity : ∀ e, 0 < density e)
    (hcap : PatternCapacity Act mass density)
    (hAct : ∀ e, Act e ⊆ Active)
    (hne : ∀ σ ∈ Active, (fiber σ).Nonempty)
    (hitems : ∀ σ ∈ Active, fiber σ ⊆ items G)
    (hactive : ∀ e σ, σ ∈ Active → 0 < oneCount fiber σ e → σ ∈ Act e)
    (hspread : ∀ e σ, σ ∈ Act e →
      (oneCount fiber σ e : ℚ) * density e ≤ ((fiber σ).card : ℚ)) :
    FracPacking G :=
  canonicalPacking Active fiber (normalizedCoefficient mass fiber)
    (fun σ _ => normalizedCoefficient_nonneg mass fiber hmass σ) hitems
    (fun e _ => normalized_load_le_one Active fiber mass Act density hmass
      hdensity hcap hAct hne hactive hspread e)

/-- Exact value after normalized spreading: every nonempty fibre contributes
its whole assigned mass times its item reward. -/
theorem normalizedPacking_value_eq
    (Active : Finset Pat) (fiber : Pat → Finset (Finset V))
    (mass reward : Pat → ℚ) (Act : Sym2 V → Finset Pat)
    (density : Sym2 V → ℚ)
    (hmass : ∀ σ, 0 ≤ mass σ) (hdensity : ∀ e, 0 < density e)
    (hcap : PatternCapacity Act mass density)
    (hAct : ∀ e, Act e ⊆ Active)
    (hne : ∀ σ ∈ Active, (fiber σ).Nonempty)
    (hitems : ∀ σ ∈ Active, fiber σ ⊆ items G)
    (hactive : ∀ e σ, σ ∈ Active → 0 < oneCount fiber σ e → σ ∈ Act e)
    (hspread : ∀ e σ, σ ∈ Act e →
      (oneCount fiber σ e : ℚ) * density e ≤ ((fiber σ).card : ℚ))
    (hreward : ∀ σ ∈ Active, ∀ K ∈ fiber σ, gainF ℚ K = reward σ) :
    (normalizedPacking Active fiber mass Act density hmass hdensity hcap hAct
      hne hitems hactive hspread).value
      = ∑ σ ∈ Active, reward σ * mass σ := by
  rw [normalizedPacking]
  rw [canonicalPacking_value_eq Active fiber
    (normalizedCoefficient mass fiber) reward
    (fun σ _ => normalizedCoefficient_nonneg mass fiber hmass σ) hitems
    (fun e _ => normalized_load_le_one Active fiber mass Act density hmass
      hdensity hcap hAct hne hactive hspread e) hreward]
  apply Finset.sum_congr rfl
  intro σ hσ
  have hcardQ : (0 : ℚ) < ((fiber σ).card : ℚ) := by
    exact_mod_cast Finset.card_pos.2 (hne σ hσ)
  rw [normalizedCoefficient]
  field_simp [ne_of_gt hcardQ]

/-! ## Cleaning without dangerous renormalization -/

/-- Weight after cleaning, still divided by the cardinality of the original
reference fibre.  This is the safe normalization: deleting candidates can
only decrease loads. -/
noncomputable def referenceCoefficient (mass : Pat → ℚ) (volume : Pat → ℕ)
    (σ : Pat) : ℚ := mass σ / (volume σ : ℚ)

theorem referenceCoefficient_nonneg (mass : Pat → ℚ) (volume : Pat → ℕ)
    (hmass : ∀ σ, 0 ≤ mass σ) (σ : Pat) :
    0 ≤ referenceCoefficient mass volume σ := by
  exact div_nonneg (hmass σ) (by positivity)

theorem reference_load_le_one
    (Active : Finset Pat) (fiber : Pat → Finset (Finset V))
    (mass : Pat → ℚ) (volume : Pat → ℕ)
    (Act : Sym2 V → Finset Pat) (density : Sym2 V → ℚ)
    (hmass : ∀ σ, 0 ≤ mass σ) (hdensity : ∀ e, 0 < density e)
    (hcap : PatternCapacity Act mass density)
    (hAct : ∀ e, Act e ⊆ Active)
    (hvolume : ∀ σ ∈ Active, 0 < volume σ)
    (hactive : ∀ e σ, σ ∈ Active → 0 < oneCount fiber σ e → σ ∈ Act e)
    (hspread : ∀ e σ, σ ∈ Act e →
      (oneCount fiber σ e : ℚ) * density e ≤ (volume σ : ℚ))
    (e : Sym2 V) :
    ∑ σ ∈ Active, (oneCount fiber σ e : ℚ) *
        referenceCoefficient mass volume σ ≤ 1 := by
  classical
  calc
    ∑ σ ∈ Active, (oneCount fiber σ e : ℚ) *
          referenceCoefficient mass volume σ
        ≤ ∑ σ ∈ Active, (if σ ∈ Act e then mass σ / density e else 0) := by
          apply Finset.sum_le_sum
          intro σ hσ
          by_cases ha : σ ∈ Act e
          · rw [if_pos ha]
            exact normalized_one_term_le (mass σ) (density e)
              (oneCount fiber σ e) (volume σ) (hmass σ) (hdensity e)
              (hvolume σ hσ) (hspread e σ ha)
          · rw [if_neg ha]
            have hz : oneCount fiber σ e = 0 := by
              by_contra hnz
              exact ha (hactive e σ hσ (Nat.pos_of_ne_zero hnz))
            simp [hz]
    _ = ∑ σ ∈ Act e, mass σ / density e :=
      sum_indicator_eq_of_subset Active (Act e) (fun σ => mass σ / density e) (hAct e)
    _ ≤ 1 := hcap e

/-- Literal feasible packing formed from cleaned fibres, without rescaling the
survivors back up. -/
noncomputable def referencePacking
    (Active : Finset Pat) (fiber : Pat → Finset (Finset V))
    (mass : Pat → ℚ) (volume : Pat → ℕ)
    (Act : Sym2 V → Finset Pat) (density : Sym2 V → ℚ)
    (hmass : ∀ σ, 0 ≤ mass σ) (hdensity : ∀ e, 0 < density e)
    (hcap : PatternCapacity Act mass density)
    (hAct : ∀ e, Act e ⊆ Active)
    (hvolume : ∀ σ ∈ Active, 0 < volume σ)
    (hitems : ∀ σ ∈ Active, fiber σ ⊆ items G)
    (hactive : ∀ e σ, σ ∈ Active → 0 < oneCount fiber σ e → σ ∈ Act e)
    (hspread : ∀ e σ, σ ∈ Act e →
      (oneCount fiber σ e : ℚ) * density e ≤ (volume σ : ℚ)) :
    FracPacking G :=
  canonicalPacking Active fiber (referenceCoefficient mass volume)
    (fun σ _ => referenceCoefficient_nonneg mass volume hmass σ) hitems
    (fun e _ => reference_load_le_one Active fiber mass volume Act density
      hmass hdensity hcap hAct hvolume hactive hspread e)

/-- Exact retained value after cleaning. -/
theorem referencePacking_value_eq
    (Active : Finset Pat) (fiber : Pat → Finset (Finset V))
    (mass reward : Pat → ℚ) (volume : Pat → ℕ)
    (Act : Sym2 V → Finset Pat) (density : Sym2 V → ℚ)
    (hmass : ∀ σ, 0 ≤ mass σ) (hdensity : ∀ e, 0 < density e)
    (hcap : PatternCapacity Act mass density)
    (hAct : ∀ e, Act e ⊆ Active)
    (hvolume : ∀ σ ∈ Active, 0 < volume σ)
    (hitems : ∀ σ ∈ Active, fiber σ ⊆ items G)
    (hactive : ∀ e σ, σ ∈ Active → 0 < oneCount fiber σ e → σ ∈ Act e)
    (hspread : ∀ e σ, σ ∈ Act e →
      (oneCount fiber σ e : ℚ) * density e ≤ (volume σ : ℚ))
    (hreward : ∀ σ ∈ Active, ∀ K ∈ fiber σ, gainF ℚ K = reward σ) :
    (referencePacking Active fiber mass volume Act density hmass hdensity hcap
      hAct hvolume hitems hactive hspread).value
      = ∑ σ ∈ Active, ((fiber σ).card : ℚ) *
          (reward σ * referenceCoefficient mass volume σ) := by
  exact canonicalPacking_value_eq Active fiber (referenceCoefficient mass volume)
    reward (fun σ _ => referenceCoefficient_nonneg mass volume hmass σ) hitems
    (fun e _ => reference_load_le_one Active fiber mass volume Act density
      hmass hdensity hcap hAct hvolume hactive hspread e) hreward

/-- If every cleaned fibre retains a `(1-u)` fraction of its reference
volume, the cleaned packing retains the same fraction of the assigned value. -/
theorem referencePacking_value_ge
    (Active : Finset Pat) (fiber : Pat → Finset (Finset V))
    (mass reward : Pat → ℚ) (volume : Pat → ℕ)
    (Act : Sym2 V → Finset Pat) (density : Sym2 V → ℚ)
    (hmass : ∀ σ, 0 ≤ mass σ) (hreward0 : ∀ σ ∈ Active, 0 ≤ reward σ)
    (hdensity : ∀ e, 0 < density e)
    (hcap : PatternCapacity Act mass density)
    (hAct : ∀ e, Act e ⊆ Active)
    (hvolume : ∀ σ ∈ Active, 0 < volume σ)
    (hitems : ∀ σ ∈ Active, fiber σ ⊆ items G)
    (hactive : ∀ e σ, σ ∈ Active → 0 < oneCount fiber σ e → σ ∈ Act e)
    (hspread : ∀ e σ, σ ∈ Act e →
      (oneCount fiber σ e : ℚ) * density e ≤ (volume σ : ℚ))
    (hreward : ∀ σ ∈ Active, ∀ K ∈ fiber σ, gainF ℚ K = reward σ)
    (u : ℚ) (hretain : ∀ σ ∈ Active,
      (1 - u) * (volume σ : ℚ) ≤ ((fiber σ).card : ℚ)) :
    (1 - u) * (∑ σ ∈ Active, reward σ * mass σ)
      ≤ (referencePacking Active fiber mass volume Act density hmass hdensity
        hcap hAct hvolume hitems hactive hspread).value := by
  rw [referencePacking_value_eq Active fiber mass reward volume Act density
    hmass hdensity hcap hAct hvolume hitems hactive hspread hreward]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro σ hσ
  have hvQ : (0 : ℚ) < (volume σ : ℚ) := by
    exact_mod_cast hvolume σ hσ
  have hfactor : 0 ≤ reward σ * mass σ / (volume σ : ℚ) := by
    exact div_nonneg (mul_nonneg (hreward0 σ hσ) (hmass σ)) hvQ.le
  have hmul := mul_le_mul_of_nonneg_right (hretain σ hσ) hfactor
  rw [referenceCoefficient]
  field_simp [ne_of_gt hvQ] at hmul ⊢
  nlinarith

/-! ## Rational budgets (the `(1+u)` cleaning slack) -/

/-- Coefficient with an arbitrary positive reference budget.  In RC01 the
budget is `(1+u)` times the original fibre cardinality. -/
noncomputable def budgetCoefficient (mass budget : Pat → ℚ) (σ : Pat) : ℚ :=
  mass σ / budget σ

theorem budgetCoefficient_nonneg (mass budget : Pat → ℚ)
    (hmass : ∀ σ, 0 ≤ mass σ) (hbudget : ∀ σ, 0 ≤ budget σ) (σ : Pat) :
    0 ≤ budgetCoefficient mass budget σ :=
  div_nonneg (hmass σ) (hbudget σ)

theorem budget_one_term_le {mass density budget : ℚ} {count : ℕ}
    (hmass : 0 ≤ mass) (hdensity : 0 < density) (hbudget : 0 < budget)
    (hspread : (count : ℚ) * density ≤ budget) :
    (count : ℚ) * (mass / budget) ≤ mass / density := by
  have hmul := mul_le_mul_of_nonneg_left hspread hmass
  calc
    (count : ℚ) * (mass / budget) = ((count : ℚ) * mass) / budget := by ring
    _ ≤ mass / density := by
      rw [div_le_div_iff₀ hbudget hdensity]
      nlinarith

/-- Additive form of the two cleaning losses.  Certo independently verified
that only nonnegativity of `u` and `v` is needed. -/
theorem cleaning_retention {u v : ℚ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    1 - u - v ≤ (1 - v) / (1 + u) := by
  have hden : (0 : ℚ) < 1 + u := by linarith
  rw [le_div_iff₀ hden]
  nlinarith [sq_nonneg u, mul_nonneg hu hv]

/-- Per-pattern value retained after a `v`-fraction cleaning loss and an
`(1+u)` load normalization.  This is the multiplicative estimate used before
summing the K3 and K4 pattern layers. -/
theorem budget_term_value_ge {clean reference mass reward u v : ℚ}
    (href : 0 < reference) (hmass : 0 ≤ mass) (hreward : 0 ≤ reward)
    (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hclean : (1 - v) * reference ≤ clean) :
    (1 - u - v) * (reward * mass)
      ≤ clean * (reward * (mass / ((1 + u) * reference))) := by
  have hden : 0 < (1 + u) * reference := mul_pos (by linarith) href
  have hscale : 0 ≤ reward * mass / ((1 + u) * reference) :=
    div_nonneg (mul_nonneg hreward hmass) hden.le
  have hmul := mul_le_mul_of_nonneg_right hclean hscale
  have hret := cleaning_retention hu hv
  have hbase : 0 ≤ reward * mass := mul_nonneg hreward hmass
  have hretmul := mul_le_mul_of_nonneg_right hret hbase
  calc
    (1 - u - v) * (reward * mass)
        ≤ (1 - v) / (1 + u) * (reward * mass) := hretmul
    _ = ((1 - v) * reference) *
          (reward * mass / ((1 + u) * reference)) := by
            field_simp [ne_of_gt href, ne_of_gt (show 0 < 1 + u by linarith)]
            <;> ring
    _ ≤ clean * (reward * mass / ((1 + u) * reference)) := hmul
    _ = clean * (reward * (mass / ((1 + u) * reference))) := by ring

theorem budget_load_le_one
    (Active : Finset Pat) (fiber : Pat → Finset (Finset V))
    (mass budget : Pat → ℚ) (Act : Sym2 V → Finset Pat)
    (density : Sym2 V → ℚ)
    (hmass : ∀ σ, 0 ≤ mass σ) (hdensity : ∀ e, 0 < density e)
    (hcap : PatternCapacity Act mass density)
    (hAct : ∀ e, Act e ⊆ Active)
    (hbudget : ∀ σ ∈ Active, 0 < budget σ)
    (hactive : ∀ e σ, σ ∈ Active → 0 < oneCount fiber σ e → σ ∈ Act e)
    (hspread : ∀ e σ, σ ∈ Act e →
      (oneCount fiber σ e : ℚ) * density e ≤ budget σ)
    (e : Sym2 V) :
    ∑ σ ∈ Active, (oneCount fiber σ e : ℚ) *
        budgetCoefficient mass budget σ ≤ 1 := by
  classical
  calc
    ∑ σ ∈ Active, (oneCount fiber σ e : ℚ) * budgetCoefficient mass budget σ
        ≤ ∑ σ ∈ Active, (if σ ∈ Act e then mass σ / density e else 0) := by
          apply Finset.sum_le_sum
          intro σ hσ
          by_cases ha : σ ∈ Act e
          · rw [if_pos ha]
            exact budget_one_term_le (hmass σ) (hdensity e) (hbudget σ hσ)
              (hspread e σ ha)
          · rw [if_neg ha]
            have hz : oneCount fiber σ e = 0 := by
              by_contra hnz
              exact ha (hactive e σ hσ (Nat.pos_of_ne_zero hnz))
            simp [hz]
    _ = ∑ σ ∈ Act e, mass σ / density e :=
      sum_indicator_eq_of_subset Active (Act e) (fun σ => mass σ / density e) (hAct e)
    _ ≤ 1 := hcap e

noncomputable def budgetPacking
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
      (oneCount fiber σ e : ℚ) * density e ≤ budget σ) : FracPacking G :=
  canonicalPacking Active fiber (budgetCoefficient mass budget)
    (fun σ hσ => div_nonneg (hmass σ) (hbudget σ hσ).le)
    hitems (fun e _ => budget_load_le_one Active fiber mass budget Act density
      hmass hdensity hcap hAct hbudget hactive hspread e)

theorem budgetPacking_value_eq
    (Active : Finset Pat) (fiber : Pat → Finset (Finset V))
    (mass budget reward : Pat → ℚ) (Act : Sym2 V → Finset Pat)
    (density : Sym2 V → ℚ)
    (hmass : ∀ σ, 0 ≤ mass σ) (hdensity : ∀ e, 0 < density e)
    (hcap : PatternCapacity Act mass density)
    (hAct : ∀ e, Act e ⊆ Active)
    (hbudget : ∀ σ ∈ Active, 0 < budget σ)
    (hitems : ∀ σ ∈ Active, fiber σ ⊆ items G)
    (hactive : ∀ e σ, σ ∈ Active → 0 < oneCount fiber σ e → σ ∈ Act e)
    (hspread : ∀ e σ, σ ∈ Act e →
      (oneCount fiber σ e : ℚ) * density e ≤ budget σ)
    (hreward : ∀ σ ∈ Active, ∀ K ∈ fiber σ, gainF ℚ K = reward σ) :
    (budgetPacking Active fiber mass budget Act density hmass hdensity hcap hAct
      hbudget hitems hactive hspread).value
      = ∑ σ ∈ Active, ((fiber σ).card : ℚ) *
          (reward σ * budgetCoefficient mass budget σ) := by
  exact canonicalPacking_value_eq Active fiber (budgetCoefficient mass budget)
    reward
    (fun σ hσ => div_nonneg (hmass σ) (hbudget σ hσ).le)
    hitems (fun e _ => budget_load_le_one Active fiber mass budget Act density
      hmass hdensity hcap hAct hbudget hactive hspread e) hreward

end PaperIV.RC01CanonicalNormalization

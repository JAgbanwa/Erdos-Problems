import PaperIV.SpreadPacking
import PaperIV.RC01CanonicalSlackBridge

/-!
# RC01: the cleaned spread packing

This is the synthesis of the two local RC01 developments.  `PatternTransfer`
supplies the mass and the capacity ledger by reduced pattern; the cleaned
canonical construction supplies an arbitrary positive budget for each literal
fibre.  Taking the budget to be `(1+u)` times the rooted reference volume makes
the packing feasible after deleting the two-sided exceptional roots, without
requiring the false pointwise mean condition for every physical edge.
-/

namespace PaperIV.RC01CleanedSpreadPacking

open Finset
open MixedRounding
open PaperIV.PatternTransfer
open PaperIV.RC01CanonicalFractional
open PaperIV.RC01CanonicalNormalization
open PaperIV.WeightedPatternCoins

variable {V P : Type*} [Fintype V] [DecidableEq V]
  [Fintype P] [DecidableEq P]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Patterns retained by RC01 which serve the physical pair of an edge. -/
noncomputable def activeServing (Pats : Finset (Finset P)) (part : V → P)
    (e : Sym2 V) : Finset (Finset P) :=
  Pats.filter (fun H => H ∈ servingT part e)

theorem activeServing_subset (Pats : Finset (Finset P)) (part : V → P)
    (e : Sym2 V) : activeServing Pats part e ⊆ Pats :=
  Finset.filter_subset _ _

/-- The transferred pattern masses satisfy the exact capacity predicate used
by `budgetPacking`, after restriction to the retained patterns. -/
theorem activeServing_patternCapacity (x : FracPacking G) (part : V → P)
    (Pats : Finset (Finset P)) :
    PatternCapacity (activeServing Pats part) (psiT x part) (densT G part) := by
  intro e
  have hd : 0 < densT G part e := densT_pos part e
  have hsub : activeServing Pats part e ⊆ servingT part e := by
    intro H hH
    exact (Finset.mem_filter.1 hH).2
  have hsum : ∑ H ∈ activeServing Pats part e, psiT x part H
      ≤ ∑ H ∈ servingT part e, psiT x part H :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun H _ _ => psiT_nonneg x part H)
  calc
    ∑ H ∈ activeServing Pats part e, psiT x part H / densT G part e
        = (∑ H ∈ activeServing Pats part e, psiT x part H) / densT G part e := by
            rw [Finset.sum_div]
    _ ≤ (∑ H ∈ servingT part e, psiT x part H) / densT G part e :=
      div_le_div_of_nonneg_right hsum hd.le
    _ ≤ 1 := by
      rw [div_le_one hd]
      exact transfer_capacity x part e

/-- The cleaned, spread fractional packing.  `hspread` is now allowed to use a
larger reference budget, so it is exactly what the bilateral rooted cleanup
proves outside its deleted roots. -/
noncomputable def cleanedSpreadPacking (x : FracPacking G) (part : V → P)
    (Pats : Finset (Finset P)) (copies : Finset P → Finset (Finset V))
    (budget : Finset P → ℚ)
    (hbudget : ∀ H ∈ Pats, 0 < budget H)
    (hsub : ∀ H ∈ Pats, copies H ⊆ items G)
    (hserve : ∀ H ∈ Pats, ∀ K ∈ copies H, ∀ e : Sym2 V,
      e ∈ pairs K → H ∈ servingT part e)
    (hspread : ∀ e H, H ∈ activeServing Pats part e →
      (oneCount copies H e : ℚ) * densT G part e ≤ budget H) : FracPacking G :=
  budgetPacking Pats copies (psiT x part) budget
    (activeServing Pats part) (densT G part)
    (fun H => psiT_nonneg x part H) (fun e => densT_pos part e)
    (activeServing_patternCapacity x part Pats)
    (activeServing_subset Pats part) hbudget hsub
    (by
      intro e H hH hcount
      have hnonempty : ((copies H).filter (fun K => e ∈ pairs K)).Nonempty :=
        Finset.card_pos.1 hcount
      let K := hnonempty.choose
      have hKmem := Finset.mem_filter.1 hnonempty.choose_spec
      exact Finset.mem_filter.2 ⟨hH, hserve H hH K hKmem.1 e hKmem.2⟩)
    hspread

end PaperIV.RC01CleanedSpreadPacking

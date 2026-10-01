import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Tactic.Positivity

/-!
# RD09 finite averaging certificates

This module isolates the elementary finite averaging step used twice by the
RD09 local constructor.  It deliberately knows nothing about graphs.  The
input is a finite, nonempty family of literal assignments and a nonnegative
integer defect attached to each assignment.  A global incidence count then
produces one assignment whose defect is no larger than the average.

Keeping the conclusion in cross-multiplied form avoids division and is the
form consumed by the later root--colour and factor--candidate adapters.
-/

namespace PaperIV.RD09FiniteAveraging

open scoped BigOperators

variable {Assignment : Type*} [Fintype Assignment] [Nonempty Assignment]

/-- A finite family contains an element whose rational cost is at most the
average cost, stated without division. -/
theorem exists_card_mul_cost_le_sum (cost : Assignment → ℚ) :
    ∃ a : Assignment,
      (Fintype.card Assignment : ℚ) * cost a ≤ ∑ b : Assignment, cost b := by
  classical
  let total : ℚ := ∑ b : Assignment, cost b
  let average : ℚ := total / Fintype.card Assignment
  have hcard : (Fintype.card Assignment : ℚ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hsum :
      (∑ b : Assignment, cost b) ≤ ∑ _b : Assignment, average := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, average, total]
    rw [mul_div_cancel₀ _ hcard]
  obtain ⟨a, -, ha⟩ :=
    Finset.exists_le_of_sum_le
      (Finset.univ_nonempty : (Finset.univ : Finset Assignment).Nonempty) hsum
  refine ⟨a, ?_⟩
  calc
    (Fintype.card Assignment : ℚ) * cost a
        ≤ (Fintype.card Assignment : ℚ) * average :=
          mul_le_mul_of_nonneg_left ha (by positivity)
    _ = ∑ b : Assignment, cost b := by
      exact mul_div_cancel₀ _ hcard

/-- Integer form of finite averaging.  This is the form needed when `cost`
counts invalid bases or failed factors. -/
theorem exists_card_mul_natCost_le_sum (cost : Assignment → ℕ) :
    ∃ a : Assignment,
      Fintype.card Assignment * cost a ≤ ∑ b : Assignment, cost b := by
  obtain ⟨a, ha⟩ :=
    exists_card_mul_cost_le_sum (fun b : Assignment => (cost b : ℚ))
  refine ⟨a, ?_⟩
  exact_mod_cast ha

/-- If the total integer defect is at most `T`, one assignment has
cross-multiplied defect at most `T`. -/
theorem exists_card_mul_natCost_le_of_sum_le (cost : Assignment → ℕ) (T : ℕ)
    (htotal : (∑ b : Assignment, cost b) ≤ T) :
    ∃ a : Assignment, Fintype.card Assignment * cost a ≤ T := by
  obtain ⟨a, ha⟩ := exists_card_mul_natCost_le_sum cost
  exact ⟨a, ha.trans htotal⟩

/-- Rational-budget version used directly by inequalities such as RD09-L1:
if the total integral defect is bounded by `T`, some assignment has defect at
most `T / |Assignment|`. -/
theorem exists_natCost_le_div_of_sum_le (cost : Assignment → ℕ) (T : ℚ)
    (htotal : (∑ b : Assignment, (cost b : ℚ)) ≤ T) :
    ∃ a : Assignment, (cost a : ℚ) ≤ T / Fintype.card Assignment := by
  obtain ⟨a, ha⟩ := exists_card_mul_cost_le_sum (fun b => (cost b : ℚ))
  refine ⟨a, (le_div_iff₀' ?_).2 ?_⟩
  · exact_mod_cast Fintype.card_pos
  · exact ha.trans htotal

/-! ## Cyclic/group shifts suffice

The RD09 phase-I proof is usually phrased as an average over every bijection
between colour classes and roots.  That factorial assignment space is
unnecessary.  After labelling both sides by any finite group, the translations
`i ↦ i * shift` already form a balanced family: for fixed `i`, every target is
reached exactly once. -/

section GroupShifts

variable {Index : Type*} [Fintype Index] [Nonempty Index] [Group Index]

/-- Number of bad class--root pairs produced by a group translation. -/
def shiftCost (bad : Index → Index → ℕ) (shift : Index) : ℕ :=
  ∑ i : Index, bad i (i * shift)

omit [Nonempty Index] in
/-- Exact double count: summing the defects of all translations counts every
ordered class--root incidence exactly once. -/
theorem sum_shiftCost_eq (bad : Index → Index → ℕ) :
    (∑ shift : Index, shiftCost bad shift) = ∑ i : Index, ∑ root : Index, bad i root := by
  classical
  simp only [shiftCost]
  rw [Finset.sum_comm]
  apply Fintype.sum_congr
  intro i
  exact Fintype.sum_bijective (fun shift : Index => i * shift)
    (Group.mulLeft_bijective i) _ (fun root => bad i root) (fun _ => rfl)

/-- One of the `|Index|` explicit translations has defect at most the average
over all ordered incidences.  This replaces the factorial averaging step in
RD09-L1. -/
theorem exists_shift_card_mul_cost_le_total (bad : Index → Index → ℕ) :
    ∃ shift : Index,
      Fintype.card Index * shiftCost bad shift
        ≤ ∑ i : Index, ∑ root : Index, bad i root := by
  obtain ⟨shift, hshift⟩ := exists_card_mul_natCost_le_sum (shiftCost bad)
  rw [sum_shiftCost_eq] at hshift
  exact ⟨shift, hshift⟩

/-- Budgeted form of the explicit-shift averaging certificate. -/
theorem exists_shift_card_mul_cost_le_of_total_le (bad : Index → Index → ℕ)
    (T : ℕ) (htotal : (∑ i : Index, ∑ root : Index, bad i root) ≤ T) :
    ∃ shift : Index, Fintype.card Index * shiftCost bad shift ≤ T := by
  obtain ⟨shift, hshift⟩ := exists_shift_card_mul_cost_le_total bad
  exact ⟨shift, hshift.trans htotal⟩

end GroupShifts

end PaperIV.RD09FiniteAveraging

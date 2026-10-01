import Mathlib

/-!
# Selecting the critical split-terminal branch

Once the split LP identifies the terminal value as the maximum of three
branches, this order-theoretic lemma isolates the critical one near the
extremal threshold.  It is intentionally independent of the calculation of
the three branches.
-/

namespace PaperIV

theorem critical_branch_of_near_max {α : Type*} [LinearOrder α]
    {critical middle third threshold value : α}
    (hvalue : value = max critical (max middle third))
    (hnear : threshold ≤ value)
    (hmiddle : middle < threshold)
    (hthird : third < threshold) :
    value = critical := by
  have htail : max middle third < threshold := max_lt hmiddle hthird
  have htail_le : max middle third ≤ critical := by
    by_contra hnot
    have hlt : critical < max middle third := lt_of_not_ge hnot
    have hcollapse : value = max middle third := by
      rw [hvalue, max_eq_right (le_of_lt hlt)]
    rw [hcollapse] at hnear
    exact (not_le_of_gt htail) hnear
  rw [hvalue, max_eq_left htail_le]

end PaperIV

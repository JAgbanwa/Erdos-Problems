import Mathlib

/-!
# First entry below a threshold, with a window (component E3, part B)

The copy path of the candidate route produces a finite sequence of labelled
distances.  The first-entry argument needs exactly this: if the sequence starts at
or above a threshold `r`, ends strictly below it, and never moves by more than `δ`
in one step, then at the **least** index where it is below `r` it is still within
`δ` of `r`.

Nothing here assumes monotonicity: the sequence may oscillate arbitrarily, as long
as each single step is bounded by `δ`.

## Intended instantiation

`N` is the length of the copy path, `d i` is the labelled distance of the `i`-th
graph of the path to the fixed critical split family (for instance
`PaperIV.EditMetric.famDistNorm` of its edge set), `r` is the threshold `ε/2`, and
`δ = 1/n`, for which `exists_first_entry_window_inv_nat` is the ready-made form.
This module proves nothing about graphs or chordality; it is the scalar interface
only.
-/

namespace PaperIV.FirstEntryWindow

variable {N : ℕ} (d : Fin (N + 1) → ℚ) (r : ℚ)

/-! ## 1. The literal least index -/

/-- The indices at which the sequence is strictly below the threshold. -/
def belowSet : Finset (Fin (N + 1)) := Finset.univ.filter fun i => d i < r

lemma mem_belowSet {i : Fin (N + 1)} : i ∈ belowSet d r ↔ d i < r := by
  simp [belowSet]

lemma belowSet_nonempty (hlast : d (Fin.last N) < r) : (belowSet d r).Nonempty :=
  ⟨Fin.last N, (mem_belowSet d r).2 hlast⟩

/-- The **least** index at which the sequence is below the threshold.  It is a
literal minimum of a nonempty finite set, not a choice. -/
def firstBelow (hlast : d (Fin.last N) < r) : Fin (N + 1) :=
  (belowSet d r).min' (belowSet_nonempty d r hlast)

theorem firstBelow_lt (hlast : d (Fin.last N) < r) : d (firstBelow d r hlast) < r :=
  (mem_belowSet d r).1 (Finset.min'_mem _ _)

/-- Leastness: no earlier index is below the threshold. -/
theorem firstBelow_le (hlast : d (Fin.last N) < r) {i : Fin (N + 1)} (hi : d i < r) :
    firstBelow d r hlast ≤ i :=
  Finset.min'_le _ _ ((mem_belowSet d r).2 hi)

theorem le_of_lt_firstBelow (hlast : d (Fin.last N) < r) {i : Fin (N + 1)}
    (hi : i < firstBelow d r hlast) : r ≤ d i := by
  by_contra hcon
  push_neg at hcon
  exact absurd (firstBelow_le d r hlast hcon) (not_le.2 hi)

theorem firstBelow_ne_zero (h0 : r ≤ d 0) (hlast : d (Fin.last N) < r) :
    firstBelow d r hlast ≠ 0 := by
  intro h
  have hlt := firstBelow_lt d r hlast
  rw [h] at hlt
  exact absurd hlt (not_lt.2 h0)

/-! ## 2. The window -/

/-- **First-entry window.**  A sequence that starts at or above `r`, ends below `r`,
and has steps of size at most `δ` is, at its least index below `r`, within `δ` of the
threshold.  Monotonicity is *not* assumed. -/
theorem firstBelow_window {δ : ℚ} (h0 : r ≤ d 0) (hlast : d (Fin.last N) < r)
    (hstep : ∀ i : Fin N, |d i.succ - d i.castSucc| ≤ δ) :
    r - δ ≤ d (firstBelow d r hlast) ∧ d (firstBelow d r hlast) < r := by
  set j := firstBelow d r hlast with hj
  have hjlt : d j < r := firstBelow_lt d r hlast
  refine ⟨?_, hjlt⟩
  -- the least index is not the starting one
  have hj0 : (j : ℕ) ≠ 0 := by
    intro hval
    exact firstBelow_ne_zero d r h0 hlast (Fin.ext (by simpa using hval))
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hj0
  have hmN : m < N := by
    have := j.isLt
    omega
  -- the predecessor, as an index of the step family
  set i : Fin N := ⟨m, hmN⟩ with hi
  have hsucc : i.succ = j := Fin.ext (by simp [Fin.val_succ, hi, hm])
  have hcast_lt : i.castSucc < j := by
    rw [Fin.lt_def]
    simp [Fin.val_castSucc, hi, hm]
  -- before the first entry the sequence is still at or above the threshold
  have hge : r ≤ d i.castSucc := le_of_lt_firstBelow d r hlast hcast_lt
  have hstep_i := hstep i
  rw [hsucc] at hstep_i
  have hbounds := abs_le.1 hstep_i
  linarith [hbounds.1]

/-- Packaged existence form, convenient for instantiation by the route. -/
theorem exists_first_entry_window {δ : ℚ} (h0 : r ≤ d 0) (hlast : d (Fin.last N) < r)
    (hstep : ∀ i : Fin N, |d i.succ - d i.castSucc| ≤ δ) :
    ∃ j : Fin (N + 1),
      (∀ i : Fin (N + 1), d i < r → j ≤ i) ∧ r - δ ≤ d j ∧ d j < r := by
  obtain ⟨hlow, hhigh⟩ := firstBelow_window d r h0 hlast hstep
  exact ⟨firstBelow d r hlast, fun i hi => firstBelow_le d r hlast hi, hlow, hhigh⟩

/-- The form the graph route instantiates: steps of size at most `1 / n`. -/
theorem exists_first_entry_window_inv_nat (n : ℕ) (h0 : r ≤ d 0)
    (hlast : d (Fin.last N) < r)
    (hstep : ∀ i : Fin N, |d i.succ - d i.castSucc| ≤ 1 / (n : ℚ)) :
    ∃ j : Fin (N + 1),
      (∀ i : Fin (N + 1), d i < r → j ≤ i) ∧ r - 1 / (n : ℚ) ≤ d j ∧ d j < r :=
  exists_first_entry_window d r h0 hlast hstep

end PaperIV.FirstEntryWindow

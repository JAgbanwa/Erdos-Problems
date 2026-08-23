/-
# The designed region of a cell, counted.

The reservoir link of an outer vertex `u` of the grid design is its `F`-link inside
`BKLO.gridRegion h C (x u) (y u)`, the union of the `h` classes of its row with the `h` classes of
its column.  Those `2h - 1` classes are pairwise distinct and pairwise disjoint, so the region has
exactly `(2h - 1)t` vertices, where `t` is the common size of the classes.

This file records that count, together with the two inclusions that go with it: the region lies in
the pool `W'`, and it contains the class of the cell `(x u, y u)` itself.

Everything here is `sorry`-free.
-/
import BKLO.ReservoirDesignStructured

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-- A cell coordinate pair is a class index. -/
theorem grid_idx_lt {p j h : ℕ} (hp : p < h) (hj : j < h) : p * h + j < h * h := by
  calc p * h + j < p * h + h := by omega
    _ = (p + 1) * h := by ring
    _ ≤ h * h := Nat.mul_le_mul_right _ hp

section

variable {h cs : ℕ} {C : ℕ → Finset V}

/-- The row part of a region has `h` classes' worth of vertices. -/
theorem card_gridRow (hcard : ∀ i < h * h, (C i).card = cs)
    (hdisj : ∀ i < h * h, ∀ j < h * h, i ≠ j → Disjoint (C i) (C j)) {p : ℕ} (hp : p < h) :
    ((Finset.range h).biUnion (fun j => C (p * h + j))).card = h * cs := by
  classical
  rw [Finset.card_biUnion]
  · rw [Finset.sum_congr rfl fun j hj => hcard _ (grid_idx_lt hp (Finset.mem_range.1 hj))]
    simp [Finset.sum_const]
  · intro i hi j hj hij
    exact hdisj _ (grid_idx_lt hp (Finset.mem_range.1 hi)) _
      (grid_idx_lt hp (Finset.mem_range.1 hj)) (by omega)

/-- The column part of a region has `h` classes' worth of vertices. -/
theorem card_gridCol (hcard : ∀ i < h * h, (C i).card = cs)
    (hdisj : ∀ i < h * h, ∀ j < h * h, i ≠ j → Disjoint (C i) (C j)) {q : ℕ} (hq : q < h) :
    ((Finset.range h).biUnion (fun i => C (i * h + q))).card = h * cs := by
  classical
  have hhpos : 0 < h := lt_of_le_of_lt (Nat.zero_le q) hq
  rw [Finset.card_biUnion]
  · rw [Finset.sum_congr rfl fun i hi =>
      hcard _ (grid_idx_lt (Finset.mem_range.1 hi) hq)]
    simp [Finset.sum_const]
  · intro i hi j hj hij
    refine hdisj _ (grid_idx_lt (Finset.mem_range.1 hi) hq) _
      (grid_idx_lt (Finset.mem_range.1 hj) hq) ?_
    intro heq
    exact hij (Nat.eq_of_mul_eq_mul_right hhpos (by omega))

/-- The row part and the column part of a region meet exactly in the class of the cell. -/
theorem gridRow_inter_gridCol (hdisj : ∀ i < h * h, ∀ j < h * h, i ≠ j → Disjoint (C i) (C j))
    {p q : ℕ} (hp : p < h) (hq : q < h) :
    ((Finset.range h).biUnion (fun j => C (p * h + j)))
      ∩ ((Finset.range h).biUnion (fun i => C (i * h + q))) = C (p * h + q) := by
  classical
  ext a
  simp only [Finset.mem_inter, Finset.mem_biUnion, Finset.mem_range]
  constructor
  · rintro ⟨⟨j, hj, haj⟩, ⟨i, hi, hai⟩⟩
    by_cases heq : p * h + j = i * h + q
    · have hjq : j = q := by
        have h1 : (p * h + j) % h = j := by
          rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
        have h2 : (i * h + q) % h = q := by
          rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hq]
        rw [heq] at h1; omega
      rw [← hjq]; exact haj
    · exact absurd haj (Finset.disjoint_right.1
        (hdisj _ (grid_idx_lt hp hj) _ (grid_idx_lt hi hq) heq) hai)
  · intro ha
    exact ⟨⟨q, hq, ha⟩, ⟨p, hp, by simpa using ha⟩⟩

/-- **The size of a designed region**: the `2h - 1` classes of a row and a column. -/
theorem card_gridRegion (hcard : ∀ i < h * h, (C i).card = cs)
    (hdisj : ∀ i < h * h, ∀ j < h * h, i ≠ j → Disjoint (C i) (C j)) {p q : ℕ}
    (hp : p < h) (hq : q < h) :
    (gridRegion h C p q).card + cs = 2 * (h * cs) := by
  classical
  have hunion := Finset.card_union_add_card_inter
    ((Finset.range h).biUnion (fun j => C (p * h + j)))
    ((Finset.range h).biUnion (fun i => C (i * h + q)))
  rw [gridRow_inter_gridCol hdisj hp hq, hcard _ (grid_idx_lt hp hq),
    card_gridRow hcard hdisj hp, card_gridCol hcard hdisj hq] at hunion
  simpa [gridRegion, two_mul] using hunion

/-- The class of the cell `(p, q)` lies in the region of `(p, q)`. -/
theorem class_subset_gridRegion {p q : ℕ} (hq : q < h) :
    C (p * h + q) ⊆ gridRegion h C p q := by
  intro a ha
  exact Finset.mem_union_left _ (Finset.mem_biUnion.2 ⟨q, Finset.mem_range.2 hq, ha⟩)

/-- The region of a cell lies in the pool. -/
theorem gridRegion_subset {W' : Finset V} (hsub : ∀ i < h * h, C i ⊆ W') {p q : ℕ}
    (hp : p < h) (hq : q < h) : gridRegion h C p q ⊆ W' := by
  intro a ha
  rcases Finset.mem_union.1 ha with hrow | hcol
  · obtain ⟨j, hj, haj⟩ := Finset.mem_biUnion.1 hrow
    exact hsub _ (grid_idx_lt hp (Finset.mem_range.1 hj)) haj
  · obtain ⟨i, hi, hai⟩ := Finset.mem_biUnion.1 hcol
    exact hsub _ (grid_idx_lt (Finset.mem_range.1 hi) hq) hai

end

end BKLO

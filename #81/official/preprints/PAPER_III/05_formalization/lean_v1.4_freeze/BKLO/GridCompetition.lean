/-
# Two cells compete for a row-to-column edge.

The route that the grid design supports for `BKLO.GridPairingResidualClean` pairs, inside the link
of an outer vertex `u` of the cell `(p, q)`, the classes of the *row* `p` to the classes of the
*column* `q`.  Its point is this structural fact: an edge whose endpoints lie in the class `(p, j)`
and in the class `(i, q)` with `p ≠ i` and `j ≠ q` lies inside the designed region of exactly two
cells, `(p, q)` and `(i, j)`.  So the outer vertices that can ever use that edge are those of two
cells — at most `2(|D|/h² + 1)` of them — instead of the `|D|/h` outer vertices of a whole row,
which is what blocks the naive greedy.

`BKLO.grid_two_cell_competition` is that fact, with the classes only assumed pairwise disjoint and
the two endpoints only assumed to lie in the two given classes.

Everything here is `sorry`-free.
-/
import BKLO.GridRegionCard

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-- A grid index determines its row and column. -/
theorem grid_idx_inj {h p q p' q' : ℕ} (hq : q < h) (hq' : q' < h)
    (heq : p * h + q = p' * h + q') : p = p' ∧ q = q' := by
  have hh : 0 < h := lt_of_le_of_lt (Nat.zero_le q) hq
  have h1 : (p * h + q) % h = q := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hq]
  have h2 : (p' * h + q') % h = q' := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hq']
  have hqq : q = q' := by rw [← h1, heq, h2]
  refine ⟨?_, hqq⟩
  have : p * h = p' * h := by omega
  exact Nat.eq_of_mul_eq_mul_right hh this

/-- If a vertex of the class `(p, j)` lies in the region of the cell `(p', q')`, then that cell is
in the row `p` or in the column `j`. -/
theorem row_or_col_of_mem_gridRegion {h : ℕ} {C : ℕ → Finset V}
    (hdisj : ∀ i < h * h, ∀ j < h * h, i ≠ j → Disjoint (C i) (C j)) {p j p' q' : ℕ}
    (hp : p < h) (hj : j < h) (hp' : p' < h) (hq' : q' < h) {a : V}
    (ha : a ∈ C (p * h + j)) (hreg : a ∈ gridRegion h C p' q') : p' = p ∨ q' = j := by
  rcases Finset.mem_union.1 hreg with hrow | hcol
  · obtain ⟨j₀, hj₀, ha₀⟩ := Finset.mem_biUnion.1 hrow
    have hj₀' : j₀ < h := Finset.mem_range.1 hj₀
    by_cases heq : p' * h + j₀ = p * h + j
    · exact Or.inl (grid_idx_inj hj₀' hj heq).1
    · exact absurd ha (Finset.disjoint_left.1
        (hdisj _ (grid_idx_lt hp' hj₀') _ (grid_idx_lt hp hj) heq) ha₀)
  · obtain ⟨i₀, hi₀, ha₀⟩ := Finset.mem_biUnion.1 hcol
    have hi₀' : i₀ < h := Finset.mem_range.1 hi₀
    by_cases heq : i₀ * h + q' = p * h + j
    · exact Or.inr (grid_idx_inj hq' hj heq).2
    · exact absurd ha (Finset.disjoint_left.1
        (hdisj _ (grid_idx_lt hi₀' hq') _ (grid_idx_lt hp hj) heq) ha₀)

/-- **Two cells compete for a row-to-column edge.**  If `a` lies in the class `(p, j)`, `b` lies in
the class `(i, q)`, the rows `p`, `i` and the columns `j`, `q` are distinct, and both `a` and `b`
lie in the designed region of the cell `(p', q')`, then that cell is `(p, q)` or `(i, j)`. -/
theorem grid_two_cell_competition {h : ℕ} {C : ℕ → Finset V}
    (hdisj : ∀ i < h * h, ∀ j < h * h, i ≠ j → Disjoint (C i) (C j)) {p q i j p' q' : ℕ}
    (hp : p < h) (hq : q < h) (hi : i < h) (hj : j < h) (hp' : p' < h) (hq' : q' < h)
    (hpi : p ≠ i) (hjq : j ≠ q) {a b : V}
    (ha : a ∈ C (p * h + j)) (hb : b ∈ C (i * h + q))
    (hareg : a ∈ gridRegion h C p' q') (hbreg : b ∈ gridRegion h C p' q') :
    (p' = p ∧ q' = q) ∨ (p' = i ∧ q' = j) := by
  have h1 := row_or_col_of_mem_gridRegion hdisj hp hj hp' hq' ha hareg
  have h2 := row_or_col_of_mem_gridRegion hdisj hi hq hp' hq' hb hbreg
  rcases h1 with h1 | h1
  · rcases h2 with h2 | h2
    · exact absurd (h1 ▸ h2 : p = i) hpi
    · exact Or.inl ⟨h1, h2⟩
  · rcases h2 with h2 | h2
    · exact Or.inr ⟨h2, h1⟩
    · exact absurd (h1 ▸ h2 : j = q) hjq

end BKLO

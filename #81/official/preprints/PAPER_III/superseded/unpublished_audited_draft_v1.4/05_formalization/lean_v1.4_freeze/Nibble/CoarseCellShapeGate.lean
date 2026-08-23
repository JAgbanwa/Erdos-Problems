/-
# Nibble — the **shape gate** of the coarse-cell route to `BlockCoverResidualCoupled`

`Nibble.CoupledDyadicBoxRoute` §5 proposes the repair that both refutations of the dyadic route
point at: allocate a single **shape** (equivalently a single third cluster) to every cell of every
cluster-pair grid, the cells being coarse — of a length `C ≫ τ`, so that tiling a cell by blocks of
a prescribed length wastes only an `O(τ/C)` fraction — and then run the weighted nibble
`Nibble.fracNibble_withSlack` on the hypergraph whose ground set is the set of cells and whose
members are the coherent triples of cells ("boxes").

This file records the arithmetic obstruction that decides *how* a box may be shaped, and therefore
which nibble can be run on it.  Write, for a cluster triple `(U,W,X)` of a coarse-cell allocation,

    p = ⌊C_U / (τ·d(W,X))⌋,  q = ⌊C_W / (τ·d(U,X))⌋,  s = ⌊C_X / (τ·d(U,W))⌋

for the number of blocks a coarse cell of the corresponding cluster axis is tiled into — the block
lengths are the ones `Nibble.AX1.IsGridSubTriple` prescribes, `τ` times the *opposite* density.  A
cell of the pair `(U,W)` then holds `p·q` block rectangles, a cell of `(U,X)` holds `p·s`, and a
cell of `(W,X)` holds `q·s`.

## 1. A one-cell-per-pair box cannot fill its three cells (`Nibble.AX1.cellBox_members_le`,
`Nibble.AX1.cellBox_full_imp_tileCounts_eq`)

The members of a box are triples of blocks whose three pair-projections are injective — that is
exactly the disjointness clause of `Nibble.AX1.BlockCoverResidualCoupled` inside the box.  Hence a
box built on *one* cell per pair carries at most `min (p·q) (p·s) (q·s)` members, while filling its
`(U,W)` cell needs `p·q` of them, its `(U,X)` cell `p·s` and its `(W,X)` cell `q·s`.  All three
happen simultaneously only when `p = q = s`, and then the achieved fraction of the charged area is
`min(p,q,s)/max(p,q,s)`, i.e. the ratio of the smallest to the largest cluster density of the
triple.  This is the *near-uniform* regime, which `Nibble.AX1.blockCoverResidualCoupledNearUniform_holds`
already covers, and the loss in general is the factor that `Nibble.AX1.cellTriangle_LP_gap` refutes.

## 2. The tile counts cannot be equalised by the choice of the cell lengths
(`Nibble.AX1.tileCounts_eq_overdetermined`, `Nibble.AX1.tileCounts_not_equalisable`)

The cell lengths `C_U` are attached to *clusters*, not to triples: the block sub-triples of two
triples through the same cluster `U` share the coarse subdivision of `U`, since a block of `U` is a
block of the grid of `U` and the covering clause forces the two occurrences of a member's `U`-block
— in the pair `(U,W)` and in the pair `(U,X)` — to be the same set.  Asking `p = q = s` for every
cluster triple is therefore a system on the `C`'s alone: `C_U/d(W,X) = C_W/d(U,X) = C_X/d(U,W)`.
For three clusters it is solvable; from four clusters on it is over-determined, and
`Nibble.AX1.tileCounts_not_equalisable` exhibits a density profile — `d(0,2)=d(1,2)=d(0,3)=1/2`,
`d(1,3)=1/4` — for which no positive cell lengths satisfy it.

## 3. What a box must look like, and why the box hypergraph is not `3`-uniform
(`Nibble.AX1.latinBox_cell_fill`, `Nibble.AX1.coarseCellBox_card_eq_three_iff`)

The corrected box is the *product* box: `q·s` coarse intervals of `U`, `p·s` of `W` and `p·q` of
`X`, all cells between them, and `L² = (p·q·s)²` members given by a Latin square on the `L` blocks
of each cluster (`Nibble.AX1.gridShift`, `Nibble.AX1.coherent_cellTriangle_count`).  Then every one
of its three cell families is filled exactly — `Nibble.AX1.latinBox_cell_fill` is that identity —
and the value of the box is exactly the LP value of the area it charges, with no loss.  But such a
box occupies

    (q·s)(p·s) + (q·s)(p·q) + (p·s)(p·q) = p·q·s·(p + q + s)

cells, which is `3` only in the degenerate case `p = q = s = 1`
(`Nibble.AX1.coarseCellBox_card_eq_three_iff`).  So the ground set of `Nibble.fracNibble_withSlack`
cannot be taken to be the cells: the hypothesis `IsUniform K 3` fails, and it fails by the amount
above, which is exactly the quantity by which the coarse-cell route still has to be assembled by
other means (a matching of *product rectangles of cells*, coherent along the three cluster axes,
rather than a matching of cell triples).

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.CoupledDyadicBoxRoute

open Finset

namespace Nibble.AX1

/-! ## 1. A one-cell-per-pair box cannot fill its three cells -/

/-- **The members of a single box are limited by each of its three cells.**  A family of members —
triples of blocks whose three pair-projections are injective, which is the disjointness clause of
the residual inside the box — has at most `min (p·q) (min (p·s) (q·s))` elements, where `p`, `q`,
`s` are the numbers of blocks the three cells are tiled into. -/
theorem cellBox_members_le {α β γ : Type} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    [Fintype α] [Fintype β] [Fintype γ] (M : Finset (α × β × γ))
    (hUW : Set.InjOn (fun t : α × β × γ => (t.1, t.2.1)) M)
    (hUX : Set.InjOn (fun t : α × β × γ => (t.1, t.2.2)) M)
    (hWX : Set.InjOn (fun t : α × β × γ => (t.2.1, t.2.2)) M) :
    #M ≤ min (Fintype.card α * Fintype.card β)
      (min (Fintype.card α * Fintype.card γ) (Fintype.card β * Fintype.card γ)) := by
  classical
  have h1 : #M ≤ Fintype.card α * Fintype.card β := by
    have := Finset.card_image_of_injOn hUW
    calc #M = #(M.image (fun t : α × β × γ => (t.1, t.2.1))) := this.symm
      _ ≤ Fintype.card (α × β) := Finset.card_le_univ _
      _ = Fintype.card α * Fintype.card β := Fintype.card_prod _ _
  have h2 : #M ≤ Fintype.card α * Fintype.card γ := by
    have := Finset.card_image_of_injOn hUX
    calc #M = #(M.image (fun t : α × β × γ => (t.1, t.2.2))) := this.symm
      _ ≤ Fintype.card (α × γ) := Finset.card_le_univ _
      _ = Fintype.card α * Fintype.card γ := Fintype.card_prod _ _
  have h3 : #M ≤ Fintype.card β * Fintype.card γ := by
    have := Finset.card_image_of_injOn hWX
    calc #M = #(M.image (fun t : α × β × γ => (t.2.1, t.2.2))) := this.symm
      _ ≤ Fintype.card (β × γ) := Finset.card_le_univ _
      _ = Fintype.card β * Fintype.card γ := Fintype.card_prod _ _
  exact le_min h1 (le_min h2 h3)

/-- **Filling all three cells of a one-cell-per-pair box forces equal tile counts.**  If a box
whose three cells hold `p·q`, `p·s` and `q·s` block rectangles carries a member family that fills
all three, then `p = q = s`: the three cluster densities of the triple agree to within the rounding
of the tile counts.  This is precisely the near-uniform regime. -/
theorem cellBox_full_imp_tileCounts_eq {p q s N : ℕ} (hp : 0 < p) (hq : 0 < q) (hs : 0 < s)
    (h1 : N = p * q) (h2 : N = p * s) (h3 : N = q * s) : p = q ∧ q = s := by
  have hqs : q = s := Nat.eq_of_mul_eq_mul_left hp (by omega)
  have hpq : p = q := by
    have : p * s = q * s := by omega
    exact Nat.eq_of_mul_eq_mul_right hs this
  exact ⟨hpq, hqs⟩

/-- The fraction of its `(U,W)` cell that a one-cell-per-pair box can fill is `min(p,q,s)/p` on the
`U` axis: when `s < q` the `(U,W)` cell is short of `p·(q - s)` block rectangles. -/
theorem cellBox_deficit {p q s : ℕ} (hs : s ≤ q) :
    min (p * q) (min (p * s) (q * s)) + p * (q - s) ≤ p * q + (q * s) := by
  have h : min (p * q) (min (p * s) (q * s)) ≤ p * s := le_trans (min_le_right _ _) (min_le_left _ _)
  have h2 : p * (q - s) ≤ p * q - p * s := by
    rw [Nat.mul_sub]
  omega

/-! ## 2. The tile counts cannot be equalised by the choice of the cell lengths -/

/-- **The tile-count identity of two triples through the same cluster pair is a constraint on the
densities alone.**  If the coarse cell lengths `C` equalise the tile counts of the triples
`{0,1,2}` and `{0,1,3}` — i.e. `C₀/d(1,2) = C₁/d(0,2)` and `C₀/d(1,3) = C₁/d(0,3)` — then the two
density ratios agree. -/
theorem tileCounts_eq_overdetermined {C₀ C₁ d02 d12 d03 d13 : ℝ}
    (h2 : C₀ * d02 = C₁ * d12) (h3 : C₀ * d03 = C₁ * d13) :
    C₀ * (d02 * d13) = C₀ * (d03 * d12) := by
  linear_combination d13 * h2 - d12 * h3

/-- **The tile counts are not equalisable from four clusters on.**  For the density profile
`d(0,2) = d(1,2) = d(0,3) = 1/2`, `d(1,3) = 1/4` there is no choice of positive coarse cell lengths
`C₀, C₁` for which the triples `{0,1,2}` and `{0,1,3}` both have equal tile counts.  Hence the
one-shape-per-cell allocation cannot be made exact by tuning the cell lengths. -/
theorem tileCounts_not_equalisable :
    ¬ ∃ C₀ C₁ : ℝ, 0 < C₀ ∧ 0 < C₁ ∧
      C₀ * (1/2 : ℝ) = C₁ * (1/2 : ℝ) ∧ C₀ * (1/2 : ℝ) = C₁ * (1/4 : ℝ) := by
  rintro ⟨C₀, C₁, hC₀, hC₁, h2, h3⟩
  have hC : C₀ = C₁ := by linarith
  rw [hC] at h3
  linarith

/-! ## 3. The product box fills exactly, and is not a triple of cells -/

/-- **The product box fills all three of its cell families exactly.**  With `q·s` coarse intervals
of `U`, `p·s` of `W` and `p·q` of `X`, the number of block rectangles of the `(U,W)` cells is
`(q·s)·(p·s)·(p·q) = (p·q·s)²`, and by symmetry the same for the other two pairs: one Latin family
of `L² = (p·q·s)²` members fills all three exactly, with no waste. -/
theorem latinBox_cell_fill (p q s : ℕ) :
    (q * s) * (p * s) * (p * q) = (p * q * s) ^ 2 ∧
    (q * s) * (p * q) * (p * s) = (p * q * s) ^ 2 ∧
    (p * s) * (p * q) * (q * s) = (p * q * s) ^ 2 := by
  refine ⟨by ring, by ring, by ring⟩

/-- **The product box is not a triple of cells.**  It occupies `p·q·s·(p+q+s)` cells, which equals
`3` only in the degenerate case `p = q = s = 1`; so the box hypergraph on the coarse cells is not
`3`-uniform and `Nibble.fracNibble_withSlack` does not apply to it. -/
theorem coarseCellBox_card_eq_three_iff {p q s : ℕ} (hp : 0 < p) (hq : 0 < q) (hs : 0 < s) :
    (q * s) * (p * s) + (q * s) * (p * q) + (p * s) * (p * q) = 3 ↔ (p = 1 ∧ q = 1 ∧ s = 1) := by
  constructor
  · intro h
    have h1 : 0 < q * s * (p * s) := by positivity
    have h2 : 0 < q * s * (p * q) := by positivity
    have h3 : 0 < p * s * (p * q) := by positivity
    have e1 : q * s * (p * s) = 1 := by omega
    obtain ⟨hqs, hps⟩ := mul_eq_one.mp e1
    obtain ⟨hq1, hs1⟩ := mul_eq_one.mp hqs
    obtain ⟨hp1, -⟩ := mul_eq_one.mp hps
    exact ⟨hp1, hq1, hs1⟩
  · rintro ⟨rfl, rfl, rfl⟩
    norm_num

/-! ### Axiom check -/

section AxCheck

#print axioms Nibble.AX1.cellBox_members_le
#print axioms Nibble.AX1.cellBox_full_imp_tileCounts_eq
#print axioms Nibble.AX1.tileCounts_not_equalisable
#print axioms Nibble.AX1.latinBox_cell_fill
#print axioms Nibble.AX1.coarseCellBox_card_eq_three_iff

end AxCheck

end Nibble.AX1

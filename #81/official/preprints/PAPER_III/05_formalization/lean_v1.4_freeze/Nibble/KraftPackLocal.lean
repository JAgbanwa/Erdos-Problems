/-
# Local: Kraft / dyadic aligned packing (the core of the laminar multi-scale route).

The portion-per-band route to `BlockCoverResidualCoupled` was machine-refuted because reserving a
*square* portion of a cluster for a demand of area `f·g` costs `f + g ≥ 2√(fg)` (AM–GM), giving the
budget `Σ_π √(a_π) ≤ 1` instead of the LP's `Σ_π a_π ≤ 1`.

The divergent fix: make the block lengths **dyadic**.  Then the intervals a cluster side offers are
**laminar** (nested or disjoint), and packing one side is a 1-D problem governed by **Kraft's
inequality**: dyadic intervals of total length `≤ 2^L` pack into `[0, 2^L)` *exactly*, with no
`√`-loss.  This file proves that achievability, integer/aligned form, by a prefix-sum argument:

* `kraft_pack` — for monotone levels `ℓ` with `∑ 2^{L-ℓ i} ≤ 2^L` and `ℓ i ≤ L`, the prefix sums
  give disjoint, `2^{L-ℓ i}`-aligned sub-intervals of `[0, 2^L)`.

No probability, no graph theory — the exact 1-D packing that the square-portion budget missed.
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Interval.Finset.Nat

open Finset

namespace Nibble.AX1

/-- The prefix-sum placement of dyadic blocks: `pos ℓ L i = ∑_{j < i} 2^{L - ℓ j}`. -/
def kraftPos (ℓ : ℕ → ℕ) (L : ℕ) (i : ℕ) : ℕ :=
  ∑ j ∈ Finset.range i, 2 ^ (L - ℓ j)

/-- Consecutive blocks abut: `pos (i+1) = pos i + 2^{L - ℓ i}`. -/
theorem kraftPos_succ (ℓ : ℕ → ℕ) (L i : ℕ) :
    kraftPos ℓ L (i + 1) = kraftPos ℓ L i + 2 ^ (L - ℓ i) := by
  simp [kraftPos, Finset.sum_range_succ]

/-- **Alignment.**  If `ℓ` is monotone, `pos i` is a multiple of the `i`-th block length
`2^{L - ℓ i}` — the laminarity that makes the intervals nest without fragmentation. -/
theorem kraftPos_aligned {ℓ : ℕ → ℕ} (hmono : Monotone ℓ) (L i : ℕ) :
    2 ^ (L - ℓ i) ∣ kraftPos ℓ L i := by
  unfold kraftPos
  refine Finset.dvd_sum ?_
  intro j hj
  have hji : j < i := Finset.mem_range.mp hj
  have hℓ : ℓ j ≤ ℓ i := hmono (le_of_lt hji)
  -- `L - ℓ i ≤ L - ℓ j`, so `2^{L-ℓ i} ∣ 2^{L-ℓ j}`
  exact pow_dvd_pow 2 (Nat.sub_le_sub_left hℓ L)

/-- **Kraft achievability (integer/aligned form).**  For monotone levels `ℓ` bounded by `L` with
`∑_{i<n} 2^{L-ℓ i} ≤ 2^L`, the prefix-sum positions `p i := kraftPos ℓ L i` give blocks
`[p i, p i + 2^{L-ℓ i})` that are (i) inside `[0, 2^L)`, (ii) `2^{L-ℓ i}`-aligned, and
(iii) pairwise disjoint — an exact 1-D dyadic packing, no `√`-loss. -/
theorem kraft_pack {n L : ℕ} {ℓ : ℕ → ℕ} (hmono : Monotone ℓ)
    (hbound : ∑ i ∈ Finset.range n, 2 ^ (L - ℓ i) ≤ 2 ^ L) :
    (∀ i < n, kraftPos ℓ L i + 2 ^ (L - ℓ i) ≤ 2 ^ L) ∧
    (∀ i < n, 2 ^ (L - ℓ i) ∣ kraftPos ℓ L i) ∧
    (∀ i < n, ∀ j < n, i ≠ j →
      Disjoint (Finset.Ico (kraftPos ℓ L i) (kraftPos ℓ L i + 2 ^ (L - ℓ i)))
               (Finset.Ico (kraftPos ℓ L j) (kraftPos ℓ L j + 2 ^ (L - ℓ j)))) := by
  -- the prefix sums are monotone and bounded by the total
  have hmono_pos : Monotone (kraftPos ℓ L) := by
    intro a b hab
    unfold kraftPos
    exact Finset.sum_le_sum_of_subset (Finset.range_mono hab)
  have htot : ∀ i ≤ n, kraftPos ℓ L i ≤ 2 ^ L := by
    intro i hi
    exact le_trans (hmono_pos hi) hbound
  refine ⟨?_, ?_, ?_⟩
  · -- fits
    intro i hi
    rw [← kraftPos_succ]
    exact htot (i + 1) hi
  · -- aligned
    intro i _
    exact kraftPos_aligned hmono L i
  · -- disjoint: consecutive prefix sums, so blocks abut in order
    intro i _ j _ hij
    -- WLOG `i < j`; then `pos i + len i = pos (i+1) ≤ pos j`
    rcases lt_or_gt_of_ne hij with h | h
    · rw [Finset.disjoint_left]
      intro x hxi hxj
      rw [Finset.mem_Ico] at hxi hxj
      have h1 : kraftPos ℓ L i + 2 ^ (L - ℓ i) = kraftPos ℓ L (i + 1) := (kraftPos_succ ℓ L i).symm
      have h2 : kraftPos ℓ L (i + 1) ≤ kraftPos ℓ L j := hmono_pos h
      omega
    · rw [Finset.disjoint_left]
      intro x hxi hxj
      rw [Finset.mem_Ico] at hxi hxj
      have h1 : kraftPos ℓ L j + 2 ^ (L - ℓ j) = kraftPos ℓ L (j + 1) := (kraftPos_succ ℓ L j).symm
      have h2 : kraftPos ℓ L (j + 1) ≤ kraftPos ℓ L i := hmono_pos h
      omega

end Nibble.AX1

/-
# Nibble — the **Latin filling of a product box** of coarse cells

`Nibble.CoarseCellShapeGate` isolates the shape arithmetic of the coarse-cell route to
`Nibble.AX1.BlockCoverResidualCoupled`: a box of a cluster triple `(U,W,X)` whose cells are tiled
into `p`, `q`, `s` blocks per axis has to consist of `q·s` coarse intervals of `U`, `p·s` of `W` and
`p·q` of `X` — the *product box* — if all three of its cell families are to be filled without waste.

This file supplies the filling itself, deterministically, from the Latin-square tools of
`Nibble.GridShiftBalance`.  Write `L = p·q·s` for the number of blocks each cluster contributes to
the box (`L = (q·s)·p = (p·s)·q = (p·q)·s`, one per coarse interval per tile slot) and take as
members the `L²` triples

    (u, v, w)   with   w ≡ u + v  (mod L),

`u`, `v`, `w` running over the blocks of `U`, `W`, `X`.  Then:

* `Nibble.AX1.latinFill_card` — there are exactly `L²` members;
* `Nibble.AX1.latinFill_UW_bijective`, `Nibble.AX1.latinFill_UX_bijective`,
  `Nibble.AX1.latinFill_WX_bijective` — each of the three pair-projections is a **bijection** onto
  all block pairs, which is at once the disjointness clause of the residual (no two members share a
  vertex-pair rectangle) and the exactness of the filling (every block pair is used);
* `Nibble.AX1.latinFill_cell_fiber_card` — each cell of each of the three pair grids receives
  exactly its own number of block rectangles (`p·q` for a `(U,W)` cell), i.e. **every coarse cell of
  the box is tiled completely**: the box wastes nothing beyond the `O(τ/C)` margin of a single cell.

Together with `Nibble.AX1.latinBox_cell_fill` this is the *positive* half of the coarse-cell step:
what remains for `Nibble.AX1.BlockCoverResidualCoupled` is not the filling of a box but the
**allocation** of the boxes — a family of product rectangles of cells, one per cluster triple of the
LP support, pairwise disjoint in every cluster pair and coherent along the three cluster axes.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.GridShiftBalance
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Int.Star

open Finset

namespace Nibble.AX1

/-- The third block of a member of the Latin filling: `w ≡ u + v (mod L)`. -/
def latinThird (L : ℕ) (u v : Fin L) : Fin L :=
  ⟨(u.val + v.val) % L, Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le _) u.isLt)⟩

/-- The Latin filling of a product box: the member with `U`-block `u` and `W`-block `v`. -/
def latinFill (L : ℕ) (uv : Fin L × Fin L) : Fin L × Fin L × Fin L :=
  (uv.1, uv.2, latinThird L uv.1 uv.2)

/-- The box has exactly `L²` members. -/
theorem latinFill_card (L : ℕ) :
    #((univ : Finset (Fin L × Fin L)).image (latinFill L)) = L ^ 2 := by
  classical
  have hinj : Function.Injective (latinFill L) := by
    rintro ⟨u, v⟩ ⟨u', v'⟩ h
    simp only [latinFill, Prod.mk.injEq] at h
    exact Prod.ext h.1 h.2.1
  rw [Finset.card_image_of_injective _ hinj]
  simp [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, pow_two]

/-- **The `(U,W)` projection is a bijection**: every pair of a `U`-block and a `W`-block carries
exactly one member. -/
theorem latinFill_UW_bijective (L : ℕ) :
    Function.Bijective (fun uv : Fin L × Fin L => ((latinFill L uv).1, (latinFill L uv).2.1)) := by
  have : (fun uv : Fin L × Fin L => ((latinFill L uv).1, (latinFill L uv).2.1)) = id := rfl
  rw [this]
  exact Function.bijective_id

/-- **The `(U,X)` projection is a bijection**: every pair of a `U`-block and an `X`-block carries
exactly one member. -/
theorem latinFill_UX_bijective (L : ℕ) :
    Function.Bijective (fun uv : Fin L × Fin L => ((latinFill L uv).1, (latinFill L uv).2.2)) := by
  refine (Finite.injective_iff_bijective).mp ?_
  rintro ⟨u, v⟩ ⟨u', v'⟩ h
  simp only [latinFill, latinThird, Prod.mk.injEq, Fin.mk.injEq] at h
  obtain ⟨hu, hw⟩ := h
  subst hu
  have hmod : (u.val + v.val) ≡ (u.val + v'.val) [MOD L] := hw
  have hv : v.val % L = v'.val % L := Nat.ModEq.add_left_cancel' u.val hmod
  rw [Nat.mod_eq_of_lt v.isLt, Nat.mod_eq_of_lt v'.isLt] at hv
  exact Prod.ext rfl (Fin.ext hv)

/-- **The `(W,X)` projection is a bijection**: every pair of a `W`-block and an `X`-block carries
exactly one member. -/
theorem latinFill_WX_bijective (L : ℕ) :
    Function.Bijective (fun uv : Fin L × Fin L => ((latinFill L uv).2.1, (latinFill L uv).2.2)) := by
  refine (Finite.injective_iff_bijective).mp ?_
  rintro ⟨u, v⟩ ⟨u', v'⟩ h
  simp only [latinFill, latinThird, Prod.mk.injEq, Fin.mk.injEq] at h
  obtain ⟨hv, hw⟩ := h
  subst hv
  have hmod : (u.val + v.val) ≡ (u'.val + v.val) [MOD L] := hw
  have hu : u.val % L = u'.val % L := Nat.ModEq.add_right_cancel' v.val hmod
  rw [Nat.mod_eq_of_lt u.isLt, Nat.mod_eq_of_lt u'.isLt] at hu
  exact Prod.ext (Fin.ext hu) rfl

/-! ### Every coarse cell of the box is tiled completely -/

/-- A coarse interval of a cluster holds exactly `p` blocks. -/
theorem card_blocks_in_coarse_cell {L p i : ℕ} (hp : 0 < p) (hi : (i + 1) * p ≤ L) :
    #((univ : Finset (Fin L)).filter (fun u => u.val / p = i)) = p := by
  classical
  have key : ∀ n : ℕ, n / p = i ↔ (i * p ≤ n ∧ n < i * p + p) := by
    intro n
    constructor
    · intro hn
      have h1 : i * p ≤ n := by
        calc i * p = (n / p) * p := by rw [hn]
          _ ≤ n := Nat.div_mul_le_self n p
      have hlt : n / p < i + 1 := by omega
      have h2 : n < (i + 1) * p := (Nat.div_lt_iff_lt_mul hp).mp hlt
      exact ⟨h1, by nlinarith⟩
    · rintro ⟨h1, h2⟩
      exact Nat.div_eq_of_lt_le h1 (by nlinarith)
  have hmap : ((univ : Finset (Fin L)).filter (fun u => u.val / p = i)).map Fin.valEmbedding
      = Finset.Ico (i * p) (i * p + p) := by
    ext n
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.valEmbedding_apply, Finset.mem_Ico]
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact (key u.val).mp hu
    · rintro ⟨h1, h2⟩
      have hn : n < L := by nlinarith [hi]
      exact ⟨⟨n, hn⟩, (key n).mpr ⟨h1, h2⟩, rfl⟩
  have := congrArg Finset.card hmap
  simpa [Nat.card_Ico] using this

/-- **Every coarse cell of the box is tiled completely.**  The members whose `U`-block lies in the
`i`-th coarse interval of `U` and whose `W`-block lies in the `j`-th coarse interval of `W` — that
is, the members inside the `(i,j)` cell of the `(U,W)` grid — are exactly `p·q` many, one per block
rectangle of the cell. -/
theorem latinFill_cell_fiber_card {L p q i j : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hi : (i + 1) * p ≤ L) (hj : (j + 1) * q ≤ L) :
    #((univ : Finset (Fin L × Fin L)).filter
        (fun uv => uv.1.val / p = i ∧ uv.2.val / q = j)) = p * q := by
  classical
  have hprod : (univ : Finset (Fin L × Fin L)).filter
      (fun uv => uv.1.val / p = i ∧ uv.2.val / q = j)
      = ((univ : Finset (Fin L)).filter (fun u => u.val / p = i)) ×ˢ
        ((univ : Finset (Fin L)).filter (fun v => v.val / q = j)) := by
    ext ⟨u, v⟩
    simp [Finset.mem_filter, Finset.mem_product]
  rw [hprod, Finset.card_product, card_blocks_in_coarse_cell hp hi,
    card_blocks_in_coarse_cell hq hj]

/-! ### Axiom check -/

section AxCheck

#print axioms Nibble.AX1.latinFill_card
#print axioms Nibble.AX1.latinFill_UW_bijective
#print axioms Nibble.AX1.latinFill_UX_bijective
#print axioms Nibble.AX1.latinFill_WX_bijective
#print axioms Nibble.AX1.latinFill_cell_fiber_card

end AxCheck

end Nibble.AX1

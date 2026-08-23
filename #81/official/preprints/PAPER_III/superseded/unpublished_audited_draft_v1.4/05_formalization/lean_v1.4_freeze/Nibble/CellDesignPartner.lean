/-
# Nibble — the **partner-indexed cell design**

`Nibble.CoarseCellDiagonalDesign` builds a coarse-cell design in which the cell index of a cluster
is an element of `(Z × Z) × (Z × Z) × (Z × Z)`, one `Z × Z` block per *role* a cluster pair plays
inside a cluster triple (`ST`, `SY`, `TY`).  That design cannot be used globally: the ownership rule
of a fixed cluster pair reads a fixed one of the three blocks, so all the cluster triples through
that pair must give the pair the same role, i.e. the roles are a proper `3`-edge-colouring of the
cluster graph in which every triangle is rainbow.  A colour class of such a colouring is a matching,
so a complete cluster graph on `≥ 5` clusters admits none.

This file replaces the three role-blocks by **one block per partner cluster**: the cell index of a
cluster is a function

    CellH ι Z = ι → Z × Z,

`ι` the cluster index type, and the ownership value of the pair `(S, T)` at the cells `(gS, gT)` is

    pairVal S T gS gT = gS T + gT S,

the `T`-coordinate of `S`'s cell plus the `S`-coordinate of `T`'s cell.  Every pair reads its own
pair of coordinates, so no colouring is needed and the rule is symmetric in the pair.

For a cluster triple — three clusters `cl 0`, `cl 1`, `cl 2`, indexed by `ZMod 3` so that the whole
design is cyclically symmetric — a triple of value sets `own : ZMod 3 → Finset (Z × Z)`
(`own a` belongs to the pair *opposite* to `a`) selects the **coherent cell triangles**
(`Nibble.AX1.CoherentTri`), and

* `Nibble.AX1.blockIdx` assigns to a coherent triangle a *block index* inside each of its three
  cells, whose first component is the ownership value of the opposite pair;
* `Nibble.AX1.blockIdx_face_inj` — **the face injectivity**: two coherent triangles that agree in
  two cells and have the same two block indices there are equal.  This is what makes the block
  rectangles of the members pairwise disjoint;
* `Nibble.AX1.blockIdx_mem_box` — the block index of the cell `a` lies in a set of size
  `#(own a) · |Z| ^ (#ι - 2)`, which bounds the number of blocks a cell has to host;
* `Nibble.AX1.card_coherentTri_ge` — **the count**: there are at least
  `#(own 0) · #(own 1) · #(own 2) · |Z| ^ (6·#ι - 6)` coherent cell triangles, the number needed for
  the allocation to be lossless.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Field.ZMod
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Positivity

open Finset

namespace Nibble.AX1

section Design

variable {ι : Type*} [DecidableEq ι] [Fintype ι]
variable {Z : Type*} [AddCommGroup Z] [Fintype Z] [DecidableEq Z]

/-- **The cell index of a cluster**: one `Z × Z` coordinate per partner cluster. -/
abbrev CellH (ι Z : Type*) [AddCommGroup Z] := ι → Z × Z

/-- **The ownership value of a cluster pair**: the `T`-coordinate of the cell of `S` plus the
`S`-coordinate of the cell of `T`.  It is symmetric in the pair. -/
def pairVal (S T : ι) (gS gT : CellH ι Z) : Z × Z := gS T + gT S

theorem pairVal_comm (S T : ι) (gS gT : CellH ι Z) :
    pairVal S T gS gT = pairVal T S gT gS := add_comm _ _

variable (cl : ZMod 3 → ι)

/-- The ownership value of the pair opposite to the position `a`. -/
def cellVal (g : ZMod 3 → CellH ι Z) (a : ZMod 3) : Z × Z :=
  pairVal (cl (a + 1)) (cl (a + 2)) (g (a + 1)) (g (a + 2))

theorem cellVal_eq (g : ZMod 3 → CellH ι Z) (a : ZMod 3) :
    cellVal cl g a = g (a + 1) (cl (a + 2)) + g (a + 2) (cl (a + 1)) := rfl

/-- **A coherent cell triangle**: each of the three cluster pairs of the triple has its ownership
value in the value set of the opposite position. -/
def CoherentTri (own : ZMod 3 → Finset (Z × Z)) (g : ZMod 3 → CellH ι Z) : Prop :=
  ∀ a : ZMod 3, cellVal cl g a ∈ own a

/-- **The block index of a coherent cell triangle inside its cell at the position `a`.**  Its first
component is the ownership value of the opposite pair; its second component collects, from the two
other cells, the coordinates that the two faces at `a` need in order to be injective. -/
def blockIdx (g : ZMod 3 → CellH ι Z) (a : ZMod 3) : (Z × Z) × (ι → Z) :=
  (cellVal cl g a,
    fun Q => if Q = cl a ∨ Q = cl (a + 1) then 0
      else (g (a + 1) (Equiv.swap (cl (a + 1)) (cl (a + 2)) Q)).1 + (g (a + 2) Q).2)

/-! ### Cyclic arithmetic in `ZMod 3` -/

theorem zmod3_add_one_add_one (a : ZMod 3) : a + 1 + 1 = a + 2 := by ring

theorem zmod3_add_one_add_two (a : ZMod 3) : a + 1 + 2 = a := by
  have h : a + 1 + 2 = a + 3 := by ring
  rw [h, show (3 : ZMod 3) = 0 by decide +kernel, add_zero]

theorem zmod3_add_two_add_one (a : ZMod 3) : a + 2 + 1 = a := by
  have h : a + 2 + 1 = a + 3 := by ring
  rw [h, show (3 : ZMod 3) = 0 by decide +kernel, add_zero]

theorem zmod3_add_two_add_two (a : ZMod 3) : a + 2 + 2 = a + 1 := by
  have h : a + 2 + 2 = a + 1 + 3 := by ring
  rw [h, show (3 : ZMod 3) = 0 by decide +kernel, add_zero]

theorem zmod3_ne_add_one (a : ZMod 3) : a ≠ a + 1 := by revert a; decide
theorem zmod3_ne_add_two (a : ZMod 3) : a ≠ a + 2 := by revert a; decide
theorem zmod3_add_one_ne_add_two (a : ZMod 3) : a + 1 ≠ a + 2 := by revert a; decide

/-! ### The face injectivity -/

/-- **Face injectivity.**  Two cell triangles of the same cluster triple that agree at the two
positions `a`, `a+1` and have the same block indices there agree at the third position too. -/
theorem blockIdx_face_inj (hcl : Function.Injective cl) (a : ZMod 3)
    (g g' : ZMod 3 → CellH ι Z)
    (h0 : g a = g' a) (h1 : g (a + 1) = g' (a + 1))
    (hb0 : blockIdx cl g a = blockIdx cl g' a)
    (hb1 : blockIdx cl g (a + 1) = blockIdx cl g' (a + 1)) :
    g (a + 2) = g' (a + 2) := by
  have hne : ∀ b c : ZMod 3, b ≠ c → cl b ≠ cl c := fun b c h hh => h (hcl hh)
  have e12 : a + 1 + 1 = a + 2 := zmod3_add_one_add_one a
  have e13 : a + 1 + 2 = a := zmod3_add_one_add_two a
  -- the first components
  have hv0 : cellVal cl g a = cellVal cl g' a := congrArg Prod.fst hb0
  have hv1 : cellVal cl g (a + 1) = cellVal cl g' (a + 1) := congrArg Prod.fst hb1
  rw [cellVal_eq, cellVal_eq, h1] at hv0
  rw [cellVal_eq, cellVal_eq, e12, e13, h0] at hv1
  have hQ1 : g (a + 2) (cl (a + 1)) = g' (a + 2) (cl (a + 1)) := add_left_cancel hv0
  have hQ0 : g (a + 2) (cl a) = g' (a + 2) (cl a) := add_right_cancel hv1
  -- the second components
  have hu0 : (blockIdx cl g a).2 = (blockIdx cl g' a).2 := congrArg Prod.snd hb0
  have hu1 : (blockIdx cl g (a + 1)).2 = (blockIdx cl g' (a + 1)).2 := congrArg Prod.snd hb1
  funext Q
  by_cases hQa : Q = cl a
  · rw [hQa]; exact hQ0
  by_cases hQa1 : Q = cl (a + 1)
  · rw [hQa1]; exact hQ1
  -- second components of `g (a+2) Q`, read off the block index at `a`
  have hsnd : (g (a + 2) Q).2 = (g' (a + 2) Q).2 := by
    have hc := congrFun hu0 Q
    simp only [blockIdx, if_neg (by tauto : ¬ (Q = cl a ∨ Q = cl (a + 1))), h1] at hc
    exact add_left_cancel hc
  -- first components of `g (a+2) Q`, read off the block index at `a+1`
  have hfst : (g (a + 2) Q).1 = (g' (a + 2) Q).1 := by
    set Q' := Equiv.swap (cl (a + 2)) (cl a) Q with hQ'def
    have hback : Equiv.swap (cl (a + 2)) (cl a) Q' = Q := by
      rw [hQ'def, Equiv.swap_apply_self]
    have hnot : ¬ (Q' = cl (a + 1) ∨ Q' = cl (a + 2)) := by
      by_cases hQ2 : Q = cl (a + 2)
      · have : Q' = cl a := by rw [hQ'def, hQ2, Equiv.swap_apply_left]
        rw [this]
        exact not_or_intro (hne a (a + 1) (zmod3_ne_add_one a))
          (hne a (a + 2) (zmod3_ne_add_two a))
      · have : Q' = Q := by
          rw [hQ'def]
          exact Equiv.swap_apply_of_ne_of_ne hQ2 hQa
        rw [this]
        exact not_or_intro hQa1 hQ2
    have hc := congrFun hu1 Q'
    simp only [blockIdx, e12, e13, h0, hback] at hc
    rw [if_neg hnot, if_neg hnot] at hc
    exact add_right_cancel hc
  exact Prod.ext hfst hsnd

end Design

/-! ### The cell-count obstruction

The design above is exact and lossless inside one cluster triple, but its cell index is a *product*
over the partner clusters: a cluster has `|Z| ^ (2·#ι)` cells, and at least `|Z| ^ (2·(k-1))` of
them are needed if `k-1` partners are active (one independent coordinate per partner is exactly
what makes the three ownership rules of a triple independent).  The residual, on the other hand,
asks for blocks of relative size at least `α ≥ ε₁/8` inside their cluster, and each cell holds at
least one block, so a cluster has at most `1/α ≤ 8/ε₁` cells.  With `k ≥ 4/ε₁` clusters the two
requirements are incompatible. -/

/-- **A cluster has at most `1/α` cells.**  Pairwise disjoint cells inside a cluster, each holding
a block of relative size at least `α`, number at most `1/α`. -/
theorem card_cells_le_inv_alpha {V : Type*} [DecidableEq V] {S : Finset V} {α : ℝ} (hα : 0 < α)
    {n : ℕ} (cell : Fin n → Finset V) (hsub : ∀ i, cell i ⊆ S)
    (hdisj : ∀ i j, i ≠ j → Disjoint (cell i) (cell j))
    (hsize : ∀ i, α * (#S : ℝ) ≤ (#(cell i) : ℝ)) (hS : 0 < #S) :
    (n : ℝ) ≤ 1 / α := by
  classical
  have hbi : #((univ : Finset (Fin n)).biUnion cell) = ∑ i : Fin n, #(cell i) :=
    Finset.card_biUnion (fun i _ j _ hij => hdisj i j hij)
  have hle : ∑ i : Fin n, (#(cell i) : ℝ) ≤ (#S : ℝ) := by
    have hsub' : (univ : Finset (Fin n)).biUnion cell ⊆ S := by
      intro v hv
      obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp hv
      exact hsub i hi
    have := Finset.card_le_card hsub'
    rw [hbi] at this
    exact_mod_cast this
  have hlow : (n : ℝ) * (α * (#S : ℝ)) ≤ ∑ i : Fin n, (#(cell i) : ℝ) := by
    have := Finset.sum_le_sum (fun i (_ : i ∈ (univ : Finset (Fin n))) => hsize i)
    simpa [Finset.sum_const, Finset.card_univ, mul_comm] using this
  have hSpos : (0 : ℝ) < (#S : ℝ) := by exact_mod_cast hS
  have hn : (n : ℝ) * α ≤ 1 := by
    have h := le_trans hlow hle
    have : (n : ℝ) * α * (#S : ℝ) ≤ 1 * (#S : ℝ) := by ring_nf; ring_nf at h; linarith
    exact le_of_mul_le_mul_right this hSpos
  rw [le_div_iff₀ hα]
  linarith

private theorem two_mul_lt_four_pow (k : ℕ) (hk : 4 ≤ k) : 2 * k < 4 ^ (k - 1) := by
  induction k with
  | zero => omega
  | succ m ih =>
    rcases Nat.lt_or_ge m 4 with hm | hm
    · interval_cases m <;> simp_all <;> norm_num
    · have h := ih (by omega)
      have hstep : 4 ^ (m + 1 - 1) = 4 * 4 ^ (m - 1) := by
        have : m + 1 - 1 = (m - 1) + 1 := by omega
        rw [this, pow_succ]
        ring
      rw [hstep]
      omega

/-- **The product cell index is incompatible with the relative block size.**  A cluster with
`k - 1` active partners needs `M ^ (2·(k-1))` cells (`M = |Z| ≥ 2`), while blocks of relative size
`≥ α ≥ ε₁/8` allow at most `1/α` cells; with `k ≥ 4/ε₁` clusters this fails. -/
theorem productCell_count_infeasible {ε₁ α : ℝ} {k M : ℕ} (hε₁ : 0 < ε₁) (hε₁1 : ε₁ ≤ 1)
    (hα : ε₁ / 8 ≤ α) (hk : 4 / ε₁ ≤ (k : ℝ)) (hM : 2 ≤ M) :
    ¬ ((M ^ (2 * (k - 1)) : ℝ) ≤ 1 / α) := by
  intro hcon
  have hα0 : 0 < α := lt_of_lt_of_le (by positivity) hα
  -- `1/α ≤ 8/ε₁ ≤ 2k`
  have h8 : (1 : ℝ) / α ≤ 8 / ε₁ := by
    rw [div_le_div_iff₀ hα0 hε₁]
    linarith
  have hk4 : (4 : ℝ) ≤ (k : ℝ) := by
    have : (4 : ℝ) / ε₁ ≥ 4 := by
      rw [ge_iff_le, le_div_iff₀ hε₁]
      nlinarith
    linarith
  have hkN : 4 ≤ k := by exact_mod_cast hk4
  have h2k : (8 : ℝ) / ε₁ ≤ 2 * (k : ℝ) := by
    rw [div_le_iff₀ hε₁]
    have : (4 : ℝ) ≤ ε₁ * k := by
      rw [div_le_iff₀ hε₁] at hk
      linarith
    linarith
  -- but `M ^ (2(k-1)) ≥ 4 ^ (k-1) > 2k`
  have hpow : (4 : ℕ) ^ (k - 1) ≤ M ^ (2 * (k - 1)) := by
    have : (4 : ℕ) ^ (k - 1) = (2 ^ 2) ^ (k - 1) := by norm_num
    rw [this, ← pow_mul]
    exact Nat.pow_le_pow_left hM _
  have hlt : 2 * k < M ^ (2 * (k - 1)) := lt_of_lt_of_le (two_mul_lt_four_pow k hkN) hpow
  have hltR : (2 : ℝ) * (k : ℝ) < ((M ^ (2 * (k - 1)) : ℕ) : ℝ) := by exact_mod_cast hlt
  have hcast : ((M ^ (2 * (k - 1)) : ℕ) : ℝ) = (M : ℝ) ^ (2 * (k - 1)) := by push_cast; ring
  rw [hcast] at hltR
  linarith

end Nibble.AX1

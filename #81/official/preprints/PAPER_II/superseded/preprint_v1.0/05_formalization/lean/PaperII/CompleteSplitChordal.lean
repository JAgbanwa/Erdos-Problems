import PaperII.CompleteSplit
import PaperII.Chordal
import PaperII.Arith
import PaperII.IsChordalCopy

/-!
# Paper II — Chordal structure of the complete-split graph `S_{p,q}`

Helper lemmas assembling `chordalStructure_completeSplit` (in `L12`): the Dirac-family fields A1/A3
for `S_{p,q}`, proven directly (an independent-side vertex is simplicial; two of them are
nonadjacent). Plus two elementary integer floor bounds used by L12's main inequality.

The clique-tree / running-intersection machinery that formerly lived here (star of maximal cliques)
was removed together with A4: L7 is now clique-tree-free, so `chordalStructure_completeSplit` only
needs the two Dirac-family fields.
-/

open SimpleGraph

namespace PaperII

/-
Simplicial-hereditary field: every nonempty induced subgraph of `S_{p,q}` has a simplicial
vertex (an independent-side vertex if any, else any vertex of the induced clique).
-/
theorem completeSplit_simplicial_hereditary (p q : ℕ) (W : Set (Fin p ⊕ Fin q))
    (hW : W.Nonempty) : ∃ v : W, IsSimplicial ((completeSplit p q).induce W) v := by
  by_cases h : ∃ b : Fin q, Sum.inr b ∈ W;
  · obtain ⟨ b, hb ⟩ := h; use ⟨ Sum.inr b, hb ⟩ ; simp +decide [ IsSimplicial, Set.Pairwise ] ;
  · obtain ⟨ v, hv ⟩ := hW;
    rcases v with ( v | v ) <;> simp_all +decide [ IsSimplicial ];
    refine' ⟨ v, hv, _ ⟩;
    intro x hx y hy; aesop;

/-
`two_nonadj_simplicial` field: a connected noncomplete `S_{p,q}` (forcing `q ≥ 2`) has two
nonadjacent simplicial vertices, namely two distinct independent-side vertices.
-/
theorem completeSplit_two_nonadj_simplicial (p q : ℕ) :
    (completeSplit p q).Connected → (¬ ∀ u v : Fin p ⊕ Fin q, u ≠ v → (completeSplit p q).Adj u v) →
    ∃ x y : Fin p ⊕ Fin q, x ≠ y ∧ ¬ (completeSplit p q).Adj x y ∧
      IsSimplicial (completeSplit p q) x ∧ IsSimplicial (completeSplit p q) y := by
  -- From the hypothesis that the graph is connected and not complete, we can use the fact that there exist two vertices that are not adjacent.
  intro hConnected hNotComplete
  obtain ⟨u, v, huv_ne, huv_notAdj⟩ : ∃ u v : Fin p ⊕ Fin q, u ≠ v ∧ ¬(completeSplit p q).Adj u v := by
    grind;
  cases' u with u u <;> cases' v with v v <;> simp_all +decide [ IsSimplicial, Set.Pairwise ]

/-- The complete-split graph `S_{p,q}` is chordal in the standard sense (`IsChordal`). Any induced
cycle of length `≥ 4` must use `≥ 2` vertices of the clique side (the independent side is an
independent set, so at most alternating with clique vertices forces two clique vertices at distance 2
on the cycle); those two clique vertices are adjacent, giving a chord. Feeds the `isChordal` field of
`chordalStructure_completeSplit` and the attainment witness of the unconditional Theorem 1.2. -/
theorem isChordal_completeSplit (p q : ℕ) : IsChordal (completeSplit p q) := by
  intro v0 c hc hlen
  -- Every vertex on a cycle of length `≥ 4` has two cycle-neighbours `a,b` with `s(a,b) ∉ edges`
  -- (`cycle_two_neighbors`). Picking an independent-side (`inr`) vertex if the cycle has one — else
  -- any vertex of the all-clique cycle — forces `a,b` onto the clique side (`inl`), where distinct
  -- vertices are adjacent, so `s(a,b)` is the required chord.
  by_cases h : ∃ w ∈ c.support, ∃ w' : Fin q, w = Sum.inr w'
  · obtain ⟨w, hw, w', rfl⟩ := h
    obtain ⟨a, b, ha, hb, hab, hnab⟩ := cycle_two_neighbors c hc hlen hw
    have haadj := c.adj_of_mem_edges ha
    have hbadj := c.adj_of_mem_edges hb
    have nbhd : ∀ u : Fin p ⊕ Fin q, (completeSplit p q).Adj (Sum.inr w') u →
        ∃ i : Fin p, u = Sum.inl i := by
      intro u hu; cases u with
      | inl i => exact ⟨i, rfl⟩
      | inr j => exact absurd hu (completeSplit_inr_inr p q w' j)
    obtain ⟨ia, rfl⟩ := nbhd a haadj
    obtain ⟨ib, rfl⟩ := nbhd b hbadj
    refine ⟨Sum.inl ia, Sum.inl ib, c.snd_mem_support_of_mem_edges ha,
      c.snd_mem_support_of_mem_edges hb, ?_, hnab⟩
    rw [completeSplit_inl_inl]; exact fun he => hab (by rw [he])
  · push_neg at h
    obtain ⟨a, b, ha, hb, hab, hnab⟩ := cycle_two_neighbors c hc hlen c.start_mem_support
    have hasup := c.snd_mem_support_of_mem_edges ha
    have hbsup := c.snd_mem_support_of_mem_edges hb
    have nbhd : ∀ u : Fin p ⊕ Fin q, u ∈ c.support → ∃ i : Fin p, u = Sum.inl i := by
      intro u hu; cases u with
      | inl i => exact ⟨i, rfl⟩
      | inr j => exact absurd rfl (h _ hu j)
    obtain ⟨ia, rfl⟩ := nbhd a hasup
    obtain ⟨ib, rfl⟩ := nbhd b hbsup
    refine ⟨Sum.inl ia, Sum.inl ib, hasup, hbsup, ?_, hnab⟩
    rw [completeSplit_inl_inl]; exact fun he => hab (by rw [he])

/-
Integer floor bound, nonsaturated branch: `2·(C(p,2)+p·q) ≤ 6·⌊(2(p+q)+1)²/24⌋`.
Here `p·(p-1)+2p·q = 2·(C(p,2)+p·q)`.  Proof: with `N = 2(p+q)+1`, the identity
`N² = (p(p-1)+8pq)+ (4q²+8p+4q+1)` (see `nonsat_domination_identity`) and `p ≥ 3` give
`N² % 24 ≤ 23 < 8p+1 ≤ N² - 8·(C+pq)`, so `24·⌊N²/24⌋ ≥ 8·(C+pq)`.
-/
theorem nonsat_le_floor_int (p q : ℤ) (hp : 3 ≤ p) (hq : 0 ≤ q) :
    p * (p - 1) + 2 * (p * q) ≤ 6 * ((2 * (p + q) + 1) ^ 2 / 24) := by
  nlinarith [ Int.mul_ediv_add_emod ( ( 2 * ( p + q ) + 1 ) ^ 2 ) 24, Int.emod_nonneg ( ( 2 * ( p + q ) + 1 ) ^ 2 ) ( by norm_num : ( 24 : ℤ ) ≠ 0 ), Int.emod_lt_of_pos ( ( 2 * ( p + q ) + 1 ) ^ 2 ) ( by norm_num : ( 24 : ℤ ) > 0 ) ]

/-
Integer floor bound, degenerate branch `p ≤ 1` (`C(p,2)=0`, edges `= p·q`):
`p·q ≤ ⌊(2(p+q)+1)²/24⌋`.  Since `p ≤ 1`, `p·q ≤ q` and `24q ≤ (2q+3)² = (2(p+q)+1)²`
when `p ≤ 1` via `(2q-3)² ≥ 0`.
-/
theorem deg_le_floor_int (p q : ℤ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq : 0 ≤ q) :
    p * q ≤ (2 * (p + q) + 1) ^ 2 / 24 := by
  rw [ Int.le_ediv_iff_mul_le ] <;
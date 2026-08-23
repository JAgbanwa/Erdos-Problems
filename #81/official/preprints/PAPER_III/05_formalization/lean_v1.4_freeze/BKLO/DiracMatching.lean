/-
# Dirac's theorem for perfect matchings.

This file discharges the third external input of `BKLO/Inputs.lean`, `PerfectMatchingDirac`:
every graph on an even number of vertices with `|V| ≤ 2·δ(G)` has a perfect matching.

The proof goes through Tutte's theorem (`SimpleGraph.tutte`, in Mathlib): it suffices to check
that no set `u ⊆ V` is a Tutte violator, i.e. that after deleting `u` the number `k` of odd
components is at most `|u| = s`.

* Every connected component `C` of `G - u` satisfies `δ + 1 ≤ |C| + s`: a vertex `v ∈ C` has all
  of its `≥ δ` neighbours inside `C ∪ u`.
* Hence `k · (δ + 1 - s) ≤ |V| - s` (the components are pairwise disjoint), and also `k ≤ |V| - s`.
* Parity (`SimpleGraph.odd_ncard_oddComponents`) gives `k ≡ |V| - s ≡ s (mod 2)` since `|V|` is
  even, so `s < k` would force `s + 2 ≤ k`, which contradicts the two counting bounds.
-/
import BKLO.Inputs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Combinatorics.SimpleGraph.Tutte
import Mathlib.Data.Int.Star

open Finset

namespace BKLO

/-- If every connected component of a finite graph `H` has at least `m` vertices, then any set `S`
of components satisfies `|S| · m ≤ |W|`. -/
theorem ncard_mul_le_card_of_le_ncard_supp {W : Type*} [Finite W] (H : SimpleGraph W) (m : ℕ)
    (hm : ∀ c : H.ConnectedComponent, m ≤ c.supp.ncard)
    (S : Set H.ConnectedComponent) : S.ncard * m ≤ Nat.card W := by
  classical
  cases nonempty_fintype W
  have : Fintype H.ConnectedComponent := Fintype.ofFinite _
  have hdisj : ∀ x ∈ S.toFinset, ∀ y ∈ S.toFinset, x ≠ y →
      Disjoint x.supp.toFinset y.supp.toFinset := fun x _ y _ hxy =>
    Set.disjoint_toFinset.2 (H.pairwise_disjoint_supp_connectedComponent hxy)
  have key : ∑ c ∈ S.toFinset, c.supp.toFinset.card ≤ Fintype.card W := by
    rw [← Finset.card_biUnion hdisj]
    exact Finset.card_le_univ _
  have h2 : S.toFinset.card * m ≤ ∑ c ∈ S.toFinset, c.supp.toFinset.card := by
    rw [← smul_eq_mul]
    refine Finset.card_nsmul_le_sum _ _ _ fun c _ => ?_
    rw [← Set.ncard_eq_toFinset_card']
    exact hm c
  rw [Set.ncard_eq_toFinset_card', Nat.card_eq_fintype_card]
  omega

/-- Every component of `G - u` has at least `δ(G) + 1 - |u|` vertices: a vertex of the component
has all its neighbours inside the component together with `u`. -/
theorem minDegree_succ_le_ncard_supp_add_ncard {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : Set V)
    (c : (((⊤ : G.Subgraph).deleteVerts u).coe).ConnectedComponent) :
    G.minDegree + 1 ≤ c.supp.ncard + u.ncard := by
  classical
  obtain ⟨v, hv⟩ := c.nonempty_supp
  have hsub : insert (v : V) (G.neighborSet v) ⊆ (Subtype.val '' c.supp) ∪ u := by
    intro w hw
    rcases hw with rfl | hw
    · exact Or.inl ⟨v, hv, rfl⟩
    · by_cases hwu : w ∈ u
      · exact Or.inr hwu
      · refine Or.inl ⟨⟨w, ?_⟩, ?_, rfl⟩
        · simp [hwu]
        · refine c.mem_supp_of_adj_mem_supp hv ?_
          simp only [SimpleGraph.Subgraph.coe_adj]
          simp only [SimpleGraph.Subgraph.deleteVerts_adj, hwu, SimpleGraph.Subgraph.verts_top,
            Set.mem_univ, true_and, SimpleGraph.Subgraph.top_adj, not_false_eq_true]
          exact ⟨v.2.2, hw⟩
  have hcard1 : (insert (v : V) (G.neighborSet v)).ncard = G.degree v + 1 := by
    rw [Set.ncard_insert_of_notMem (by simp)]
    congr 1
    rw [← SimpleGraph.coe_neighborFinset, Set.ncard_coe_finset,
      SimpleGraph.card_neighborFinset_eq_degree]
  have hcard2 : ((Subtype.val '' c.supp) ∪ u).ncard ≤ c.supp.ncard + u.ncard := by
    refine le_trans (Set.ncard_union_le _ _) ?_
    gcongr
    exact le_of_eq (Set.ncard_image_of_injective _ Subtype.val_injective)
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  have hmd := G.minDegree_le_degree (v : V)
  omega

/-- **Dirac's theorem for perfect matchings.**  A graph on an even number of vertices whose
minimum degree is at least `|V| / 2` has a perfect matching.  This discharges the third external
input `BKLO.PerfectMatchingDirac`. -/
theorem perfectMatchingDirac_holds : PerfectMatchingDirac := by
  intro V _ _ G _ hEven hdeg
  classical
  rw [SimpleGraph.tutte]
  intro u hviol
  set n := Fintype.card V with hn
  set s := u.ncard with hs
  set H := (((⊤ : G.Subgraph).deleteVerts u).coe) with hH
  rw [SimpleGraph.IsTutteViolator, ← hH, ← hs] at hviol
  set k := H.oddComponents.ncard with hk
  -- the vertex set of `G - u` has `n - s` elements
  have hverts : ((⊤ : G.Subgraph).deleteVerts u).verts = Set.univ \ u := by
    simp [SimpleGraph.Subgraph.deleteVerts]
  have hsn : s ≤ n := by
    have := Set.ncard_le_ncard (Set.subset_univ u) (Set.finite_univ (α := V))
    rwa [Set.ncard_univ, Nat.card_eq_fintype_card] at this
  have hW : Nat.card ↥(((⊤ : G.Subgraph).deleteVerts u).verts) = n - s := by
    rw [hverts, Nat.card_coe_set_eq, Set.ncard_diff (Set.subset_univ u), Set.ncard_univ,
      Nat.card_eq_fintype_card]
  -- every component is nonempty, so `k ≤ n - s`
  have h1 : k * 1 ≤ n - s := by
    rw [← hW]
    refine ncard_mul_le_card_of_le_ncard_supp H 1 (fun c => ?_) _
    exact (Set.ncard_pos (Set.toFinite _)).2 c.nonempty_supp
  -- parity: `k ≡ n - s (mod 2)`
  have hpar : Odd k ↔ Odd (n - s) := by
    rw [hk, hH, SimpleGraph.odd_ncard_oddComponents, hW]
  rw [Nat.odd_iff, Nat.odd_iff] at hpar
  obtain ⟨a, ha⟩ := hEven
  by_cases hcase : n ≤ 2 * s
  · omega
  · push_neg at hcase
    -- `s < δ`, and every component has at least `δ + 1 - s` vertices
    have hsd : s < G.minDegree := by omega
    have h2 : k * (G.minDegree + 1 - s) ≤ n - s := by
      rw [← hW]
      refine ncard_mul_le_card_of_le_ncard_supp H _ (fun c => ?_) _
      have := minDegree_succ_le_ncard_supp_add_ncard G u c
      omega
    -- parity forces `s + 2 ≤ k`
    have hk2 : s + 2 ≤ k := by omega
    obtain ⟨t, ht⟩ : ∃ t, G.minDegree = s + t := ⟨G.minDegree - s, by omega⟩
    have hmul : (s + 2) * (t + 1) ≤ k * (G.minDegree + 1 - s) :=
      Nat.mul_le_mul hk2 (by omega)
    have hexp : (s + 2) * (t + 1) = s * t + s + 2 * t + 2 := by ring
    have hns : n - s ≤ s + 2 * t := by omega
    have hchain : s * t + s + 2 * t + 2 ≤ s + 2 * t :=
      calc s * t + s + 2 * t + 2 = (s + 2) * (t + 1) := hexp.symm
        _ ≤ k * (G.minDegree + 1 - s) := hmul
        _ ≤ n - s := h2
        _ ≤ s + 2 * t := hns
    linarith [Nat.zero_le (s * t)]

end BKLO

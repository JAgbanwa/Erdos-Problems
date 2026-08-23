/-
  Part B (Phase 2) — residual graph + residual divisibility (support for the absorption method).

  The absorber-reservation interface is now routed through the transformer-bank target in
  `TransformerAbsorberTry`, not through the dead-end FLEX-unit route in `AbsorberBuild`. This
  file now provides only the shared support lemmas that route depends on:
  * `residual G A`            — the graph after deleting an absorber `A`'s covered edges;
  * AB-5 `residual_divisible` — removing an edge-disjoint family of triangles from a
    triangle-divisible graph keeps it triangle-divisible (local parity/counting), sorry-free.

  (The earlier non-flex `build_absorber` / `reserve_core` / `reserve_absorber_proof` scaffolding
  was superseded by the flex route and removed.)
-/
import Ax2.PartB.BKLO.Defs

namespace Ax2.BKLO

open SimpleGraph Finset Ax2

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The residual graph after removing an absorber's edges. -/
noncomputable def residual (G : SimpleGraph V) (A : Finset (Finset V)) : SimpleGraph V :=
  G.deleteEdges (↑(coveredEdges A))

noncomputable instance instDecidableResidualAdj (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset (Finset V)) : DecidableRel (residual G A).Adj := Classical.decRel _

/-- **AB-5 (residual divisibility).** Removing an edge-disjoint family of triangles from a
triangle-divisible graph leaves it triangle-divisible: `3 ∣ e` is preserved (each triangle
removes 3 edges) and every degree stays even (each triangle removes 2 edges at each of its
vertices). -/
theorem residual_divisible (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdiv : TriangleDivisible G) {A : Finset (Finset V)} (hA : ∀ t ∈ A, G.IsNClique 3 t)
    (hAd : EdgeDisjoint A) : TriangleDivisible (residual G A) := by
  obtain ⟨hdiv_edge, hdiv_deg⟩ := hdiv
  -- Note: residual G A = G.deleteEdges (coveredEdges A)
  -- We need to establish: (residual G A).edgeFinset = G.edgeFinset \ coveredEdges A
  have h_edgeFinset : (residual G A).edgeFinset = G.edgeFinset \ coveredEdges A := by
    unfold residual
    rw [SimpleGraph.edgeFinset_deleteEdges]
  refine ⟨?_, ?_⟩
  · -- Show 3 ∣ #(residual G A).edgeFinset
    rw [h_edgeFinset]
    -- Need: coveredEdges A ⊆ G.edgeFinset and 3 ∣ #coveredEdges A
    have h_subset : coveredEdges A ⊆ G.edgeFinset := by
      intro e he
      simp only [coveredEdges, Finset.mem_biUnion] at he
      obtain ⟨t, ht, he⟩ := he
      unfold triEdges at he
      rw [Finset.mem_filter] at he
      simp only [SimpleGraph.mem_edgeFinset]
      have ht3 := hA t ht
      obtain ⟨he_mem, he_not_diag⟩ := he
      rw [Finset.mem_sym2_iff] at he_mem
      -- e = {u, v} for some u, v ∈ t with u ≠ v
      -- Need to show e ∈ G.edgeSet using ht3 (t is a clique)
      cases e with
      | h =>
        rename_i u v
        -- u and v are both in s(u, v), so they're in t
        -- he_not_diag means u ≠ v
        -- ht3 says t is a clique, so G.Adj u v
        have hx : u ∈ t := he_mem u (by simp)
        have hy : v ∈ t := he_mem v (by simp)
        rw [SimpleGraph.mem_edgeSet]
        -- he_not_diag : ¬s(u, v).IsDiag means u ≠ v
        have huv_ne : u ≠ v := by
          intro rfl
          exact he_not_diag (by simp [Sym2.IsDiag])
        exact ht3.isClique (x := u) hx (y := v) hy huv_ne
    have h_card_covered : 3 ∣ (coveredEdges A).card := by
      -- coveredEdges A = A.biUnion triEdges
      -- Each triangle has 3 edges, and they're edge-disjoint
      -- So #coveredEdges A = 3 * #A
      rw [coveredEdges, Finset.card_biUnion]
      · -- Each triEdges t has card 3
        have h_tri_card : ∀ t ∈ A, (triEdges t).card = 3 := by
          intro t ht
          have ht3 := hA t ht
          -- t has exactly 3 elements
          have ht_card : t.card = 3 := ht3.card_eq
          -- triEdges t = t.sym2.filter (¬ IsDiag)
          unfold triEdges
          -- t.sym2 has 6 elements, diag has 3, so filter (¬ IsDiag) has 3
          rw [Finset.filter_not]
          rw [Finset.card_sdiff]
          · -- #t.sym2 = 6
            have h1 : t.sym2.card = (t.card + 1).choose 2 := Finset.card_sym2 t
            -- #(filter Sym2.IsDiag t.sym2) = 3
            have h2 : (Finset.filter Sym2.IsDiag t.sym2).card = t.card := by
              -- Use that (filter IsDiag t.sym2) = image (fun a => s(a,a)) t
              have heq : Finset.filter Sym2.IsDiag t.sym2 = t.image (fun a => Sym2.mk (a, a)) := by
                ext e
                simp only [Finset.mem_filter, Finset.mem_image]
                constructor <;> intro h
                · cases e with
                  | h =>
                    rename_i u v
                    cases h with
                    | intro he_sym2 he_diag =>
                      -- s(u, v).IsDiag means u = v
                      -- s(u, v) ∈ t.sym2 means u ∈ t
                      use u
                      refine ⟨?_, ?_⟩
                      · -- u ∈ t from s(u, v) ∈ t.sym2
                        simp only [Finset.mem_sym2_iff] at he_sym2
                        exact he_sym2 u (by simp)
                      · -- s(u, u) = s(u, v) from s(u, v).IsDiag
                        -- s(u, v).IsDiag means u = v
                        have : u = v := by
                          cases he_diag
                          rfl
                        rw [this]
                · obtain ⟨a, ha, he_eq⟩ := h
                  -- e = s(a, a) with a ∈ t
                  -- So e ∈ t.sym2 and e.IsDiag
                  refine ⟨?_, ?_⟩ <;> rw [← he_eq]
                  · simp [Finset.mem_sym2_iff, ha]
                  · simp [Sym2.IsDiag]
              rw [heq, Finset.card_image_of_injective]
              intro a b hab
              rw [Sym2.mk_eq_mk_iff] at hab
              rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
            have h3 : Finset.filter Sym2.IsDiag t.sym2 ∩ t.sym2 = Finset.filter Sym2.IsDiag t.sym2 := by
              rw [Finset.inter_eq_left]
              exact Finset.filter_subset _ _
            rw [ht_card] at h1 h2
            rw [h1, h3, h2]
            decide
        rw [Finset.sum_congr rfl h_tri_card]
        simp
      · -- Edge disjoint
        intro t₁ ht₁ t₂ ht₂ hne
        exact hAd t₁ ht₁ t₂ ht₂ hne
    have h_card_residual : #(G.edgeFinset \ coveredEdges A) = #G.edgeFinset - #(coveredEdges A) := by
      simp [Finset.card_sdiff, Finset.inter_eq_left.mpr h_subset]
    rw [h_card_residual]
    omega
  · -- Show all degrees are even
    intro v
    open Classical in
    -- degree v = #(G.adj v)
    -- For residual G A = G.deleteEdges (coveredEdges A):
    have h_adj : ∀ u, (residual G A).Adj u v ↔ G.Adj u v ∧ (Sym2.mk (u, v)) ∉ coveredEdges A := by
      intro u
      unfold residual
      simp [deleteEdges]
      by_cases huv : u = v <;> simp [huv]
    -- degree v = #(adj v)
    -- (resual G A).adj v = G.adj v \ {u | G.Adj u v ∧ s(u, v) ∈ coveredEdges A}
    -- Define the finset of vertices whose edge to v is in coveredEdges A
    let removedAdjFinset : Finset V :=
      Finset.filter (fun u : V => (Sym2.mk (u, v)) ∈ coveredEdges A) ((G.neighborSet v).toFinset)
    have h_adj_eq : (residual G A).neighborSet v = G.neighborSet v \ removedAdjFinset := by
      ext u
      simp [removedAdjFinset]
      have := h_adj u
      rw [SimpleGraph.adj_comm] at this
      simp_all [SimpleGraph.adj_comm]
    -- (residual G A).degree v = #(G.neighborSet v \ removedAdjFinset)
    have h_deg_eq : (residual G A).degree v = G.degree v - #removedAdjFinset := by
      have h1 : (residual G A).degree v = #(SimpleGraph.neighborFinset (residual G A) v) := rfl
      have h2 : G.degree v = #(SimpleGraph.neighborFinset G v) := rfl
      have h_adj_eq' : (residual G A).neighborFinset v = G.neighborFinset v \ removedAdjFinset := by
        ext u
        simp [removedAdjFinset]
        have := h_adj u
        rw [SimpleGraph.adj_comm] at this
        simp_all [SimpleGraph.adj_comm]
      rw [h1, h2, h_adj_eq']
      have h_sub : removedAdjFinset ⊆ G.neighborFinset v := Finset.filter_subset _ _
      simp [Finset.card_sdiff, Finset.inter_eq_left.mpr h_sub]
    -- Now show that #removedAdjFinset is even
    -- Each triangle through v contributes exactly 2 neighbors whose edge is in coveredEdges A
    have h_removed_even : Even #removedAdjFinset := by
      -- removedAdjFinset = biUnion over triangles through v of the two other vertices
      -- First, let's express removedAdjFinset as a biUnion
      let trianglesThroughV := A.filter (fun t => v ∈ t)
      have h_removed_eq : removedAdjFinset = trianglesThroughV.biUnion (fun t => t \ {v}) := by
        ext u
        simp only [removedAdjFinset, trianglesThroughV, Finset.mem_filter, Finset.mem_biUnion,
          Finset.mem_sdiff, Finset.mem_singleton]
        constructor
        · intro ⟨hu_adj, hu_covered⟩
          simp only [coveredEdges, Finset.mem_biUnion] at hu_covered
          obtain ⟨t, ht, hte⟩ := hu_covered
          unfold triEdges at hte
          rw [Finset.mem_filter] at hte
          obtain ⟨he_sym2, he_not_diag⟩ := hte
          rw [Finset.mem_sym2_iff] at he_sym2
          have huv_ne : u ≠ v := by
            intro rfl
            simp [Sym2.IsDiag] at he_not_diag
          refine ⟨t, ⟨ht, ?_⟩, ?_⟩
          · exact he_sym2 v (by simp)
          · exact ⟨he_sym2 u (by simp), huv_ne⟩
        · intro ⟨t, ⟨ht, hv_in_t⟩, hu_in_t, hu_ne_v⟩
          have h_adj_uv : G.Adj u v := (hA t ht).isClique hu_in_t hv_in_t hu_ne_v
          refine ⟨?_, ?_⟩
          · -- u ∈ (G.neighborSet v).toFinset
            have heq : (G.neighborSet v).toFinset = G.neighborFinset v := rfl
            rw [heq]
            simp [SimpleGraph.mem_neighborFinset]
            exact h_adj_uv.symm
          · -- s(u, v) ∈ coveredEdges A
            simp only [coveredEdges, Finset.mem_biUnion]
            refine ⟨t, ht, ?_⟩
            unfold triEdges
            rw [Finset.mem_filter]
            refine ⟨?_, ?_⟩
            · rw [Finset.mem_sym2_iff]
              intro a ha
              simp only [Sym2.mem_iff] at ha
              rcases ha with rfl | rfl <;> assumption
            · simp [Sym2.IsDiag, hu_ne_v]
      -- Now use that #removedAdjFinset = 2 * #trianglesThroughV
      rw [h_removed_eq]
      -- Each triangle t with v ∈ t contributes |t \ {v}| = 2 elements
      -- The triangles are edge-disjoint, so the pairs are disjoint
      rw [Finset.card_biUnion]
      · -- Each t \ {v} has cardinality 2
        have h_each : ∀ t ∈ trianglesThroughV, (t \ {v}).card = 2 := by
          intro t ht
          simp only [trianglesThroughV, Finset.mem_filter] at ht
          have ht3 := (hA t ht.1).card_eq
          have hv_in : v ∈ t := ht.2
          simp [Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.singleton_subset_iff.mpr hv_in), ht3]
        rw [Finset.sum_congr rfl h_each]
        simp
      · -- The sets t \ {v} are pairwise disjoint
        intro t₁ ht₁ t₂ ht₂ hne
        simp [trianglesThroughV] at ht₁ ht₂
        -- If u ∈ t₁ \ {v} ∩ t₂ \ {v}, then s(u, v) ∈ triEdges t₁ and s(u, v) ∈ triEdges t₂
        rw [Function.onFun, Finset.disjoint_left]
        intro u hu
        simp only [Finset.mem_sdiff, Finset.mem_singleton] at hu ⊢
        have hu_t1 : u ∈ t₁ := hu.1
        have hu_ne_v : u ≠ v := hu.2
        -- If u ∈ t₂ \ {v}, derive contradiction via edge-disjointness
        intro ⟨hu_t2, hu_ne_v2⟩
        have h_mem1 : (Sym2.mk (u, v)) ∈ triEdges t₁ := by
          unfold triEdges
          rw [Finset.mem_filter]
          refine ⟨?_, ?_⟩
          · rw [Finset.mem_sym2_iff]
            intro x hx
            simp only [Sym2.mem_iff] at hx
            rcases hx with rfl | rfl <;> [exact hu_t1; exact ht₁.2]
          · simp [Sym2.IsDiag, hu_ne_v]
        have h_mem2 : (Sym2.mk (u, v)) ∈ triEdges t₂ := by
          unfold triEdges
          rw [Finset.mem_filter]
          refine ⟨?_, ?_⟩
          · rw [Finset.mem_sym2_iff]
            intro x hx
            simp only [Sym2.mem_iff] at hx
            rcases hx with rfl | rfl <;> [exact hu_t2; exact ht₂.2]
          · simp [Sym2.IsDiag, hu_ne_v2]
        exact Finset.disjoint_left.mp (hAd t₁ ht₁.1 t₂ ht₂.1 hne) h_mem1 h_mem2
    rw [h_deg_eq]
    have h_card_le : #removedAdjFinset ≤ G.degree v := by
      have h_sub : removedAdjFinset ⊆ G.neighborFinset v := Finset.filter_subset _ _
      have h_eq : G.degree v = #(G.neighborFinset v) := rfl
      rw [h_eq]
      exact Finset.card_le_card h_sub
    rw [Nat.even_sub h_card_le]
    exact iff_of_true (hdiv_deg v) h_removed_even

end Ax2.BKLO

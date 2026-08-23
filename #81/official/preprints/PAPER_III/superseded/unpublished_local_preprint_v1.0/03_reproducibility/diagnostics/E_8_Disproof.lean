/-
# Paper III — §8: the *very sparse* packing estimate is FALSE as stated

This file records a machine-checked refutation of `E_8_very_sparse_packing_estimate`
(in `PaperIII/E_8.lean`).  That lemma claims, for every `k`, a threshold `n₀` beyond
which every split graph `G` with `10q < p` and the degree bound satisfies

    (edgeCount(G) − n²/6) / 2  ≤  ν₃(G).

Taking `q = 0` (the degree hypothesis is then vacuous, `Fin 0` being empty) with an
**even** clique size `p`, the graph is `K_p`.  A parity/double-counting argument shows
that in `K_p` every vertex has odd degree `p − 1`, so at least one edge at each vertex is
left uncovered by any edge-disjoint triangle family; hence

    ν₃(K_p) ≤ p(p − 2)/6,   while   (edgeCount − n²/6)/2 = p(p−2)/6 + p/12.

So the target exceeds `ν₃` by exactly `p/12 > 0` for arbitrarily large even `p`, refuting
the `∃ n₀, ∀ G …` statement.  (The paper's genuine E-8 carries an additive `O(n)` slack,
or reads `ν₃` as the *fractional* optimum `ν₃*`; the strict integral form here is false.)
-/
import PaperIII.E_8

namespace PaperIII

open SplitGraph Finset SimpleGraph

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- In an edge-disjoint triangle packing, the two non-`v` vertices of each triangle
through `v` are distinct neighbours of `v`, and edge-disjointness makes these pairs
disjoint; hence at most `⌊deg v / 2⌋` triangles pass through `v`. -/
lemma card_triangles_at_le_degree (H : SimpleGraph W) [DecidableRel H.Adj]
    {T : Finset (Finset W)} (hT : IsTrianglePacking H T) (v : W) :
    2 * (T.filter (fun t => v ∈ t)).card ≤ H.degree v := by
  -- We'll show that 2*(triangles through v) ≤ degree v
  -- by constructing an injection from pairs (triangle, position in triangle) to neighbors
  have hpk := hT.1
  have hpai := hT.2
  let filteredT := T.filter (fun t => v ∈ t)
  -- The union of (t \ {v}) over all t in filteredT
  let S := filteredT.biUnion (fun t => t \ {v})
  -- We'll show S.card = 2 * filteredT.card and S ⊆ H.neighborFinset v
  -- First: the sets (t \ {v}) are pairwise disjoint
  have hdisj : (∀ t₁ ∈ filteredT, ∀ t₂ ∈ filteredT, t₁ ≠ t₂ → Disjoint (t₁ \ {v}) (t₂ \ {v})) := by
    intro t₁ ht₁ t₂ ht₂ hne
    rw [Finset.disjoint_iff_ne]
    intro a ha b hb hab
    have ha1 : a ∈ t₁ := Finset.mem_sdiff.mp ha |>.1
    have ha2 : a ≠ v := by
      simp only [Finset.mem_sdiff, Finset.mem_singleton] at ha
      exact ha.2
    have hb1 : b ∈ t₂ := Finset.mem_sdiff.mp hb |>.1
    have hb2 : b ≠ v := by
      simp only [Finset.mem_sdiff, Finset.mem_singleton] at hb
      exact hb.2
    -- t₁ and t₂ both contain v, so v ∈ t₁ ∩ t₂
    have hv1 : v ∈ t₁ := Finset.mem_filter.mp ht₁ |>.2
    have hv2 : v ∈ t₂ := Finset.mem_filter.mp ht₂ |>.2
    -- If a = b, then t₁ ∩ t₂ contains at least v and a
    -- But hpai says |t₁ ∩ t₂| ≤ 1, contradiction
    exfalso
    have hint : v ∈ t₁ ∩ t₂ := Finset.mem_inter.mpr ⟨hv1, hv2⟩
    have haT : a ∈ t₁ ∩ t₂ := Finset.mem_inter.mpr ⟨ha1, by rw [hab]; exact hb1⟩
    -- But |t₁ ∩ t₂| ≤ 1
    have ht1T : t₁ ∈ T := Finset.mem_filter.mp ht₁ |>.1
    have ht2T : t₂ ∈ T := Finset.mem_filter.mp ht₂ |>.1
    have hcard := hpai ht1T ht2T hne
    -- We have two distinct elements in t₁ ∩ t₂, so |t₁ ∩ t₂| ≥ 2
    have h_card_ge : ({v, a} : Finset W) ⊆ t₁ ∩ t₂ := by
      intro x hx
      simp at hx
      cases hx with
      | inl h => rw [h]; exact hint
      | inr h => rw [h]; exact haT
    have h_two : ({v, a} : Finset W).card = 2 := by
      rw [Finset.card_pair ha2.symm]
    have h_ge : 2 ≤ (t₁ ∩ t₂).card := h_two ▸ Finset.card_le_card h_card_ge
    linarith
  -- Now show S has cardinality 2 * filteredT.card (since sets are disjoint and each has size 2)
  have hS_card : S.card = 2 * filteredT.card := by
    -- Each (t \ {v}) has size 2 since t is a 3-clique with v
    have hsizes : ∀ t ∈ filteredT, (t \ {v}).card = 2 := by
      intro t ht
      have htT : t ∈ T := Finset.mem_filter.mp ht |>.1
      have hv : v ∈ t := Finset.mem_filter.mp ht |>.2
      have hcard3 : t.card = 3 := (hpk t htT).card_eq
      rw [Finset.card_sdiff]
      simp only [hcard3]
      have hvt : {v} ∩ t = {v} := by simp [hv]
      simp [hvt]
    rw [Finset.card_biUnion]
    · rw [Finset.sum_congr rfl hsizes]
      simp [mul_comm]
    · exact fun t₁ ht₁ t₂ ht₂ hne => hdisj t₁ ht₁ t₂ ht₂ hne
  -- Now show S ⊆ H.neighborFinset v
  have hS_sub : S ⊆ H.neighborFinset v := by
    intro x hx
    rw [Finset.mem_biUnion] at hx
    obtain ⟨t, ht, hxt⟩ := hx
    simp only [Finset.mem_sdiff, Finset.mem_singleton] at hxt
    have htT : t ∈ T := Finset.mem_filter.mp ht |>.1
    have hv : v ∈ t := Finset.mem_filter.mp ht |>.2
    have hclique := hpk t htT
    rw [SimpleGraph.mem_neighborFinset]
    simp only [SimpleGraph.isNClique_iff] at hclique
    have hne : v ≠ x := fun h => hxt.2 (h.symm)
    exact hclique.1 hv hxt.1 hne
  -- Conclude
  calc 2 * #filteredT = S.card := hS_card.symm
    _ ≤ (H.neighborFinset v).card := Finset.card_le_card hS_sub
    _ = H.degree v := rfl

/-- Double counting: summing "triangles through `v`" over all `v` counts each triangle
three times. -/
lemma sum_card_triangles_at (H : SimpleGraph W) [DecidableRel H.Adj]
    (T : Finset (Finset W)) (hT : ∀ t ∈ T, H.IsNClique 3 t) :
    ∑ v : W, (T.filter (fun t => v ∈ t)).card = 3 * T.card := by
  simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  have hrhs : (3 : ℕ) * ∑ x ∈ T, (1 : ℕ) = ∑ x ∈ T, (3 : ℕ) := by
    simp [mul_comm]
  rw [hrhs]
  apply Finset.sum_congr rfl
  intro t ht
  have hc := hT t ht
  rw [SimpleGraph.isNClique_iff] at hc
  rw [show (∑ x : W, if x ∈ t then (1 : ℕ) else 0) = t.card by
    rw [Finset.sum_boole]; simp]
  exact hc.2

/-- Parity double-counting bound for triangle packings: `6·|T| ≤ Σ_v 2·⌊deg v / 2⌋`. -/
lemma packing_card_parity_bound (H : SimpleGraph W) [DecidableRel H.Adj]
    {T : Finset (Finset W)} (hT : IsTrianglePacking H T) :
    6 * T.card ≤ ∑ v : W, 2 * (H.degree v / 2) := by
  have h3 : ∑ v : W, (T.filter (fun t => v ∈ t)).card = 3 * T.card :=
    sum_card_triangles_at H T hT.1
  have key : 6 * T.card = ∑ v : W, 2 * (T.filter (fun t => v ∈ t)).card := by
    rw [← Finset.mul_sum, h3]; ring
  rw [key]
  apply Finset.sum_le_sum
  intro v _
  have hb := card_triangles_at_le_degree H hT v
  have hle : (T.filter (fun t => v ∈ t)).card ≤ H.degree v / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num)]; omega
  omega

/-- For the `q = 0` split graph on an **even** clique of size `p ≥ 2`, `ν₃ ≤ p(p−2)/6`. -/
lemma nu3_clique_even_le (G : SplitGraph) (hq : G.q = 0) (hp2 : 2 ≤ G.p) (hpev : Even G.p) :
    6 * G.nu3' ≤ G.p * (G.p - 2) := by
  haveI : IsEmpty (Fin G.q) := hq ▸ inferInstanceAs (IsEmpty (Fin 0))
  have hpev' : G.p % 2 = 0 := by rcases hpev with ⟨m, hm⟩; omega
  have hsum : ∑ v : G.V, 2 * (G.graph.degree v / 2) ≤ G.p * (G.p - 2) := by
    have hstep : ∑ v : G.V, 2 * (G.graph.degree v / 2)
        = ∑ a : Fin G.p, 2 * (G.graph.degree (Sum.inl a) / 2) := by
      rw [Fintype.sum_sum_type]; simp
    rw [hstep]
    calc ∑ a : Fin G.p, 2 * (G.graph.degree (Sum.inl a) / 2)
        ≤ ∑ _a : Fin G.p, (G.p - 2) := by
          apply Finset.sum_le_sum
          intro a _
          have hd : G.graph.degree (Sum.inl a) < G.p := by
            have := G.graph.degree_lt_card_verts (Sum.inl a)
            simpa [SplitGraph.V, hq] using this
          omega
      _ = G.p * (G.p - 2) := by rw [Finset.sum_const]; simp
  have hbound : ∀ T : Finset (Finset G.V), IsTrianglePacking G.graph T →
      6 * T.card ≤ G.p * (G.p - 2) := fun T hT =>
    le_trans (packing_card_parity_bound G.graph hT) hsum
  have hN : G.nu3' ≤ (G.p * (G.p - 2)) / 6 := by
    unfold SplitGraph.nu3' nu3
    apply csSup_le
    · exact ⟨0, ∅, ⟨by simp, by simp⟩, by simp⟩
    · rintro c ⟨T, hT, rfl⟩
      have := hbound T hT; omega
  omega

/-- **`E_8_very_sparse_packing_estimate` is false.** -/
theorem E_8_very_sparse_packing_estimate_false (k : ℕ) :
    ¬ (∃ n₀ : ℕ, ∀ G : SplitGraph, n₀ ≤ G.n → 10 * G.q < G.p →
      (∀ i : Fin G.q, (2 * (G.n : ℝ) - 1) / 6 + k < (G.d i : ℝ)) →
      ((G.edgeCount : ℝ) - (G.n : ℝ) ^ 2 / 6) / 2 ≤ (G.nu3' : ℝ)) := by
  rintro ⟨n₀, h⟩
  let G : SplitGraph := ⟨2 * (n₀ + 1), 0, Fin.elim0⟩
  have hq : G.q = 0 := rfl
  have hpp : G.p = 2 * (n₀ + 1) := rfl
  have hp2 : 2 ≤ G.p := by rw [hpp]; omega
  have hpev : Even G.p := by rw [hpp]; exact ⟨n₀ + 1, by ring⟩
  haveI hemp : IsEmpty (Fin G.q) := hq ▸ inferInstanceAs (IsEmpty (Fin 0))
  have hn : n₀ ≤ G.n := by rw [SplitGraph.n, hpp, hq]; omega
  have h10 : 10 * G.q < G.p := by rw [hq, hpp]; omega
  have hdeg : ∀ i : Fin G.q, (2 * (G.n : ℝ) - 1) / 6 + k < (G.d i : ℝ) :=
    fun i => isEmptyElim i
  have hconcl := h G hn h10 hdeg
  have hnu := nu3_clique_even_le G hq hp2 hpev
  have he : G.edgeCount = G.p.choose 2 := by
    rw [SplitGraph.edgeCount_eq]; simp
  have hnn : (G.n : ℝ) = (G.p : ℝ) := by rw [SplitGraph.n, hq]; simp
  have heR : (G.edgeCount : ℝ) = (G.p : ℝ) * ((G.p : ℝ) - 1) / 2 := by
    rw [he, Nat.cast_choose_two]
  have hnuR : 6 * (G.nu3' : ℝ) ≤ (G.p : ℝ) * ((G.p : ℝ) - 2) := by
    calc 6 * (G.nu3' : ℝ) = ((6 * G.nu3' : ℕ) : ℝ) := by push_cast; ring
      _ ≤ ((G.p * (G.p - 2) : ℕ) : ℝ) := by exact_mod_cast hnu
      _ = (G.p : ℝ) * ((G.p : ℝ) - 2) := by push_cast [Nat.cast_sub hp2]; ring
  have hP2 : (2 : ℝ) ≤ (G.p : ℝ) := by exact_mod_cast hp2
  rw [heR, hnn] at hconcl
  nlinarith [hconcl, hnuR, hP2]

end PaperIII

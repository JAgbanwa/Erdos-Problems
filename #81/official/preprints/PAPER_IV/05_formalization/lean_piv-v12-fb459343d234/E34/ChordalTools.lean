import E34.CoBipartite

/-!
# E34 — chordality tools and Lemma 4 (large cliques in dense chordal graphs)

* `exists_simplicial_in` — Dirac: an induced chordal subgraph on a nonempty set `U` has a
  vertex whose neighbourhood in `U` is a clique.
* `isChordal_of_simplicial_outside` — if every vertex outside `Y` is simplicial and `H[Y]` is
  chordal, then `H` is chordal.
* `exists_large_clique` — **Lemma 4 (elementary form).** If `G[D]` is chordal, then `D`
  contains a clique `C` with `(|D| − |C|)² ≤ ` (number of ordered non-adjacent pairs of `D`).
  In unordered terms: a chordal graph on `d` vertices with `M` non-edges has
  `ω ≥ d − √(2M)`, which is the Gyárfás–Hubenko–Solymosi bound
  `ω ≥ (1 − √(1 − 2c)) d` for `c d² ≤ C(d,2) − M` edges.
-/

namespace E34

open Finset

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

/-- Chordality passes to induced subgraphs on subsets. -/
theorem isChordal_induce_mono {U U' : Finset (Fin n)} (h : U' ⊆ U)
    (hU : AlonShapira.IsChordal (G.induce (U : Set (Fin n)))) :
    AlonShapira.IsChordal (G.induce (U' : Set (Fin n))) :=
  hU.of_embedding (SimpleGraph.induceHomOfLE G (by exact_mod_cast h))

/-- Dirac's theorem, relative form. -/
theorem exists_simplicial_in (U : Finset (Fin n))
    (hU : AlonShapira.IsChordal (G.induce (U : Set (Fin n)))) (hne : U.Nonempty) :
    ∃ v ∈ U, ∀ a ∈ U, ∀ b ∈ U, G.Adj v a → G.Adj v b → a ≠ b → G.Adj a b := by
  classical
  have h2 : (G.induce (U : Set (Fin n))).IsChordal :=
    PaperIV.EditRoute.isChordal_of_noInducedCycle _ (fun k hk => hU k _ ⟨hk, rfl⟩)
  haveI : Nonempty (U : Set (Fin n)) := ⟨⟨hne.choose, hne.choose_spec⟩⟩
  obtain ⟨⟨v, hv⟩, hs⟩ := h2.exists_isSimplicial
  refine ⟨v, hv, fun a ha b hb hva hvb hab => ?_⟩
  have := hs (x := ⟨a, ha⟩) (y := ⟨b, hb⟩) hva hvb (fun h => hab (congrArg Subtype.val h))
  exact this

/-- Simplicial vertices outside a chordal part keep the graph chordal. -/
theorem isChordal_of_simplicial_outside (H : SimpleGraph (Fin n)) (Y : Finset (Fin n))
    (hY : AlonShapira.IsChordal (H.induce (Y : Set (Fin n))))
    (hX : ∀ x, x ∉ Y → ∀ a b, H.Adj x a → H.Adj x b → a ≠ b → H.Adj a b) :
    AlonShapira.IsChordal H := by
  intro k F hF
  obtain ⟨hk, rfl⟩ := hF
  refine ⟨fun e => ?_⟩
  by_cases h : ∃ p, e p ∉ Y
  · obtain ⟨p, hp⟩ := h
    have ha1 : H.Adj (e p) (e (succPos (by omega) p)) := e.map_adj_iff.2 (cyc_adj_succ hk p)
    have ha2 : H.Adj (e p) (e (predPos (by omega) p)) := e.map_adj_iff.2 (cyc_adj_pred hk p)
    have hne : e (succPos (by omega) p) ≠ e (predPos (by omega) p) :=
      fun h' => succ_ne_pred hk p (e.injective h')
    exact not_cyc_adj_succ_pred hk p (e.map_adj_iff.1 (hX _ hp _ _ ha1 ha2 hne))
  · push_neg at h
    let e' : SimpleGraph.cycleGraph k ↪g H.induce (Y : Set (Fin n)) :=
      { toFun := fun i => ⟨e i, h i⟩
        inj' := fun i j hij => e.injective (congrArg Subtype.val hij)
        map_rel_iff' := by
          intro a b
          simp only [Function.Embedding.coeFn_mk, SimpleGraph.comap_adj,
            Function.Embedding.coe_subtype]
          exact e.map_adj_iff }
    exact (hY k _ ⟨hk, rfl⟩).false e'

/-- Ordered non-adjacent pairs of distinct vertices inside `D`. -/
def ordNE (D : Finset (Fin n)) : ℕ :=
  ((D ×ˢ D).filter (fun p => p.1 ≠ p.2 ∧ ¬ G.Adj p.1 p.2)).card

theorem ordNE_mono {D D' : Finset (Fin n)} (h : D' ⊆ D) : ordNE G D' ≤ ordNE G D := by
  unfold ordNE
  apply card_le_card
  intro p hp
  simp only [mem_filter, mem_product] at hp ⊢
  exact ⟨⟨h hp.1.1, h hp.1.2⟩, hp.2⟩

/-- Removing a vertex `v` of `D` loses at least `2 · (non-neighbours of v in D \ {v})`
ordered non-adjacent pairs. -/
theorem ordNE_erase_add (D : Finset (Fin n)) (v : Fin n) (hv : v ∈ D) :
    ordNE G (D.erase v) + 2 * ((D.erase v).filter (fun b => ¬ G.Adj v b)).card ≤ ordNE G D := by
  unfold ordNE
  set S := (D.erase v).filter (fun b => ¬ G.Adj v b)
  set A1 := ((D.erase v ×ˢ D.erase v).filter (fun p => p.1 ≠ p.2 ∧ ¬ G.Adj p.1 p.2))
  set A2 := S.map ⟨fun b => (v, b), fun x y h => by simpa using h⟩
  set A3 := S.map ⟨fun b => (b, v), fun x y h => by simpa using h⟩
  have hsub : A1 ∪ A2 ∪ A3 ⊆ (D ×ˢ D).filter (fun p => p.1 ≠ p.2 ∧ ¬ G.Adj p.1 p.2) := by
    intro p hp
    simp only [A1, A2, A3, S, mem_union, mem_filter, mem_product, mem_map, mem_erase,
      Function.Embedding.coeFn_mk] at hp ⊢
    rcases hp with (⟨⟨⟨_, h1⟩, ⟨_, h2⟩⟩, h3⟩ | ⟨b, ⟨⟨hbv, hb⟩, hnb⟩, rfl⟩) | ⟨b, ⟨⟨hbv, hb⟩, hnb⟩, rfl⟩
    · exact ⟨⟨h1, h2⟩, h3⟩
    · exact ⟨⟨hv, hb⟩, Ne.symm hbv, hnb⟩
    · exact ⟨⟨hb, hv⟩, hbv, fun h => hnb h.symm⟩
  have hd12 : Disjoint A1 A2 := by
    rw [disjoint_left]; intro p h1 h2
    simp only [A1, A2, mem_filter, mem_product, mem_map, mem_erase,
      Function.Embedding.coeFn_mk] at h1 h2
    obtain ⟨b, _, rfl⟩ := h2
    exact h1.1.1.1 rfl
  have hd123 : Disjoint (A1 ∪ A2) A3 := by
    rw [disjoint_left]; intro p h12 h3
    simp only [A1, A2, A3, S, mem_union, mem_filter, mem_product, mem_map, mem_erase,
      Function.Embedding.coeFn_mk] at h12 h3
    obtain ⟨b, ⟨⟨hbv, _⟩, _⟩, rfl⟩ := h3
    rcases h12 with h | ⟨c, _, hc⟩
    · exact h.1.2.1 rfl
    · simp only [Prod.mk.injEq] at hc; exact hbv hc.1.symm
  have := card_le_card hsub
  rw [card_union_of_disjoint hd123, card_union_of_disjoint hd12, card_map, card_map] at this
  omega

/-- **Lemma 4 (elementary form).** -/
theorem exists_large_clique (Y : Finset (Fin n))
    (hY : AlonShapira.IsChordal (G.induce (Y : Set (Fin n)))) :
    ∀ D ⊆ Y, ∃ C ⊆ D, G.IsClique (C : Set (Fin n)) ∧ (D.card - C.card) ^ 2 ≤ ordNE G D := by
  intro D
  induction D using Finset.strongInduction with
  | H D ih =>
    intro hDY
    rcases D.eq_empty_or_nonempty with hD | hD
    · subst hD; exact ⟨∅, empty_subset _, by simp, by simp⟩
    · obtain ⟨v, hv, hsimp⟩ := exists_simplicial_in G D (isChordal_induce_mono G hDY hY) hD
      obtain ⟨C', hC'D, hC', hC'b⟩ := ih (D.erase v) (erase_ssubset hv)
        ((erase_subset _ _).trans hDY)
      have hstep := ordNE_erase_add G D v hv
      set N := (D.erase v).filter (fun b => G.Adj v b)
      set y := ((D.erase v).filter (fun b => ¬ G.Adj v b)).card
      have hNy : N.card + y = (D.erase v).card := by
        rw [card_filter_add_card_filter_not]
      have hDe : (D.erase v).card + 1 = D.card := card_erase_add_one hv
      have hC'le : C'.card ≤ (D.erase v).card := card_le_card hC'D
      set x := (D.erase v).card - C'.card
      by_cases hyx : y ≤ x
      · refine ⟨insert v N, ?_, ?_, ?_⟩
        · intro a ha
          rcases mem_insert.1 ha with rfl | ha
          · exact hv
          · exact (mem_erase.1 (mem_filter.1 ha).1).2
        · intro a ha b hb hab
          simp only [coe_insert, Set.mem_insert_iff, mem_coe] at ha hb
          rcases ha with rfl | ha <;> rcases hb with rfl | hb
          · exact absurd rfl hab
          · exact (mem_filter.1 hb).2
          · exact ((mem_filter.1 ha).2).symm
          · exact hsimp a (mem_erase.1 (mem_filter.1 ha).1).2 b (mem_erase.1 (mem_filter.1 hb).1).2
              (mem_filter.1 ha).2 (mem_filter.1 hb).2 hab
        · have hvN : v ∉ N := fun h => (mem_erase.1 (mem_filter.1 h).1).1 rfl
          rw [card_insert_of_notMem hvN]
          have e : D.card - (N.card + 1) = y := by omega
          rw [e]
          have : y ^ 2 ≤ x ^ 2 := Nat.pow_le_pow_left hyx 2
          omega
      · push_neg at hyx
        refine ⟨C', hC'D.trans (erase_subset _ _), hC', ?_⟩
        have e : D.card - C'.card = x + 1 := by omega
        rw [e]
        have : (x + 1) ^ 2 = x ^ 2 + 2 * x + 1 := by ring
        omega

end E34

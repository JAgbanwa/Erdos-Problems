import A4S1.IndepAllPairs

/-!
# E14 (copied from E10 `A4S1.OwnAllPeel`, no forbidden import)
# E10, own terminal for every rooted defect `s`: joint incidence by peeling

`joint_peel`. Let `P` be a family of `ν ≤ s` disjoint non-adjacent pairs, `X` a vertex set with
distinct non-neighbours `c t` (`t ∈ X`), and `Z` a set of rows adjacent to every endpoint of `P`
and to every `c t`, in which every clique has at most `ω` vertices. Then

  `Σ_{z ∈ Z} |N(z) ∩ X| ≤ (s − ν)|Z| + 2(ω + s)|X|`.

Proof: peeling. Apply `RootedDefectAt G s` (root `∅`) to `U ⊇ W = ends(P) ∪ c(X)` and remove
the vertex found.
* A row `z` of defect `≤ s` sees at most `s − ν` vertices `t ∈ X ∩ U`: the pairs of `P` together
  with the pairs `(t, c t)` are disjoint non-adjacent pairs in its neighbourhood.
* A vertex `t ∈ X` of defect `≤ s` sees at most `ω + s` remaining rows.
* If a vertex of `W` has defect `≤ s`, at most `ω + s` rows remain (they are all its
  neighbours), and the count is bounded directly.
-/

namespace A4S1.IndepAll

open Finset PaperIV.RootedSimplicialDefect A4S1.TerminalPacking

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [Fintype V] [DecidableRel G.Adj] in
theorem card_le_of_sub_neighbors {Z Y N C : Finset V} {ω s : ℕ}
    (hω : ∀ K ⊆ Z, G.IsClique (K : Set V) → K.card ≤ ω) (hC : G.IsClique (C : Set V))
    (hNC : (N \ C).card ≤ s) (hYZ : Y ⊆ Z) (hYN : Y ⊆ N) : Y.card ≤ s + ω := by
  have h1 : Y.card ≤ (Y \ C).card + (Y ∩ C).card := by
    rw [← card_union_of_disjoint (disjoint_sdiff_inter Y C), sdiff_union_inter]
  have h2 : (Y \ C).card ≤ (N \ C).card := card_le_card (sdiff_subset_sdiff hYN (subset_refl _))
  have h3 : (Y ∩ C).card ≤ ω :=
    hω _ (inter_subset_left.trans hYZ) (hC.subset (by simp))
  omega

omit [Fintype V] in
theorem card_filter_insert_le (A : Finset V) (v : V) (p : V → Prop) [DecidablePred p] :
    ((insert v A).filter p).card ≤ (A.filter p).card + if p v then 1 else 0 := by
  rw [filter_insert]
  split_ifs
  · exact card_insert_le _ _
  · simp

omit [Fintype V] in
/-- **Joint incidence by peeling.** -/
theorem joint_peel {s : ℕ} (hG : RootedDefectAt G s) (Z X : Finset V) (P : Finset (V × V))
    (c : V → V) (ω : ℕ) (hP : IsPairFam P) (hPn : ∀ p ∈ P, ¬ G.Adj p.1 p.2)
    (hPs : P.card ≤ s) (hcn : ∀ t ∈ X, ¬ G.Adj t (c t)) (hcinj : Set.InjOn c X)
    (hZX : Disjoint Z X) (hZW : Disjoint Z (pends P ∪ X.image c))
    (hXW : Disjoint X (pends P ∪ X.image c)) (hPc : Disjoint (pends P) (X.image c))
    (hZadj : ∀ z ∈ Z, ∀ w ∈ pends P ∪ X.image c, G.Adj z w)
    (hω : ∀ K ⊆ Z, G.IsClique (K : Set V) → K.card ≤ ω) :
    ∑ z ∈ Z, (X.filter (G.Adj z)).card ≤ (s - P.card) * Z.card + 2 * (ω + s) * X.card := by
  set W := pends P ∪ X.image c with hW
  -- the pairs `(t, c t)`
  have hfam : ∀ Y ⊆ X, IsPairFam (Y.image fun t => (t, c t)) ∧
      Disjoint (pends P) (pends (Y.image fun t => (t, c t))) ∧
      (Y.image fun t => (t, c t)).card = Y.card := by
    intro Y hY
    have hcW : ∀ t ∈ X, c t ∈ W := fun t ht => mem_union_right _ (mem_image_of_mem c ht)
    have htc : ∀ t ∈ X, t ≠ c t := fun t ht h => disjoint_left.1 hXW ht (h ▸ hcW t ht)
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · intro p hp
      obtain ⟨t, ht, rfl⟩ := mem_image.1 hp
      exact htc t (hY ht)
    · intro p hp q hq hpq
      obtain ⟨t, ht, rfl⟩ := mem_image.1 hp
      obtain ⟨t', ht', rfl⟩ := mem_image.1 hq
      have htt : t ≠ t' := fun h => hpq (by rw [h])
      refine ⟨htt, fun h => ?_, fun h => ?_, fun h => htt ?_⟩
      · simp only at h
        exact disjoint_left.1 hXW (hY ht) (h ▸ hcW t' (hY ht'))
      · simp only at h
        exact disjoint_left.1 hXW (hY ht') (h ▸ hcW t (hY ht))
      exact hcinj (mem_coe.2 (hY ht)) (mem_coe.2 (hY ht')) h
    · rw [disjoint_left]
      intro v hv hv'
      obtain ⟨p, hp, h | h⟩ := mem_pends.1 hv'
      · obtain ⟨t, ht, rfl⟩ := mem_image.1 hp
        simp only at h
        exact disjoint_left.1 hXW (hY ht) (h ▸ mem_union_left _ hv)
      · obtain ⟨t, ht, rfl⟩ := mem_image.1 hp
        simp only at h
        exact disjoint_left.1 hPc hv (h ▸ mem_image_of_mem c (hY ht))
    · exact card_image_of_injOn (fun t _ t' _ h => (Prod.ext_iff.1 h).1)
  -- the peeling claim
  have claim : ∀ U : Finset V, W ⊆ U → U ⊆ Z ∪ X ∪ W →
      ∑ z ∈ Z ∩ U, ((X ∩ U).filter (G.Adj z)).card ≤
        (s - P.card) * (Z ∩ U).card + (ω + s) * ((X ∩ U).card + X.card) := by
    intro U
    induction U using Finset.strongInduction with
    | H U ih =>
      intro hWU hU0
      by_cases hZU : Z ∩ U = ∅
      · rw [hZU, sum_empty]; exact Nat.zero_le _
      have hUne : U.Nonempty := by
        obtain ⟨z, hz⟩ := nonempty_iff_ne_empty.2 hZU
        exact ⟨z, (mem_inter.1 hz).2⟩
      obtain ⟨v, hvU, C, hCsub, hC, hcard⟩ := defect_step hG hUne
      have hvU0 := hU0 hvU
      rcases mem_union.1 hvU0 with hv | hvW
      · rcases mem_union.1 hv with hvZ | hvX
        · -- a row
          set U' := U.erase v with hU'
          have hvW : v ∉ W := fun h => disjoint_left.1 hZW hvZ h
          have hvX : v ∉ X := fun h => disjoint_left.1 hZX hvZ h
          have hIH := ih U' (erase_ssubset hvU) (fun w hw => mem_erase.2 ⟨fun h => hvW (h ▸ hw),
            hWU hw⟩) ((erase_subset _ _).trans hU0)
          have hZeq : Z ∩ U = insert v (Z ∩ U') := by
            ext w; simp only [hU', mem_inter, mem_insert, mem_erase]
            constructor
            · rintro ⟨h1, h2⟩; by_cases h : w = v
              · exact Or.inl h
              · exact Or.inr ⟨h1, h, h2⟩
            · rintro (rfl | ⟨h1, -, h2⟩)
              · exact ⟨hvZ, hvU⟩
              · exact ⟨h1, h2⟩
          have hvnot : v ∉ Z ∩ U' := by simp [hU']
          have hXeq : X ∩ U' = X ∩ U := by
            ext w; simp only [hU', mem_inter, mem_erase]
            constructor
            · rintro ⟨h1, -, h2⟩; exact ⟨h1, h2⟩
            · rintro ⟨h1, h2⟩; exact ⟨h1, fun h => hvX (h ▸ h1), h2⟩
          -- the row sees at most `s − ν` vertices of `X ∩ U`
          set Xv := (X ∩ U).filter (G.Adj v) with hXv
          obtain ⟨hF1, hF2, hF3⟩ := hfam Xv (fun t ht => (mem_inter.1 (mem_filter.1 ht).1).1)
          obtain ⟨hFam, hFdisj⟩ := hP.union hF1 hF2
          have hFn : ∀ p ∈ P ∪ Xv.image (fun t => (t, c t)), ¬ G.Adj p.1 p.2 := by
            intro p hp
            rcases mem_union.1 hp with hp | hp
            · exact hPn p hp
            · obtain ⟨t, ht, rfl⟩ := mem_image.1 hp
              exact hcn t (mem_inter.1 (mem_filter.1 ht).1).1
          have hFN : ∀ p ∈ P ∪ Xv.image (fun t => (t, c t)),
              p.1 ∈ neighborsIn G U v ∧ p.2 ∈ neighborsIn G U v := by
            have hWN : ∀ w ∈ W, w ∈ neighborsIn G U v := fun w hw =>
              mem_neighborsIn.2 ⟨hWU hw, hZadj v hvZ w hw⟩
            intro p hp
            rcases mem_union.1 hp with hp | hp
            · exact ⟨hWN _ (mem_union_left _ (fst_mem_pends hp)),
                hWN _ (mem_union_left _ (snd_mem_pends hp))⟩
            · obtain ⟨t, ht, rfl⟩ := mem_image.1 hp
              obtain ⟨ht1, ht2⟩ := mem_filter.1 ht
              exact ⟨mem_neighborsIn.2 ⟨(mem_inter.1 ht1).2, ht2⟩,
                hWN _ (mem_union_right _ (mem_image_of_mem c (mem_inter.1 ht1).1))⟩
          have hFc := card_le_sdiff_of_pairs hFam hFn hFN hC
          rw [card_union_of_disjoint hFdisj, hF3] at hFc
          have hrow : Xv.card ≤ s - P.card := by omega
          rw [hZeq, sum_insert hvnot, card_insert_of_notMem hvnot]
          rw [hXeq] at hIH
          have : ∑ z ∈ Z ∩ U', ((X ∩ U).filter (G.Adj z)).card ≤
              (s - P.card) * (Z ∩ U').card + (ω + s) * ((X ∩ U).card + X.card) := hIH
          rw [Nat.mul_succ]
          have hXvdef : ((X ∩ U).filter (G.Adj v)).card = Xv.card := rfl
          omega
        · -- a vertex of `X`
          set U' := U.erase v with hU'
          have hvW : v ∉ W := fun h => disjoint_left.1 hXW hvX h
          have hvZ : v ∉ Z := fun h => disjoint_left.1 hZX h hvX
          have hIH := ih U' (erase_ssubset hvU) (fun w hw => mem_erase.2 ⟨fun h => hvW (h ▸ hw),
            hWU hw⟩) ((erase_subset _ _).trans hU0)
          have hZeq : Z ∩ U' = Z ∩ U := by
            ext w; simp only [hU', mem_inter, mem_erase]
            constructor
            · rintro ⟨h1, -, h2⟩; exact ⟨h1, h2⟩
            · rintro ⟨h1, h2⟩; exact ⟨h1, fun h => hvZ (h ▸ h1), h2⟩
          have hXeq : X ∩ U = insert v (X ∩ U') := by
            ext w; simp only [hU', mem_inter, mem_insert, mem_erase]
            constructor
            · rintro ⟨h1, h2⟩; by_cases h : w = v
              · exact Or.inl h
              · exact Or.inr ⟨h1, h, h2⟩
            · rintro (rfl | ⟨h1, -, h2⟩)
              · exact ⟨hvX, hvU⟩
              · exact ⟨h1, h2⟩
          have hvnot : v ∉ X ∩ U' := by simp [hU']
          rw [hZeq] at hIH
          have hstep : ∑ z ∈ Z ∩ U, ((X ∩ U).filter (G.Adj z)).card ≤
              ∑ z ∈ Z ∩ U, ((X ∩ U').filter (G.Adj z)).card +
                ((Z ∩ U).filter fun z => G.Adj z v).card := by
            rw [card_filter, ← sum_add_distrib]
            refine sum_le_sum fun z _ => ?_
            rw [hXeq]
            exact card_filter_insert_le _ _ _
          have hnb : ((Z ∩ U).filter fun z => G.Adj z v).card ≤ s + ω :=
            card_le_of_sub_neighbors hω hC hcard
              ((filter_subset _ _).trans inter_subset_left)
              (fun z hz => mem_neighborsIn.2 ⟨(mem_inter.1 (mem_filter.1 hz).1).2,
                (mem_filter.1 hz).2.symm⟩)
          rw [hXeq, card_insert_of_notMem hvnot]
          rw [hXeq] at hstep
          have : (ω + s) * ((X ∩ U').card + 1 + X.card) =
              (ω + s) * ((X ∩ U').card + X.card) + (ω + s) := by ring
          rw [this]
          omega
      · -- a vertex of `W`: few rows remain
        have hZN : Z ∩ U ⊆ neighborsIn G U v := fun z hz =>
          mem_neighborsIn.2 ⟨(mem_inter.1 hz).2, (hZadj z (mem_inter.1 hz).1 v hvW).symm⟩
        have hZc : (Z ∩ U).card ≤ s + ω :=
          card_le_of_sub_neighbors hω hC hcard inter_subset_left hZN
        have h1 : ∑ z ∈ Z ∩ U, ((X ∩ U).filter (G.Adj z)).card ≤ ∑ _z ∈ Z ∩ U, X.card :=
          sum_le_sum fun z _ => (card_filter_le _ _).trans (card_le_card inter_subset_left)
        rw [sum_const, smul_eq_mul] at h1
        have h2 : (Z ∩ U).card * X.card ≤ (s + ω) * X.card := Nat.mul_le_mul_right _ hZc
        nlinarith
  have hfin := claim (Z ∪ X ∪ W) subset_union_right (subset_refl _)
  have hZ : Z ∩ (Z ∪ X ∪ W) = Z := inter_eq_left.2 (subset_union_left.trans subset_union_left)
  have hX : X ∩ (Z ∪ X ∪ W) = X := inter_eq_left.2 (subset_union_right.trans subset_union_left)
  rw [hZ, hX] at hfin
  have : (ω + s) * (X.card + X.card) = 2 * (ω + s) * X.card := by ring
  omega

end A4S1.IndepAll

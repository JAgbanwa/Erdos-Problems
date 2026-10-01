import E32.Basic

/-!
# E32 — transferring partitions along edits, and the partition of `E_s`

* `exists_partition_of_edit`: an order-`≤ 4` clique partition of a graph `X` yields one of any
  graph `G` on the same vertices with at most `|Q| + |E(G) ∖ E(X)| + 4·|E(X) ∖ E(G)|` pieces
  (a deleted edge destroys one piece of at most six edges, whose at most five surviving edges
  are re-covered individually; an added edge is one new piece).
* `exists_extremal_partition`: `defSplitGraph C D H` has an order-`≤ 4` partition with
  `rootBaseline C D H = (|C|+|D|)|H| − C(|C|,2)` pieces when `2 ≤ |C| ≤ |H|`.
-/

namespace E32

open Finset PaperIV.FarRounding PaperIV.DefectComparatorGraph PaperIV.SplitUniformIncidence

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The graph whose edges are the pairs of a family of pieces. -/
def piecesGraph (P : Finset (Finset V)) : SimpleGraph V where
  Adj a b := a ≠ b ∧ ∃ K ∈ P, a ∈ K ∧ b ∈ K
  symm := fun _ _ ⟨h, K, hK, ha, hb⟩ => ⟨h.symm, K, hK, hb, ha⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance (P : Finset (Finset V)) : DecidableRel (piecesGraph P).Adj := by
  intro a b; unfold piecesGraph; infer_instance

omit [Fintype V] in
theorem card_pairs_le_six {K : Finset V} (hK : K.card ≤ 4) : (pairs K).card ≤ 6 := by
  have h : (pairs K).card = K.card.choose 2 := PaperIV.Model.card_pieceEdges K
  rw [h]
  interval_cases hc : K.card <;> decide

/-- **Edit transfer for partitions.** -/
theorem exists_partition_of_edit (G X : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel X.Adj]
    (Q : CliquePartition X) (h4 : Q.OrderAtMost 4) :
    ∃ Q' : CliquePartition G, Q'.OrderAtMost 4 ∧
      Q'.size ≤ Q.size + (G.edgeFinset \ X.edgeFinset).card +
        4 * (X.edgeFinset \ G.edgeFinset).card := by
  classical
  set Good := Q.pieces.filter (fun K => pairs K ⊆ G.edgeFinset) with hGood
  set Bad := Q.pieces.filter (fun K => ¬ pairs K ⊆ G.edgeFinset) with hBad
  set Y := piecesGraph Good with hY
  have hGoodQ : Good ⊆ Q.pieces := filter_subset _ _
  have hYedges : Good.biUnion pairs = Y.edgeFinset := by
    ext e
    induction e using Sym2.ind with
    | _ a b =>
      simp only [mem_biUnion, mk_mem_pairs, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
        hY, piecesGraph]
      constructor
      · rintro ⟨K, hK, ha, hb, hab⟩; exact ⟨hab, K, hK, ha, hb⟩
      · rintro ⟨hab, K, hK, ha, hb⟩; exact ⟨K, hK, ha, hb, hab⟩
  let QY : CliquePartition Y :=
    { pieces := Good
      isClique := fun K hK a ha b hb hab => ⟨hab, K, hK, ha, hb⟩
      two_le_card := fun K hK => Q.two_le_card K (hGoodQ hK)
      edgeDisjoint := fun K hK L hL hKL => Q.edgeDisjoint K (hGoodQ hK) L (hGoodQ hL) hKL
      covers := hYedges }
  have hYG : Y ≤ G := by
    rintro a b ⟨hab, K, hK, ha, hb⟩
    have hsub := (mem_filter.1 hK).2
    have : s(a, b) ∈ G.edgeFinset := hsub (mk_mem_pairs.2 ⟨ha, hb, hab⟩)
    simpa using this
  obtain ⟨Q', hQ'4, hQ'⟩ := PaperIV.SubgraphPadding.exists_cliquePartition_of_subgraph
    G Y hYG QY (fun K hK => h4 K (hGoodQ hK))
  refine ⟨Q', hQ'4, le_trans hQ' ?_⟩
  -- the edges of `G` missing from `Y`
  have hsplit : Good.card + Bad.card = Q.size := by
    rw [hGood, hBad, CliquePartition.size]
    exact card_filter_add_card_filter_not _
  have hsub : G.edgeFinset \ Y.edgeFinset ⊆
      (G.edgeFinset \ X.edgeFinset) ∪ Bad.biUnion (fun K => pairs K ∩ G.edgeFinset) := by
    intro e he
    obtain ⟨heG, heY⟩ := mem_sdiff.1 he
    by_cases heX : e ∈ X.edgeFinset
    · rw [← Q.covers, mem_biUnion] at heX
      obtain ⟨K, hK, heK⟩ := heX
      have hKbad : K ∈ Bad := by
        rw [hBad, mem_filter]
        refine ⟨hK, fun hKG => heY ?_⟩
        rw [← hYedges, mem_biUnion]
        exact ⟨K, mem_filter.2 ⟨hK, hKG⟩, heK⟩
      exact mem_union_right _ (mem_biUnion.2 ⟨K, hKbad, mem_inter.2 ⟨heK, heG⟩⟩)
    · exact mem_union_left _ (mem_sdiff.2 ⟨heG, heX⟩)
  have hbadpiece : ∀ K ∈ Bad, (pairs K ∩ G.edgeFinset).card ≤ 5 := by
    intro K hK
    obtain ⟨hKQ, hKG⟩ := mem_filter.1 hK
    have h6 := card_pairs_le_six (h4 K hKQ)
    have hlt : (pairs K ∩ G.edgeFinset).card < (pairs K).card := by
      apply card_lt_card
      refine ⟨inter_subset_left, fun h => hKG ?_⟩
      intro e he
      exact (mem_inter.1 (h he)).2
    omega
  have hbadsum : (Bad.biUnion (fun K => pairs K ∩ G.edgeFinset)).card ≤ 5 * Bad.card := by
    calc (Bad.biUnion (fun K => pairs K ∩ G.edgeFinset)).card
        ≤ ∑ K ∈ Bad, (pairs K ∩ G.edgeFinset).card := card_biUnion_le
      _ ≤ ∑ _K ∈ Bad, 5 := sum_le_sum hbadpiece
      _ = 5 * Bad.card := by rw [sum_const, smul_eq_mul, mul_comm]
  -- each bad piece owns a distinct deleted edge
  have hbadcard : Bad.card ≤ (X.edgeFinset \ G.edgeFinset).card := by
    have hone : ∀ K ∈ Bad, 1 ≤ (pairs K \ G.edgeFinset).card := by
      intro K hK
      obtain ⟨_, hKG⟩ := mem_filter.1 hK
      rw [Nat.one_le_iff_ne_zero, Ne, card_eq_zero, sdiff_eq_empty_iff_subset]
      exact hKG
    have hdisj : ∀ K ∈ Bad, ∀ L ∈ Bad, K ≠ L →
        Disjoint (pairs K \ G.edgeFinset) (pairs L \ G.edgeFinset) := by
      intro K hK L hL hKL
      exact Disjoint.mono sdiff_subset sdiff_subset
        (Q.edgeDisjoint K (mem_filter.1 hK).1 L (mem_filter.1 hL).1 hKL)
    have hU : Bad.biUnion (fun K => pairs K \ G.edgeFinset) ⊆ X.edgeFinset \ G.edgeFinset := by
      intro e he
      obtain ⟨K, hK, heK⟩ := mem_biUnion.1 he
      obtain ⟨he1, he2⟩ := mem_sdiff.1 heK
      refine mem_sdiff.2 ⟨?_, he2⟩
      rw [← Q.covers, mem_biUnion]
      exact ⟨K, (mem_filter.1 hK).1, he1⟩
    calc Bad.card = ∑ _K ∈ Bad, 1 := by rw [sum_const, smul_eq_mul, mul_one]
      _ ≤ ∑ K ∈ Bad, (pairs K \ G.edgeFinset).card := sum_le_sum hone
      _ = (Bad.biUnion (fun K => pairs K \ G.edgeFinset)).card := (card_biUnion hdisj).symm
      _ ≤ _ := card_le_card hU
  have hcard := card_le_card hsub
  have hunion := card_union_le (G.edgeFinset \ X.edgeFinset)
    (Bad.biUnion (fun K => pairs K ∩ G.edgeFinset))
  change Good.card + (G.edgeFinset \ Y.edgeFinset).card ≤ _
  omega

/-- The edges of the extremal graph beyond the complete split graph `splitGraph C H` are
`D`–`H` links. -/
theorem card_defSplit_sdiff_split {C D H : Finset V} :
    ((defSplitGraph C D H).edgeFinset \ (splitGraph C H).edgeFinset).card ≤ D.card * H.card := by
  classical
  have hsub : (defSplitGraph C D H).edgeFinset \ (splitGraph C H).edgeFinset ⊆
      PaperIV.SplitEdgeCount.crossEdges D H := by
    intro e he
    induction e using Sym2.ind with
    | _ a b =>
      obtain ⟨h1, h2⟩ := mem_sdiff.1 he
      simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at h1 h2
      rw [PaperIV.SplitEdgeCount.mem_crossEdges]
      obtain ⟨hab, hcase⟩ := h1
      have hns : ¬ (a ≠ b ∧ ((a ∈ C ∧ b ∈ C) ∨ (a ∈ C ∧ b ∈ H) ∨ (a ∈ H ∧ b ∈ C))) := h2
      simp only [mem_union] at hcase
      rcases hcase with h | ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact absurd ⟨hab, Or.inl h⟩ hns
      · rcases ha with ha | ha
        · exact absurd ⟨hab, Or.inr (Or.inl ⟨ha, hb⟩)⟩ hns
        · exact ⟨a, ha, b, hb, rfl⟩
      · rcases hb with hb | hb
        · exact absurd ⟨hab, Or.inr (Or.inr ⟨ha, hb⟩)⟩ hns
        · exact ⟨b, hb, a, ha, Sym2.eq_swap⟩
  calc _ ≤ (PaperIV.SplitEdgeCount.crossEdges D H).card := card_le_card hsub
    _ ≤ (D ×ˢ H).card := card_image_le
    _ = D.card * H.card := card_product _ _

theorem choose_two_le_mul {c h : ℕ} (hch : c ≤ h) : c.choose 2 ≤ c * h := by
  rw [Nat.choose_two_right]
  calc c * (c - 1) / 2 ≤ c * (c - 1) := Nat.div_le_self _ _
    _ ≤ c * h := Nat.mul_le_mul_left _ (by omega)

/-- **The partition of `E_s`.** -/
theorem exists_extremal_partition {C D H : Finset V} (hCH : Disjoint C H)
    (hC2 : 2 ≤ C.card) (hCle : C.card ≤ H.card) :
    ∃ Q : CliquePartition (defSplitGraph C D H), Q.OrderAtMost 4 ∧
      Q.size ≤ rootBaseline C D H := by
  classical
  obtain ⟨Q0, hQ04, hQ0, _⟩ :=
    PaperIV.SplitCompleteSharpValue.exists_sharp_cliquePartition_allParities hCH hC2 hCle
  obtain ⟨Q, hQ4, hQ⟩ := PaperIV.SubgraphPadding.exists_cliquePartition_of_subgraph
    (defSplitGraph C D H) (splitGraph C H) (splitGraph_le_defSplitGraph C D H) Q0 hQ04
  refine ⟨Q, hQ4, le_trans hQ ?_⟩
  have h1 := card_defSplit_sdiff_split (C := C) (D := D) (H := H)
  have h2 := choose_two_le_mul hCle
  rw [hQ0, rootBaseline, add_mul]
  omega

end E32

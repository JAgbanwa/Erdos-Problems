import PaperIV.FarRounding

/-!
# Padding a clique partition of a spanning subgraph with `K₂` pieces

If `H ≤ G` have the same vertex set, then a clique partition of `H` extends to a
clique partition of `G` by adding one `K₂` piece for every edge of `G` that `H`
does not have.  The order bound `4` is preserved.

This is the elementary transport step behind the *deletion route* to the
fixed-defect target: if a graph of rooted defect `s` can be made chordal by
deleting few edges, then the chordal theorem plus this padding pays the
difference.  The module proves the transport step and the exact arithmetic of
the available budget; it does **not** prove that a graph of rooted defect `s`
admits such a deletion (see `PaperIV/FixedL4Localization.lean` for the status
discussion).
-/

namespace PaperIV.SubgraphPadding

open Finset
open PaperIV.FarRounding

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Padding lemma.**  A clique partition of a spanning subgraph `H ≤ G` of
order at most four extends to a clique partition of `G` of order at most four,
at the cost of one extra piece per missing edge. -/
theorem exists_cliquePartition_of_subgraph
    (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hHG : H ≤ G) (Q : CliquePartition H) (h4 : Q.OrderAtMost 4) :
    ∃ Q' : CliquePartition G, Q'.OrderAtMost 4 ∧
      Q'.size ≤ Q.size + (G.edgeFinset \ H.edgeFinset).card := by
  classical
  set rest : Finset (Sym2 V) := G.edgeFinset \ H.edgeFinset with hrest
  set newPieces : Finset (Finset V) := rest.image Sym2.toFinset with hnew
  have hHsub : H.edgeFinset ⊆ G.edgeFinset := by
    intro e he
    rw [SimpleGraph.mem_edgeFinset] at he ⊢
    exact SimpleGraph.edgeSet_mono hHG he
  have hrest_not_diag : ∀ e ∈ rest, ¬ e.IsDiag := fun e he =>
    G.not_isDiag_of_mem_edgeFinset (Finset.mem_sdiff.1 he).1
  have hpairs_new : ∀ e ∈ rest, pairs e.toFinset = {e} := fun e he =>
    pairs_toFinset (hrest_not_diag e he)
  have hcard_new : ∀ e ∈ rest, e.toFinset.card = 2 := fun e he =>
    Sym2.card_toFinset_of_not_isDiag e (hrest_not_diag e he)
  have hedge_new : ∀ e ∈ rest, ∀ a ∈ e.toFinset, ∀ b ∈ e.toFinset, a ≠ b → G.Adj a b := by
    intro e he a ha b hb hab
    have hmem : s(a, b) ∈ pairs e.toFinset := mk_mem_pairs.2 ⟨ha, hb, hab⟩
    rw [hpairs_new e he, Finset.mem_singleton] at hmem
    subst hmem
    have hE := (Finset.mem_sdiff.1 he).1
    rwa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at hE
  -- the edge support of an old piece lies in `H`
  have hold_pairs : ∀ K ∈ Q.pieces, pairs K ⊆ H.edgeFinset := by
    intro K hK e he
    rw [← Q.covers]
    exact Finset.mem_biUnion.2 ⟨K, hK, he⟩
  have hkey : ∀ A ∈ newPieces, ∀ B ∈ Q.pieces ∪ newPieces, A ≠ B →
      Disjoint (pairs A) (pairs B) := by
    intro A hA B hB hAB
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hA
    rw [hpairs_new e he, Finset.disjoint_singleton_left]
    intro hmem
    rcases Finset.mem_union.1 hB with h | h
    · exact (Finset.mem_sdiff.1 he).2 (hold_pairs B h hmem)
    · obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 h
      rw [hpairs_new g hg, Finset.mem_singleton] at hmem
      exact hAB (by rw [hmem])
  refine ⟨⟨Q.pieces ∪ newPieces, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro K hK a ha b hb hab
    rcases Finset.mem_union.1 hK with h | h
    · exact hHG (Q.isClique K h a ha b hb hab)
    · obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 h
      exact hedge_new e he a ha b hb hab
  · intro K hK
    rcases Finset.mem_union.1 hK with h | h
    · exact Q.two_le_card K h
    · obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 h
      exact le_of_eq (hcard_new e he).symm
  · intro K hK L hL hKL
    rcases Finset.mem_union.1 hK with hKo | hKn
    · rcases Finset.mem_union.1 hL with hLo | hLn
      · exact Q.edgeDisjoint K hKo L hLo hKL
      · exact (hkey L hLn K hK (Ne.symm hKL)).symm
    · exact hkey K hKn L hL hKL
  · rw [biUnion_union_eq]
    have h₁ : newPieces.biUnion pairs = rest := by
      ext e
      simp only [Finset.mem_biUnion]
      constructor
      · rintro ⟨K, hK, heK⟩
        obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hK
        rw [hpairs_new f hf, Finset.mem_singleton] at heK
        exact heK ▸ hf
      · intro he
        exact ⟨e.toFinset, Finset.mem_image.2 ⟨e, he, rfl⟩,
          by rw [hpairs_new e he]; exact Finset.mem_singleton_self e⟩
    rw [h₁, Q.covers, hrest]
    ext e
    simp only [Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro (h | h)
      · exact hHsub h
      · exact h.1
    · intro h
      by_cases hm : e ∈ H.edgeFinset
      · exact Or.inl hm
      · exact Or.inr ⟨h, hm⟩
  · intro K hK
    rcases Finset.mem_union.1 hK with h | h
    · exact h4 K h
    · obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 h
      have h2 := hcard_new e he
      omega
  · calc (Q.pieces ∪ newPieces).card ≤ Q.pieces.card + newPieces.card :=
          Finset.card_union_le _ _
    _ ≤ Q.size + rest.card := by
          exact Nat.add_le_add_left (Finset.card_image_le) _

end PaperIV.SubgraphPadding

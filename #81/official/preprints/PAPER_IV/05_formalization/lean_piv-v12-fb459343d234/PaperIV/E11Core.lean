import Mathlib.Algebra.Star.BigOperators
import PaperIV.FarRounding

/-!
# E11 helpers: the star of a vertex in a clique partition
-/

namespace PaperIV.E11

open Finset PaperIV.FarRounding

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The pieces through `v`, with `v` removed, cover the neighbourhood of `v`. -/
lemma star_biUnion_eq (Q : CliquePartition G) (v : V) :
    (Q.pieces.filter (v ∈ ·)).biUnion (fun K => K.erase v) = G.neighborFinset v := by
  ext w
  simp only [mem_biUnion, mem_filter, mem_erase, SimpleGraph.mem_neighborFinset]
  constructor
  · rintro ⟨K, ⟨hK, hv⟩, hwv, hw⟩
    exact Q.isClique K hK v hv w hw (Ne.symm hwv)
  · intro h
    have he : s(v, w) ∈ Q.pieces.biUnion pairs := by
      rw [Q.covers, SimpleGraph.mem_edgeFinset]; exact h
    obtain ⟨K, hK, hvw⟩ := mem_biUnion.1 he
    obtain ⟨hv, hw, hne⟩ := mk_mem_pairs.1 hvw
    exact ⟨K, ⟨hK, hv⟩, Ne.symm hne, hw⟩

/-- The sets `K \ {v}` for the pieces through `v` are pairwise disjoint. -/
lemma star_pairwiseDisjoint (Q : CliquePartition G) (v : V) :
    ((Q.pieces.filter (v ∈ ·) : Finset (Finset V)) : Set (Finset V)).PairwiseDisjoint
      (fun K => K.erase v) := by
  intro K hK L hL hKL
  simp only [coe_filter, Set.mem_setOf_eq] at hK hL
  rw [Function.onFun, disjoint_left]
  intro w hwK hwL
  rw [mem_erase] at hwK hwL
  have h1 : s(v, w) ∈ pairs K := mk_mem_pairs.2 ⟨hK.2, hwK.2, Ne.symm hwK.1⟩
  have h2 : s(v, w) ∈ pairs L := mk_mem_pairs.2 ⟨hL.2, hwL.2, Ne.symm hwL.1⟩
  exact disjoint_left.1 (Q.edgeDisjoint K hK.1 L hL.1 hKL) h1 h2

/-- **Local count.**  `Σ_{K ∋ v} (|K| - 1) = deg v`. -/
lemma star_sum (Q : CliquePartition G) (v : V) :
    ∑ K ∈ Q.pieces.filter (v ∈ ·), (K.card - 1) = (G.neighborFinset v).card := by
  rw [← star_biUnion_eq Q v, card_biUnion (star_pairwiseDisjoint Q v)]
  refine sum_congr rfl fun K hK => ?_
  rw [card_erase_of_mem (mem_filter.1 hK).2]

/-- **Pair count.**  `Σ_K C(|K|, 2) = e(G)`. -/
lemma pairs_sum (Q : CliquePartition G) :
    ∑ K ∈ Q.pieces, K.card.choose 2 = G.edgeFinset.card := by
  rw [← Q.covers, card_biUnion (fun K hK L hL h => Q.edgeDisjoint K hK L hL h)]
  exact sum_congr rfl fun K _ => (card_pairs K).symm

end PaperIV.E11

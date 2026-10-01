import PaperIV.PhysicalToCliquePartition
import PaperIV.SplitTriangleFactorHighHost

/-!
# Exact order-four clique-partition value of the high-host complete split graph

The high-host factor module constructs an exact physical partition and proves
optimality among completions of mixed packings. This module closes the model
gap: an arbitrary clique partition of order at most four is itself an exact
physical `K₂/K₃/K₄` partition.
-/

namespace PaperIV.SplitCompleteExactValue

open Finset
open PaperIV.Model PaperIV.SplitUniformIncidence PaperIV.SplitEdgeCount
open PaperIV.PhysicalCompletion PaperIV.SplitPackingObstruction

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Regard an order-four clique partition as a physical exact partition. -/
def toExactPartition (Q : PaperIV.FarRounding.CliquePartition G)
    (hfour : Q.OrderAtMost 4) : IsExactPartition G Q.pieces where
  pieces := by
    intro K hK
    refine ⟨?_, ?_⟩
    · intro a ha b hb hab
      exact Q.isClique K hK a ha b hb hab
    · have htwo := Q.two_le_card K hK
      have hle := hfour K hK
      by_cases h2 : K.card = 2
      · exact ⟨PieceKind.K2, by simpa [PieceKind.size] using h2⟩
      by_cases h3 : K.card = 3
      · exact ⟨PieceKind.K3, by simpa [PieceKind.size] using h3⟩
      have h4 : K.card = 4 := by omega
      exact ⟨PieceKind.K4, by simpa [PieceKind.size] using h4⟩
  edgeDisjoint := by
    intro K hK L hL hne
    simpa [PaperIV.FarRounding.pairs, PaperIV.Model.pieceEdges] using
      Q.edgeDisjoint K hK L hL hne
  covers := by
    simpa [PaperIV.FarRounding.pairs, PaperIV.Model.pieceEdges,
      PaperIV.Model.coveredEdges, PaperIV.Model.graphEdges] using Q.covers

/-- The local core-resource inequality also holds for `K₂` pieces. -/
theorem gainOf_le_two_mul_innerPart_of_piece {Core Hosts : Finset V}
    (hd : Disjoint Core Hosts) {s : Finset V} (hs : IsPiece (splitGraph Core Hosts) s) :
    PaperIV.Model.gainOf s ≤ 2 * (innerPart Core s).card := by
  obtain ⟨kind, hkind⟩ := hs.kind
  cases kind with
  | K2 =>
      have hcard : s.card = 2 := by simpa [PieceKind.size] using hkind
      rw [PaperIV.Model.gainOf_of_card_two hcard]
      omega
  | K3 =>
      exact PaperIV.SplitTriangleFactorHighHost.gainOf_le_two_mul_innerPart hd hs
        (Or.inl (by simpa [PieceKind.size] using hkind))
  | K4 =>
      exact PaperIV.SplitTriangleFactorHighHost.gainOf_le_two_mul_innerPart hd hs
        (Or.inr (by simpa [PieceKind.size] using hkind))

/-- Every order-four clique partition has gain at most twice the number of core edges. -/
theorem totalGain_le_core_of_cliquePartition {Core Hosts : Finset V}
    (hd : Disjoint Core Hosts)
    (Q : PaperIV.FarRounding.CliquePartition (splitGraph Core Hosts))
    (hfour : Q.OrderAtMost 4) :
    PaperIV.Model.totalGain Q.pieces ≤ Core.card * (Core.card - 1) := by
  let hpart : IsExactPartition (splitGraph Core Hosts) Q.pieces :=
    toExactPartition Q hfour
  have hstep : PaperIV.Model.totalGain Q.pieces ≤
      ∑ s ∈ Q.pieces, 2 * (innerPart Core s).card :=
    Finset.sum_le_sum fun s hs =>
      gainOf_le_two_mul_innerPart_of_piece hd (hpart.pieces s hs)
  have hsum : ∑ s ∈ Q.pieces, (innerPart Core s).card =
      ((coveredEdges Q.pieces).filter fun e => e ∈ pieceEdges Core).card :=
    (filter_coveredEdges _ hpart.toIsPacking).symm
  have hle : ((coveredEdges Q.pieces).filter fun e => e ∈ pieceEdges Core).card ≤
      Core.card.choose 2 := by
    rw [← card_pieceEdges Core]
    exact Finset.card_le_card fun e he => (Finset.mem_filter.mp he).2
  have hmul : ∑ s ∈ Q.pieces, 2 * (innerPart Core s).card =
      2 * ∑ s ∈ Q.pieces, (innerPart Core s).card :=
    (Finset.mul_sum _ _ _).symm
  have hchoose := PaperIV.SplitUniformIncidence.mul_pred_eq_two_mul_choose_two Core.card
  omega

/-- Lower bound for every order-four clique partition of a complete split graph. -/
theorem cliquePartition_size_ge_baseline {Core Hosts : Finset V}
    (hd : Disjoint Core Hosts)
    (Q : PaperIV.FarRounding.CliquePartition (splitGraph Core Hosts))
    (hfour : Q.OrderAtMost 4) :
    Core.card * Hosts.card - Core.card.choose 2 ≤ Q.size := by
  let hpart : IsExactPartition (splitGraph Core Hosts) Q.pieces :=
    toExactPartition Q hfour
  have hsum := hpart.card_add_totalGain
  rw [card_graphEdges_splitGraph hd] at hsum
  have hgain := totalGain_le_core_of_cliquePartition hd Q hfour
  have hchoose := PaperIV.SplitUniformIncidence.mul_pred_eq_two_mul_choose_two Core.card
  exact PaperIV.SplitTriangleFactorHighHost.nat_le_of_gain_bound hsum hgain (by omega)

/-- Exact optimum for even core and at least `k-1` hosts. -/
theorem exists_optimal_cliquePartition {Core Hosts : Finset V}
    (hd : Disjoint Core Hosts) {n : ℕ} (hk : Core.card = 2 * n + 2)
    (hh : 2 * n + 1 ≤ Hosts.card) :
    ∃ Q : PaperIV.FarRounding.CliquePartition (splitGraph Core Hosts),
      Q.OrderAtMost 4 ∧
      Q.size = Core.card * Hosts.card - Core.card.choose 2 ∧
      ∀ R : PaperIV.FarRounding.CliquePartition (splitGraph Core Hosts),
        R.OrderAtMost 4 → Q.size ≤ R.size := by
  obtain ⟨P, -, hP, hcard, -⟩ :=
    PaperIV.SplitTriangleFactorHighHost.exists_split_high_host_optimal hd hk hh
  let Q := PaperIV.PhysicalToCliquePartition.ofExactPartition hP
  refine ⟨Q, PaperIV.PhysicalToCliquePartition.ofExactPartition_orderAtMost_four hP,
    ?_, ?_⟩
  · simpa [Q] using hcard
  · intro R hR
    rw [show Q.size = Core.card * Hosts.card - Core.card.choose 2 by simpa [Q] using hcard]
    exact cliquePartition_size_ge_baseline hd R hR

end PaperIV.SplitCompleteExactValue

import PaperIV.FarRounding
import PaperIV.PhysicalCompletion

/-!
# From the mixed rounding layer to a physical partition

This adapter identifies an integral `FarRounding.Packing` with the literal
`K3`/`K4` packing used by the physical completion module.  Consequently any
future rounding theorem can be consumed by the physical route without a
second, informal conversion of its resource model.
-/

namespace PaperIV.FarRoundingToPhysical

open PaperIV.FarRounding
open PaperIV.Model
open PaperIV.PhysicalCompletion

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

theorem isPiece_of_isItem {K : Finset V} (h : FarRounding.IsItem G K) :
    Model.IsPiece G K := by
  refine ⟨?_, ?_⟩
  · intro a ha b hb hab
    exact h.1 a (by simpa using ha) b (by simpa using hb) hab
  · rcases h.2 with h3 | h4
    · exact ⟨Model.PieceKind.K3, by simpa using h3⟩
    · exact ⟨Model.PieceKind.K4, by simpa using h4⟩

/-- A mixed integral packing in the fractional-rounding language is a literal
physical `K3`/`K4` packing. -/
def toPhysicalPacking (P : FarRounding.Packing G) : PhysicalCompletion.IsK34Packing G P.pieces where
  pieces := fun K hK => isPiece_of_isItem (P.isItem K hK)
  edgeDisjoint := by
    intro K hK L hL hne
    simpa only [Model.pieceEdges, FarRounding.pairs] using P.edgeDisjoint K hK L hL hne
  big := fun K hK => (P.isItem K hK).2

/-- The physical completion of a rounded packing has exactly the gain predicted
by the original mixed-packing layer. -/
theorem completion_count_add_gain (P : FarRounding.Packing G) :
    (PhysicalCompletion.completion G P.pieces).card + P.gain = (Model.graphEdges G).card := by
  have h := PhysicalCompletion.card_completion_add_totalGain (toPhysicalPacking P)
  have hgain : ∀ K ∈ P.pieces, Model.gainOf K = FarRounding.gainOf K := by
    intro K hK
    rcases (P.isItem K hK).2 with h3 | h4
    · rw [Model.gainOf_of_card_three h3, FarRounding.gainOf_of_card_eq_three h3]
    · rw [Model.gainOf_of_card_four h4, FarRounding.gainOf_of_card_eq_four h4]
  unfold Model.totalGain at h
  rw [Finset.sum_congr rfl hgain] at h
  simpa only [FarRounding.Packing.gain] using h

/-- A rounded packing therefore produces a concrete exact physical partition. -/
theorem completion_isExactPartition (P : FarRounding.Packing G) :
    Model.IsExactPartition G (PhysicalCompletion.completion G P.pieces) :=
  PhysicalCompletion.isExactPartition_completion (toPhysicalPacking P).toIsPacking

/-- Every literal physical `K3`/`K4` packing is an integral packing for the
mixed fractional program. -/
def ofPhysicalPacking {Pieces : Finset (Finset V)}
    (hP : PhysicalCompletion.IsK34Packing G Pieces) : FarRounding.Packing G where
  pieces := Pieces
  isItem := by
    intro K hK
    refine ⟨?_, hP.big K hK⟩
    intro a ha b hb hab
    exact (hP.toIsPacking.pieces K hK).clique (by simpa using ha) (by simpa using hb) hab
  edgeDisjoint := by
    intro K hK L hL hne
    simpa only [FarRounding.pairs, Model.pieceEdges] using
      hP.toIsPacking.edgeDisjoint K hK L hL hne

theorem physical_gain_eq {Pieces : Finset (Finset V)}
    (hP : PhysicalCompletion.IsK34Packing G Pieces) :
    (ofPhysicalPacking hP).gain = Model.totalGain Pieces := by
  unfold FarRounding.Packing.gain Model.totalGain
  apply Finset.sum_congr rfl
  intro K hK
  rcases hP.big K hK with h3 | h4
  · rw [FarRounding.gainOf_of_card_eq_three h3, Model.gainOf_of_card_three h3]
  · rw [FarRounding.gainOf_of_card_eq_four h4, Model.gainOf_of_card_four h4]

/-- A rational primal-dual certificate dominates the gain of every physical
`K3`/`K4` packing in the literal partition model. -/
theorem physical_gain_le_certified {w : ℚ}
    (hcert : FarRounding.CertifiedFractionalOptimum G w)
    {Pieces : Finset (Finset V)} (hP : PhysicalCompletion.IsK34Packing G Pieces) :
    (Model.totalGain Pieces : ℚ) ≤ w := by
  have h := FarRounding.gain_le_of_certified hcert (ofPhysicalPacking hP)
  rw [physical_gain_eq hP] at h
  exact h

end PaperIV.FarRoundingToPhysical

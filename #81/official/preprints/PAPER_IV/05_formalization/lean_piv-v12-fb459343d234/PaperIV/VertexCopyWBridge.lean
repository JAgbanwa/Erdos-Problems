import PaperIV.VertexCopyGate
import PaperIV.FarRoundingToPhysical

/-!
# Exact `W*` ledger along gated fine-copy stabilization

The gated dynamics is expressed using the defect `F4 = |E| - W*`.  This
module records its exact, instance-free reformulation in terms of the mixed
fractional optimum `W*`: any increase in `W*` along a gated path is paid for
by the corresponding change in the edge count.  It does not claim an
integral packing or a near-regime certificate.
-/

namespace PaperIV.VertexCopyWBridge

open PaperIV.VertexCopyMonotone
open PaperIV.VertexCopyGate
open PaperIV.FarRoundingToPhysical
open PaperIV.PhysicalCompletion

variable {V : Type*} [Fintype V] [DecidableEq V]

open Classical in
/-- The mixed fractional optimum with a fixed classical edge-decidability
instance, so it is a function of the graph alone. -/
noncomputable def optVal' (G : SimpleGraph V) : ℝ :=
  @optVal V _ _ G (Classical.decRel _)

theorem optVal_congr_inst (G : SimpleGraph V) (i₁ i₂ : DecidableRel G.Adj) :
    @optVal V _ _ G i₁ = @optVal V _ _ G i₂ := by
  have h : i₁ = i₂ := Subsingleton.elim _ _
  subst h
  rfl

theorem optVal'_eq (G : SimpleGraph V) [inst : DecidableRel G.Adj] :
    optVal' G = optVal G :=
  optVal_congr_inst G _ _

/-- The definition of the gated defect as an exact edge-minus-optimum ledger. -/
theorem F4'_eq_edge_sub_optVal' (G : SimpleGraph V) :
    F4' G = (Nat.card G.edgeSet : ℝ) - optVal' G := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel _
  rw [F4'_eq G]
  unfold F4
  rw [← optVal'_eq G]
  rw [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card]

/-- A nondecreasing defect says precisely that the gain in the fractional
optimum is at most the change in the number of literal graph edges. -/
theorem optVal'_sub_le_edge_sub_of_F4'_le {G H : SimpleGraph V}
    (h : F4' G ≤ F4' H) :
    optVal' H - optVal' G ≤ (Nat.card H.edgeSet : ℝ) - (Nat.card G.edgeSet : ℝ) := by
  rw [F4'_eq_edge_sub_optVal', F4'_eq_edge_sub_optVal'] at h
  linarith

/-- The exact `W*` ledger available along every finite gated copy path. -/
theorem optVal'_sub_le_edge_sub_of_symmetrizationPath {G H : SimpleGraph V}
    (h : SymmetrizationPath G H) :
    optVal' H - optVal' G ≤ (Nat.card H.edgeSet : ℝ) - (Nat.card G.edgeSet : ℝ) :=
  optVal'_sub_le_edge_sub_of_F4'_le (F4'_le_of_symmetrizationPath h)

/-- Every literal physical `K3/K4` packing has gain at most the mixed
fractional optimum `W*`. -/
theorem physical_totalGain_le_optVal' {G : SimpleGraph V} {Pieces : Finset (Finset V)}
    (hP : IsK34Packing G Pieces) :
    (PaperIV.Model.totalGain Pieces : ℝ) ≤ optVal' G := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel _
  have h := le_optVal ((ofPhysicalPacking hP).toFrac (F := ℝ))
  rw [PaperIV.FarRounding.Packing.toFrac_value, physical_gain_eq hP] at h
  rw [optVal'_eq G]
  exact h

/-- Consequently `F4'` is a lower bound on the number of pieces in the
completion of every literal physical `K3/K4` packing.  This is deliberately a
one-sided statement: an upper bound needs a construction whose gain is close
to `W*`. -/
theorem F4'_le_completion_card_of_physical {G : SimpleGraph V} [DecidableRel G.Adj]
    {Pieces : Finset (Finset V)}
    (hP : IsK34Packing G Pieces) :
    F4' G ≤ ((completion G Pieces).card : ℝ) := by
  classical
  have hW := physical_totalGain_le_optVal' hP
  have hcount : (completion G Pieces).card + PaperIV.Model.totalGain Pieces = G.edgeFinset.card := by
    simpa [PaperIV.Model.graphEdges] using card_completion_add_totalGain hP
  have hE : G.edgeFinset.card = Nat.card G.edgeSet := by
    rw [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card]
  rw [hE] at hcount
  have hcountR : ((completion G Pieces).card : ℝ) + (PaperIV.Model.totalGain Pieces : ℝ)
      = (Nat.card G.edgeSet : ℝ) := by
    exact_mod_cast hcount
  rw [F4'_eq_edge_sub_optVal']
  have hgain : (Nat.card G.edgeSet : ℝ) - optVal' G ≤
      (Nat.card G.edgeSet : ℝ) - (PaperIV.Model.totalGain Pieces : ℝ) :=
    sub_le_sub_left hW _
  have hledger : (Nat.card G.edgeSet : ℝ) - (PaperIV.Model.totalGain Pieces : ℝ) =
      ((completion G Pieces).card : ℝ) := by
    linarith [hcountR]
  rw [← hledger]
  exact hgain

end PaperIV.VertexCopyWBridge

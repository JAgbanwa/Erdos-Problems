import PaperIV.Model
import PaperIV.FarRounding

/-!
# Adapter from the physical model to the far-rounding partition model

The near constructor is expressed with `Model.IsExactPartition`, whereas the
far/near assembly consumes `FarRounding.CliquePartition`.  This file proves the
literal conversion once, without changing pieces or cardinalities.
-/

namespace PaperIV.PhysicalToCliquePartition

open PaperIV.Model
open PaperIV.FarRounding

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A physical exact `K₂/K₃/K₄` partition is a clique partition with the same
literal family of pieces. -/
def ofExactPartition {P : Finset (Finset V)} (hP : IsExactPartition G P) :
    CliquePartition G where
  pieces := P
  isClique := fun K hK => (hP.pieces K hK).clique
  two_le_card := by
    intro K hK
    obtain ⟨kind, hkind⟩ := (hP.pieces K hK).kind
    cases kind <;> simp [PieceKind.size] at hkind <;> omega
  edgeDisjoint := by
    intro K hK L hL hne
    simpa [FarRounding.pairs, Model.pieceEdges] using hP.edgeDisjoint K hK L hL hne
  covers := by
    simpa [FarRounding.pairs, Model.pieceEdges, Model.coveredEdges, Model.graphEdges]
      using hP.covers

@[simp] theorem ofExactPartition_pieces {P : Finset (Finset V)}
    (hP : IsExactPartition G P) : (ofExactPartition hP).pieces = P := rfl

@[simp] theorem ofExactPartition_size {P : Finset (Finset V)}
    (hP : IsExactPartition G P) : (ofExactPartition hP).size = P.card := rfl

/-- Every physical piece already has order at most four. -/
theorem ofExactPartition_orderAtMost_four {P : Finset (Finset V)}
    (hP : IsExactPartition G P) : (ofExactPartition hP).OrderAtMost 4 := by
  intro K hK
  change K ∈ P at hK
  obtain ⟨kind, hkind⟩ := (hP.pieces K hK).kind
  cases kind <;> simp [PieceKind.size] at hkind <;> omega

/-- Package the conversion and a previously proved physical cardinality bound
in exactly the form used by `NearRegimeAt`. -/
theorem exists_cliquePartition_of_exactPartition_card_le {P : Finset (Finset V)}
    (hP : IsExactPartition G P) {q : ℕ} (hcard : P.card ≤ q) :
    ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ q := by
  exact ⟨ofExactPartition hP, ofExactPartition_orderAtMost_four hP, by simpa using hcard⟩

end PaperIV.PhysicalToCliquePartition

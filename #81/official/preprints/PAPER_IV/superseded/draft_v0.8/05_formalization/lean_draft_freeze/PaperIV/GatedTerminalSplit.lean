import PaperIV.VertexCopyGate
import PaperIV.TerminalSplitAdapter

/-!
# Gated fine-copy stabilization with a literal split terminal

This is the small interface joining the two certified sides of DV157–RD09:
the gated fine-copy dynamics terminates in a universal-core split graph, and
that terminal is literally the project's split-graph constructor on its core
and complement.  No packing or rounding is constructed here.
-/

namespace PaperIV.GatedTerminalSplit

open PaperIV.VertexCopyGate
open PaperIV.TerminalSplitAdapter

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Every finite chordal graph reaches, through gated fine copies, a literal
split graph without decreasing the mixed defect `F4'`. -/
theorem exists_split_terminal_symmetrizationPath (G : SimpleGraph V) (hG : PaperIV.IsChordal G) :
    ∃ H : SimpleGraph V, ∃ C : Set V,
      SymmetrizationPath G H ∧ PaperIV.IsChordal H ∧
      H = PaperIV.SplitUniformIncidence.splitGraph (coreFinset C) (hostFinset C) ∧
      F4' G ≤ F4' H := by
  obtain ⟨H, hreach, hHchord, hHterminal, hF4⟩ := exists_terminal_symmetrizationPath G hG
  obtain ⟨C, hsplit⟩ := eq_splitGraph_of_isUniversalCoreSplit H hHterminal
  exact ⟨H, C, hreach, hHchord, hsplit, hF4⟩

end PaperIV.GatedTerminalSplit

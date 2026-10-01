import PaperIV.VertexCopy
import PaperIV.CopySelector

/-!
# Structural selector for a fine DV157–RD09 copy

This is deliberately only the selector.  It turns the already proved
non-terminal simplicial pair into a legal one-vertex copy and transports
chordality.  It makes no numerical monotonicity claim.
-/

namespace PaperIV.VertexCopySelector

open PaperIV.ChordalBasics

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Data needed for one fine copy: copy the simplicial source onto the
nonadjacent target. -/
structure AdmissibleVertexCopy (G : SimpleGraph V) [DecidableRel G.Adj] where
  target : V
  source : V
  distinct : target ≠ source
  nonadjacent : ¬ G.Adj target source
  source_simplicial : IsSimplicial G source

/-- The selected fine copy remains chordal. -/
theorem chordal_after (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : AdmissibleVertexCopy G) (hG : PaperIV.IsChordal G) :
    PaperIV.IsChordal (PaperIV.VertexCopy.graph G s.target s.source) :=
  PaperIV.VertexCopy.isChordal_graph_of_isSimplicial G s.nonadjacent hG
    s.source_simplicial

/-- Outside the universal-core split terminal class, the existing terminal
selector supplies a fine-copy move with all literal side conditions. -/
theorem exists_admissibleVertexCopy (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : PaperIV.IsChordal G)
    (hnonsplit : ¬ PaperIV.TerminalSplit.IsUniversalCoreSplit G) :
    Nonempty (AdmissibleVertexCopy G) := by
  obtain ⟨x, y, hx, hy, hxy, hclasses⟩ :=
    PaperIV.TerminalSplit.exists_nonterminal_simplicial_pair G
      (PaperIV.CopySelector.chordalStructure_of_isChordal G hG) hnonsplit
  have hne : x ≠ y := by
    intro h
    apply hclasses
    simpa [h]
  exact ⟨⟨x, y, hne, hxy, hy⟩⟩

end PaperIV.VertexCopySelector

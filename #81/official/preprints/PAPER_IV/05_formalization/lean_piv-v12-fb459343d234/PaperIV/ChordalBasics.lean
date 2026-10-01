import PaperIV.ClassCopy
import PaperIV.ChordalStructure

/-! Minimal chordal vocabulary used by the copy-step selector. -/

namespace PaperIV.ChordalBasics

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! A vertex is simplicial when its open neighbourhood is a clique.  **Alias** of the canonical
`SimpleGraph.IsSimplicial` (`PaperIV/ChordalStructure.lean`), which was word-for-word identical;
`export` keeps the short name without creating a second constant. -/
export SimpleGraph (IsSimplicial)

theorem neighborFinset_isClique_of_simplicial
    (G : SimpleGraph V) [DecidableRel G.Adj] {v : V}
    (hv : IsSimplicial G v) : G.IsClique (G.neighborFinset v : Set V) := by
  simpa [IsSimplicial, SimpleGraph.coe_neighborFinset] using hv

end PaperIV.ChordalBasics

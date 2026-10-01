import PaperIV.EditMetric
import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Edit distance from a graph to a finite graph family

This module contains the graph-specific metric vocabulary shared by the two
stability mechanisms.  It is deliberately independent of vertex
symmetrization, barrier propagation, and first-entry arguments.
-/

namespace PaperIV.GraphFamilyDistance

open PaperIV.EditMetric

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A canonical finite edge support, independent of a caller's
`DecidableRel` instance. -/
noncomputable def graphEdgeSupport (X : SimpleGraph V) : Finset (Sym2 V) := by
  classical
  exact X.edgeSet.toFinset

@[simp] theorem graphEdgeSupport_eq_edgeFinset (X : SimpleGraph V)
    [DecidableRel X.Adj] : graphEdgeSupport X = X.edgeFinset := by
  ext e
  simp only [graphEdgeSupport, Set.mem_toFinset, SimpleGraph.mem_edgeSet,
    SimpleGraph.mem_edgeFinset]

/-- Normalized edit distance of a graph to one fixed nonempty family of edge
supports. -/
noncomputable def graphFamDistNorm
    (F : Finset (Finset (Sym2 V))) (hF : F.Nonempty)
    (X : SimpleGraph V) (scale : ℚ) : ℚ :=
  famDistNorm F hF (graphEdgeSupport X) scale

end PaperIV.GraphFamilyDistance

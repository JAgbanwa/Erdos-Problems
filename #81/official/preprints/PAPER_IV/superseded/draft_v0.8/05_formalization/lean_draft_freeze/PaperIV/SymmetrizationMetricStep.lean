import PaperIV.GraphFamilyDistance
import PaperIV.VertexCopy

/-!
# Metric cost of one symmetrization step

This module contains the metric estimates shared by every propagation
mechanism along a vertex-symmetrization path.  It deliberately contains no
minimal-index, first-entry, barrier, or descent argument.

The graph-specific statement is that one fine vertex copy changes at most
`|V| - 2` edges.  After normalization by `|V|^2`, the distance to any fixed
nonempty family of graph edge supports changes by at most `1 / |V|`.
-/

namespace PaperIV.SymmetrizationMetricStep

open PaperIV.EditMetric
open PaperIV.GraphFamilyDistance

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Pure arithmetic behind the normalized one-step estimate. -/
theorem normalized_sub_two_le_inv (n : ℕ) (hn : 2 ≤ n) :
    ((n - 2 : ℕ) : ℚ) / (n : ℚ) ^ 2 ≤ 1 / (n : ℚ) := by
  have hnq : (0 : ℚ) < n := by exact_mod_cast (show 0 < n by omega)
  have hsub : ((n - 2 : ℕ) : ℚ) ≤ n := by
    exact_mod_cast Nat.sub_le n 2
  calc
    ((n - 2 : ℕ) : ℚ) / (n : ℚ) ^ 2
        ≤ (n : ℚ) / (n : ℚ) ^ 2 := by gcongr
    _ = 1 / (n : ℚ) := by field_simp

/-- One fine vertex copy changes normalized edge support by at most `1 / |V|`. -/
theorem normalized_editDist_step
    (G : SimpleGraph V) [DecidableRel G.Adj] {target source : V}
    (hn : 2 ≤ Fintype.card V) (hne : target ≠ source)
    (hnadj : ¬ G.Adj target source) :
    (editDist G.edgeFinset
        (PaperIV.VertexCopy.graph G target source).edgeFinset : ℚ) /
        (Fintype.card V : ℚ) ^ 2 ≤ 1 / (Fintype.card V : ℚ) := by
  have hstep :
      (editDist G.edgeFinset
          (PaperIV.VertexCopy.graph G target source).edgeFinset : ℚ)
        ≤ ((Fintype.card V - 2 : ℕ) : ℚ) := by
    exact_mod_cast PaperIV.VertexCopy.editDist_edgeFinset_le G hne hnadj
  calc
    (editDist G.edgeFinset
        (PaperIV.VertexCopy.graph G target source).edgeFinset : ℚ) /
        (Fintype.card V : ℚ) ^ 2
        ≤ ((Fintype.card V - 2 : ℕ) : ℚ) /
            (Fintype.card V : ℚ) ^ 2 := by gcongr
    _ ≤ 1 / (Fintype.card V : ℚ) := normalized_sub_two_le_inv _ hn

/-- The normalized distance to any fixed nonempty graph family moves by at
most `1 / |V|` under one fine vertex copy. -/
theorem graphFamDistNorm_step
    (F : Finset (Finset (Sym2 V))) (hF : F.Nonempty)
    (hn : 2 ≤ Fintype.card V)
    (X : SimpleGraph V) {target source : V}
    (hne : target ≠ source) (hnadj : ¬ X.Adj target source) :
    graphFamDistNorm F hF X ((Fintype.card V : ℚ) ^ 2) -
        graphFamDistNorm F hF (PaperIV.VertexCopy.graph X target source)
          ((Fintype.card V : ℚ) ^ 2) ≤ 1 / (Fintype.card V : ℚ) := by
  classical
  have hlip := abs_sub_famDistNorm_le F hF X.edgeFinset
    (PaperIV.VertexCopy.graph X target source).edgeFinset
    (m := (Fintype.card V : ℚ) ^ 2) (by positivity)
  have hedit := normalized_editDist_step X hn hne hnadj
  have habs :
      |graphFamDistNorm F hF X ((Fintype.card V : ℚ) ^ 2) -
        graphFamDistNorm F hF (PaperIV.VertexCopy.graph X target source)
          ((Fintype.card V : ℚ) ^ 2)| ≤ 1 / (Fintype.card V : ℚ) := by
    change
      |famDistNorm F hF (graphEdgeSupport X) ((Fintype.card V : ℚ) ^ 2) -
        famDistNorm F hF
          (graphEdgeSupport (PaperIV.VertexCopy.graph X target source))
          ((Fintype.card V : ℚ) ^ 2)| ≤ 1 / (Fintype.card V : ℚ)
    rw [graphEdgeSupport_eq_edgeFinset, graphEdgeSupport_eq_edgeFinset]
    exact hlip.trans hedit
  exact (abs_le.mp habs).2

end PaperIV.SymmetrizationMetricStep

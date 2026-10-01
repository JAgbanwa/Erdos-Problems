import PaperIV.ColourClasses
import PaperIV.Model
import PaperIV.Vizing

/-!
# Line-graph colourings as literal proper edge colourings

This is the internal adapter needed by T01.  It does not invoke Vizing: any
proper colouring of the line graph gives a total colouring of the literal edge
finset whose classes are matchings.  A vendored proof of Vizing can therefore
be connected here without a change of resource model.
-/

namespace PaperIV.LineGraphColouring

open PaperIV.Model PaperIV.ColourClasses

variable {V Color : Type*} [Fintype V] [DecidableEq V] [Inhabited Color]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Extend a line-graph colouring to all unordered pairs; values off the
literal edge finset are irrelevant to `ProperOn`. -/
noncomputable def edgeColourOfLineGraph
    (C : (G.lineGraph).Coloring Color) : Sym2 V → Color := fun e =>
  if he : e ∈ graphEdges G then C ⟨e, (mem_graphEdges G).mp he⟩ else default

/-- A line-graph colouring is a proper colour assignment on literal graph
edges in the exact `ColourClasses.ProperOn` sense. -/
theorem properOn_of_lineGraph_colouring
    (C : (G.lineGraph).Coloring Color) :
    ProperOn (graphEdges G) (edgeColourOfLineGraph C) := by
  intro e he f hf hne hsame
  rw [Finset.disjoint_left]
  intro v hve hvf
  have hsame' : C ⟨e, (mem_graphEdges G).mp he⟩ =
      C ⟨f, (mem_graphEdges G).mp hf⟩ := by
    simpa [edgeColourOfLineGraph, he, hf] using hsame
  have hadj : (G.lineGraph).Adj ⟨e, (mem_graphEdges G).mp he⟩
      ⟨f, (mem_graphEdges G).mp hf⟩ := by
    rw [SimpleGraph.lineGraph_adj_iff_exists]
    refine ⟨fun h => hne (congrArg Subtype.val h), v, ?_, ?_⟩
    · exact Sym2.mem_toFinset.mp hve
    · exact Sym2.mem_toFinset.mp hvf
  exact (C.valid hadj) hsame'

/-- The local Vizing proof supplies the literal matching-class decomposition
needed at the first terminal-construction stage.  The colour on pairs outside
`graphEdges G` is deliberately immaterial. -/
noncomputable def vizingEdgeColour (G : SimpleGraph V) [DecidableRel G.Adj] :
    Sym2 V → Fin (G.maxDegree + 1) :=
  edgeColourOfLineGraph (Classical.choice (Vizing.lineGraph_colorable G))

theorem properOn_vizingEdgeColour (G : SimpleGraph V) [DecidableRel G.Adj] :
    ProperOn (graphEdges G) (vizingEdgeColour G) :=
  properOn_of_lineGraph_colouring (Classical.choice (Vizing.lineGraph_colorable G))

end PaperIV.LineGraphColouring

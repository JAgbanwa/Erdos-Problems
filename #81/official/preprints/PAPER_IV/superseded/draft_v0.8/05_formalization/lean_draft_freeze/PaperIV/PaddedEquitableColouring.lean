import PaperIV.EquitableKempe

/-!
# Equitable edge colouring on a padded palette

The original RD09 phase-I interface used exactly `Delta + 1` colours.  The
physical assignment, however, may need at least as many colour slots as
hosts.  This module closes that harmless interface mismatch: Vizing's
colouring is injected into any larger finite palette and the already proved
Kempe descent equitably recolours it on that same palette.
-/

namespace PaperIV.PaddedEquitableColouring

open PaperIV.Model PaperIV.ColourClasses PaperIV.EquitableEdgeColouring

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Vizing plus equitable Kempe recolouring on any palette of cardinality
`c >= Delta(G) + 1`. -/
noncomputable def equitableBoundedColouringOfCard
    (G : SimpleGraph V) [DecidableRel G.Adj] (c : ℕ)
    (hc : G.maxDegree + 1 ≤ c) :
    BoundedColouring (graphEdges G) (Fin c)
      (classCeiling (graphEdges G).card c) := by
  let initial : Sym2 V → Fin c := fun e =>
    Fin.castLE hc (PaperIV.LineGraphColouring.vizingEdgeColour G e)
  have hcast : Function.Injective (Fin.castLE hc) := Fin.castLE_injective hc
  have hproper : ProperOn (graphEdges G) initial := by
    intro e he d hd hed hsame
    apply PaperIV.LineGraphColouring.properOn_vizingEdgeColour G e he d hd hed
    exact hcast hsame
  have hcpos : 0 < c := lt_of_lt_of_le (Nat.zero_lt_succ G.maxDegree) hc
  letI : Nonempty (Fin c) := Fin.pos_iff_nonempty.mp hcpos
  let balanced := Classical.choose
    (PaperIV.EquitableKempe.exists_equitable_colouring initial hproper)
  have hbalanced := Classical.choose_spec
    (PaperIV.EquitableKempe.exists_equitable_colouring initial hproper)
  simpa using boundedColouringOfEquitable _ balanced hbalanced.1 hbalanced.2

/-- The canonical palette size used when `p` physical hosts must receive
distinct classes. -/
def paddedPaletteSize (G : SimpleGraph V) [DecidableRel G.Adj] (p : ℕ) : ℕ :=
  max p (G.maxDegree + 1)

theorem hostCount_le_paddedPaletteSize (G : SimpleGraph V) [DecidableRel G.Adj] (p : ℕ) :
    p ≤ paddedPaletteSize G p := Nat.le_max_left _ _

theorem vizingSize_le_paddedPaletteSize (G : SimpleGraph V) [DecidableRel G.Adj] (p : ℕ) :
    G.maxDegree + 1 ≤ paddedPaletteSize G p := Nat.le_max_right _ _

/-- Canonical injection of an arbitrary finite host type into the padded
palette. -/
noncomputable def hostColour (G : SimpleGraph V) [DecidableRel G.Adj]
    (I : Type*) [Fintype I] :
    I → Fin (paddedPaletteSize G (Fintype.card I)) := fun i =>
  Fin.castLE (hostCount_le_paddedPaletteSize G (Fintype.card I))
    (Fintype.equivFin I i)

theorem hostColour_injective (G : SimpleGraph V) [DecidableRel G.Adj]
    (I : Type*) [Fintype I] :
    Function.Injective (hostColour G I) := by
  intro a b hab
  exact (Fintype.equivFin I).injective
    (Fin.castLE_injective (hostCount_le_paddedPaletteSize G (Fintype.card I)) hab)

end PaperIV.PaddedEquitableColouring

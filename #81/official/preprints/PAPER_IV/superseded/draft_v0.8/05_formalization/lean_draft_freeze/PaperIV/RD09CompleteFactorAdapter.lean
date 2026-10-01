import PaperIV.LineGraphColouring
import PaperIV.RD09FactorCandidateAverage

/-!
# A uniform factor map for phase II

RD09-L2 only needs a proper factor colouring of the complete graph on the
root; it does not need the optimal parity-dependent number of factors.  Vizing
therefore supplies one uniform construction with exactly `p` available
colours for every nonempty root of order `p`.  This removes the even/odd
adapter from the closure path.
-/

namespace PaperIV.RD09CompleteFactorAdapter

open PaperIV.Model PaperIV.ColourClasses
open PaperIV.RD09FactorCandidateMoments PaperIV.RD09FactorCandidateAverage

variable {Z : Type*} [Fintype Z] [DecidableEq Z] [LinearOrder Z] [Nonempty Z]

/-- The Vizing colour of the unordered root edge represented by `e`. -/
noncomputable def completeFactor (e : Z × Z) : Fin (Fintype.card Z) :=
  Fin.castLE (Nat.succ_le_iff.mpr
    (SimpleGraph.completeGraph Z).maxDegree_lt_card_verts)
    (PaperIV.LineGraphColouring.vizingEdgeColour (SimpleGraph.completeGraph Z)
      s(e.1, e.2))

/-- Equal factor colours imply literal disjointness of distinct core bases. -/
theorem completeFactor_matching
    (e : Z × Z) (he : e ∈ corePairs Z)
    (e' : Z × Z) (he' : e' ∈ corePairs Z)
    (hee' : e ≠ e') (hfac : completeFactor e = completeFactor e')
    (x : Z) (hx : x = e.1 ∨ x = e.2) (hx' : x = e'.1 ∨ x = e'.2) : False := by
  have heLt := mem_corePairs.mp he
  have he'Lt := mem_corePairs.mp he'
  let K := SimpleGraph.completeGraph Z
  let de : Sym2 Z := s(e.1, e.2)
  let de' : Sym2 Z := s(e'.1, e'.2)
  have hde : de ∈ graphEdges K := by
    rw [mem_graphEdges, SimpleGraph.mem_edgeSet]
    exact ne_of_lt heLt
  have hde' : de' ∈ graphEdges K := by
    rw [mem_graphEdges, SimpleGraph.mem_edgeSet]
    exact ne_of_lt he'Lt
  have hdene : de ≠ de' := by
    intro hed
    apply hee'
    apply eq_of_two_common he he' (ne_of_lt heLt)
    · exact Or.inl rfl
    · exact Or.inr rfl
    · have hmem : e.1 ∈ de' := by
        rw [← hed]
        change e.1 ∈ s(e.1, e.2)
        rw [Sym2.mem_iff]
        exact Or.inl rfl
      dsimp [de'] at hmem
      rw [Sym2.mem_iff] at hmem
      exact hmem
    · have hmem : e.2 ∈ de' := by
        rw [← hed]
        change e.2 ∈ s(e.1, e.2)
        rw [Sym2.mem_iff]
        exact Or.inr rfl
      dsimp [de'] at hmem
      rw [Sym2.mem_iff] at hmem
      exact hmem
  have hcolour :
      PaperIV.LineGraphColouring.vizingEdgeColour K de =
        PaperIV.LineGraphColouring.vizingEdgeColour K de' := by
    exact Fin.castLE_injective _ hfac
  have hdisj := PaperIV.LineGraphColouring.properOn_vizingEdgeColour K
    de hde de' hde' hdene hcolour
  have hxmem : x ∈ de.toFinset := Sym2.mem_toFinset.mpr (by
    change x ∈ s(e.1, e.2)
    rw [Sym2.mem_iff]
    exact hx)
  have hxmem' : x ∈ de'.toFinset := Sym2.mem_toFinset.mpr (by
    change x ∈ s(e'.1, e'.2)
    rw [Sym2.mem_iff]
    exact hx')
  exact Finset.disjoint_left.mp hdisj hxmem hxmem'

/-- The complete factor map in precisely the field shape consumed by
`IsFactorCandidateData`. -/
theorem completeFactor_facMatching :
    ∀ e ∈ corePairs Z, ∀ e' ∈ corePairs Z, e ≠ e' →
      completeFactor e = completeFactor e' →
      ∀ x : Z, (x = e.1 ∨ x = e.2) → (x = e'.1 ∨ x = e'.2) → False := by
  exact completeFactor_matching

end PaperIV.RD09CompleteFactorAdapter

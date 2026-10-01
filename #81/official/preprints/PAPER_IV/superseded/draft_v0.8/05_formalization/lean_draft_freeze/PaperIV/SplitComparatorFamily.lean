import PaperIV.GraphFamilyDistance
import PaperIV.SplitUniformIncidence

/-! # The finite family of all labelled complete-split comparators

The stability argument must minimize over a fixed family.  This module makes
that family literal and recovers a core from every minimizing member.
-/

namespace PaperIV.SplitComparatorFamily

open PaperIV.GraphFamilyDistance PaperIV.EditMetric

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Edge supports of all complete-split graphs on the fixed labelled vertex
type.  A core is allowed to be any subset of the ambient vertices. -/
noncomputable def allSplitSupports : Finset (Finset (Sym2 V)) := by
  classical
  exact Finset.univ.powerset.image fun C : Finset V =>
    graphEdgeSupport
      (PaperIV.SplitUniformIncidence.splitGraph C (Finset.univ \ C))

theorem allSplitSupports_nonempty :
    (allSplitSupports (V := V)).Nonempty := by
  classical
  refine ⟨graphEdgeSupport
      (PaperIV.SplitUniformIncidence.splitGraph (∅ : Finset V) Finset.univ), ?_⟩
  rw [allSplitSupports, Finset.mem_image]
  exact ⟨∅, Finset.mem_powerset.mpr (Finset.empty_subset _), by simp⟩

theorem mem_allSplitSupports_iff {A : Finset (Sym2 V)} :
    A ∈ allSplitSupports (V := V) ↔
      ∃ C : Finset V, A = graphEdgeSupport
        (PaperIV.SplitUniformIncidence.splitGraph C (Finset.univ \ C)) := by
  classical
  rw [allSplitSupports, Finset.mem_image]
  constructor
  · rintro ⟨C, _hC, rfl⟩
    exact ⟨C, rfl⟩
  · rintro ⟨C, rfl⟩
    exact ⟨C, Finset.mem_powerset.mpr (Finset.subset_univ C), rfl⟩

/-- The normalized distance to the split family is attained by a literal
complete-split comparator and its literal core. -/
theorem exists_closest_split (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ C : Finset V,
      famDist (allSplitSupports (V := V)) allSplitSupports_nonempty G.edgeFinset =
        editDist G.edgeFinset
          (graphEdgeSupport
            (PaperIV.SplitUniformIncidence.splitGraph C (Finset.univ \ C))) := by
  classical
  obtain ⟨A, hA, hdist⟩ := exists_mem_eq_famDist
    (allSplitSupports (V := V)) allSplitSupports_nonempty G.edgeFinset
  obtain ⟨C, rfl⟩ := mem_allSplitSupports_iff.mp hA
  exact ⟨C, hdist⟩

/-- A strict normalized-distance bound yields a literal split comparator with
the corresponding unnormalized edit bound. -/
theorem exists_split_editDist_lt (G : SimpleGraph V) [DecidableRel G.Adj]
    {eps scale : ℚ} (hscale : 0 < scale)
    (hdist : PaperIV.GraphFamilyDistance.graphFamDistNorm
      (allSplitSupports (V := V)) allSplitSupports_nonempty G scale < eps) :
    ∃ C : Finset V,
      (editDist G.edgeFinset
        (graphEdgeSupport
          (PaperIV.SplitUniformIncidence.splitGraph C (Finset.univ \ C))) : ℚ)
          < eps * scale := by
  classical
  obtain ⟨C, hclosest⟩ := exists_closest_split G
  refine ⟨C, ?_⟩
  rw [PaperIV.GraphFamilyDistance.graphFamDistNorm,
    PaperIV.EditMetric.famDistNorm,
    PaperIV.GraphFamilyDistance.graphEdgeSupport_eq_edgeFinset] at hdist
  rw [hclosest] at hdist
  exact (div_lt_iff₀ hscale).mp hdist

end PaperIV.SplitComparatorFamily

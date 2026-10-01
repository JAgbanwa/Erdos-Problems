import PaperIV.Model

/-!
# Union of resource-disjoint physical packings

The two RD09 phases are constructed separately.  This module supplies the
literal assembly step: once their pieces have no cross-phase resource conflict,
their union is again a physical packing and its covered edge set is the union
of the two covered edge sets.
-/

namespace PaperIV.PackingUnion

open PaperIV.Model

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

omit [Fintype V] [DecidableRel G.Adj] in
/-- Two literal packings can be assembled when every cross-phase pair has
disjoint physical edge resources. -/
theorem isPacking_union
    {P Q : Finset (Finset V)}
    (hP : IsPacking G P) (hQ : IsPacking G Q)
    (hcross : ∀ s ∈ P, ∀ t ∈ Q, Disjoint (pieceEdges s) (pieceEdges t)) :
    IsPacking G (P ∪ Q) := by
  refine ⟨?_, ?_⟩
  · intro s hs
    rcases Finset.mem_union.mp hs with hs | hs
    · exact hP.pieces s hs
    · exact hQ.pieces s hs
  · intro s hs t ht hne
    rcases Finset.mem_union.mp hs with hs | hs <;>
      rcases Finset.mem_union.mp ht with ht | ht
    · exact hP.edgeDisjoint s hs t ht hne
    · exact hcross s hs t ht
    · exact (hcross t ht s hs).symm
    · exact hQ.edgeDisjoint s hs t ht hne

omit [Fintype V] in
/-- The resource set covered by an assembled packing is the literal union of
the resource sets covered by its phases. -/
theorem coveredEdges_union (P Q : Finset (Finset V)) :
    coveredEdges (P ∪ Q) = coveredEdges P ∪ coveredEdges Q := by
  ext e
  simp only [mem_coveredEdges, Finset.mem_union]
  constructor
  · rintro ⟨s, hs, he⟩
    rcases hs with hs | hs
    · exact Or.inl ⟨s, hs, he⟩
    · exact Or.inr ⟨s, hs, he⟩
  · rintro (⟨s, hs, he⟩ | ⟨s, hs, he⟩)
    · exact ⟨s, Or.inl hs, he⟩
    · exact ⟨s, Or.inr hs, he⟩

omit [Fintype V] in
/-- If each phase covers its designated resource set, the assembled packing
covers the union of those sets. -/
theorem coveredEdges_union_eq
    {P Q : Finset (Finset V)} {EP EQ : Finset (Sym2 V)}
    (hP : coveredEdges P = EP) (hQ : coveredEdges Q = EQ) :
    coveredEdges (P ∪ Q) = EP ∪ EQ := by
  rw [coveredEdges_union, hP, hQ]

/-- If the two phase resource sets together are all graph edges, their
resource-disjoint union is an exact physical clique partition. -/
theorem isExactPartition_of_union
    {P Q : Finset (Finset V)}
    (hP : IsPacking G P) (hQ : IsPacking G Q)
    (hcross : ∀ s ∈ P, ∀ t ∈ Q, Disjoint (pieceEdges s) (pieceEdges t))
    (hcovers : coveredEdges P ∪ coveredEdges Q = graphEdges G) :
    IsExactPartition G (P ∪ Q) :=
  ⟨isPacking_union hP hQ hcross, by rw [coveredEdges_union, hcovers]⟩

omit [Fintype V] [DecidableRel G.Adj] in
/-- It is enough to verify resource disjointness at the phase level: every
piece resource lies in its phase's covered resource set. -/
theorem isPacking_union_of_disjoint_covered
    {P Q : Finset (Finset V)}
    (hP : IsPacking G P) (hQ : IsPacking G Q)
    (hcovered : Disjoint (coveredEdges P) (coveredEdges Q)) :
    IsPacking G (P ∪ Q) := by
  apply isPacking_union hP hQ
  intro s hs t ht
  rw [Finset.disjoint_left]
  intro e hes het
  apply (Finset.disjoint_left.mp hcovered)
  · exact mem_coveredEdges.mpr ⟨s, hs, hes⟩
  · exact mem_coveredEdges.mpr ⟨t, ht, het⟩

omit [Fintype V] in
/-- The gain ledger adds across syntactically disjoint phase families.  The
RD09 constructor proves this disjointness from its phase labels. -/
theorem totalGain_union {P Q : Finset (Finset V)} (hdisj : Disjoint P Q) :
    totalGain (P ∪ Q) = totalGain P + totalGain Q := by
  unfold totalGain
  exact Finset.sum_union hdisj

end PaperIV.PackingUnion

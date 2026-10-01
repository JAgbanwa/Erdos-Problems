import PaperIV.Model

/-! Completion of a physical `K3`/`K4` packing by its uncovered `K2` edges. -/

namespace PaperIV.PhysicalCompletion

open Finset PaperIV.Model

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def edgePiece (e : Sym2 V) : Finset V := e.toFinset

variable {G}

omit [Fintype V] in
theorem card_edgePiece {e : Sym2 V} (he : ¬ e.IsDiag) : (edgePiece e).card = 2 :=
  Sym2.card_toFinset_of_not_isDiag e he

omit [Fintype V] in
theorem pieceEdges_edgePiece {e : Sym2 V} (he : ¬ e.IsDiag) :
    pieceEdges (edgePiece e) = {e} := by
  induction e with
  | _ a b =>
    have hne : a ≠ b := by simpa [Sym2.isDiag_iff_proj_eq] using he
    have hset : edgePiece s(a, b) = ({a, b} : Finset V) := by simp [edgePiece, Sym2.toFinset_mk_eq]
    rw [hset]
    ext f
    induction f with
    | _ x y =>
      simp only [mem_pieceEdges_mk, Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff]
      constructor
      · rintro ⟨hx, hy, hxy⟩
        rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp_all
      · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> exact ⟨by simp, by simp, by simp [hne, hne.symm]⟩

theorem isPiece_edgePiece {e : Sym2 V} (he : e ∈ graphEdges G) : IsPiece G (edgePiece e) := by
  have hnd : ¬ e.IsDiag := not_isDiag_of_mem_graphEdges G he
  refine ⟨?_, ⟨PieceKind.K2, by simpa using card_edgePiece hnd⟩⟩
  induction e with
  | _ a b =>
    have hadj : G.Adj a b := by simpa [graphEdges] using he
    have hset : edgePiece s(a, b) = ({a, b} : Finset V) := by simp [edgePiece, Sym2.toFinset_mk_eq]
    rw [hset]
    simpa using (SimpleGraph.isClique_pair (G := G) (a := a) (b := b)).mpr fun _ => hadj

omit [Fintype V] in
theorem gainOf_edgePiece {e : Sym2 V} (he : ¬ e.IsDiag) : gainOf (edgePiece e) = 0 :=
  gainOf_of_card_two (card_edgePiece he)

omit [Fintype V] in
theorem edgePiece_injOn {e f : Sym2 V} (he : ¬ e.IsDiag) (hf : ¬ f.IsDiag)
    (h : edgePiece e = edgePiece f) : e = f := by
  have : ({e} : Finset (Sym2 V)) = {f} := by
    rw [← pieceEdges_edgePiece he, ← pieceEdges_edgePiece hf, h]
  simpa using this

variable (G)

def uncoveredEdges (P : Finset (Finset V)) : Finset (Sym2 V) := graphEdges G \ coveredEdges P
def completion (P : Finset (Finset V)) : Finset (Finset V) :=
  P ∪ (uncoveredEdges G P).image edgePiece

variable {G}

theorem mem_uncoveredEdges {P : Finset (Finset V)} {e : Sym2 V} :
    e ∈ uncoveredEdges G P ↔ e ∈ graphEdges G ∧ e ∉ coveredEdges P := by simp [uncoveredEdges]

theorem not_isDiag_of_mem_uncoveredEdges {P : Finset (Finset V)} {e : Sym2 V}
    (he : e ∈ uncoveredEdges G P) : ¬ e.IsDiag :=
  not_isDiag_of_mem_graphEdges G (mem_uncoveredEdges.mp he).1

theorem mem_completion {P : Finset (Finset V)} {s : Finset V} :
    s ∈ completion G P ↔ s ∈ P ∨ ∃ e ∈ uncoveredEdges G P, edgePiece e = s := by simp [completion]

theorem coveredEdges_completion {P : Finset (Finset V)} (hP : IsPacking G P) :
    coveredEdges (completion G P) = graphEdges G := by
  ext e
  simp only [mem_coveredEdges, mem_completion]
  constructor
  · rintro ⟨s, hs | ⟨f, hf, rfl⟩, hes⟩
    · exact hP.coveredEdges_subset (mem_coveredEdges.mpr ⟨s, hs, hes⟩)
    · rw [pieceEdges_edgePiece (not_isDiag_of_mem_uncoveredEdges hf), Finset.mem_singleton] at hes
      subst hes
      exact (mem_uncoveredEdges.mp hf).1
  · intro he
    by_cases hcov : e ∈ coveredEdges P
    · obtain ⟨s, hs, hes⟩ := mem_coveredEdges.mp hcov
      exact ⟨s, Or.inl hs, hes⟩
    · have hu : e ∈ uncoveredEdges G P := mem_uncoveredEdges.mpr ⟨he, hcov⟩
      exact ⟨edgePiece e, Or.inr ⟨e, hu, rfl⟩,
        by rw [pieceEdges_edgePiece (not_isDiag_of_mem_uncoveredEdges hu)]; simp⟩

theorem isExactPartition_completion {P : Finset (Finset V)} (hP : IsPacking G P) :
    IsExactPartition G (completion G P) := by
  refine ⟨⟨?_, ?_⟩, coveredEdges_completion hP⟩
  · intro s hs
    rcases mem_completion.mp hs with hs' | ⟨e, he, rfl⟩
    · exact hP.pieces s hs'
    · exact isPiece_edgePiece (mem_uncoveredEdges.mp he).1
  · intro s hs t ht hst
    rcases mem_completion.mp hs with hs' | ⟨e, he, rfl⟩ <;>
      rcases mem_completion.mp ht with ht' | ⟨f, hf, rfl⟩
    · exact hP.edgeDisjoint s hs' t ht' hst
    · rw [pieceEdges_edgePiece (not_isDiag_of_mem_uncoveredEdges hf), Finset.disjoint_singleton_right]
      intro hmem
      exact (mem_uncoveredEdges.mp hf).2 (mem_coveredEdges.mpr ⟨s, hs', hmem⟩)
    · rw [pieceEdges_edgePiece (not_isDiag_of_mem_uncoveredEdges he), Finset.disjoint_singleton_left]
      intro hmem
      exact (mem_uncoveredEdges.mp he).2 (mem_coveredEdges.mpr ⟨t, ht', hmem⟩)
    · rw [pieceEdges_edgePiece (not_isDiag_of_mem_uncoveredEdges he),
        pieceEdges_edgePiece (not_isDiag_of_mem_uncoveredEdges hf), Finset.disjoint_singleton]
      intro hef
      exact hst (by rw [hef])

variable (G) in
structure IsK34Packing (P : Finset (Finset V)) : Prop extends IsPacking G P where
  big : ∀ s ∈ P, s.card = 3 ∨ s.card = 4

omit [Fintype V] [DecidableRel G.Adj] in
theorem IsK34Packing.card_ne_two {P : Finset (Finset V)} (hP : IsK34Packing G P)
    {s : Finset V} (hs : s ∈ P) : s.card ≠ 2 := by
  rcases hP.big s hs with h | h <;> omega

theorem disjoint_image_edgePiece {P : Finset (Finset V)} (hP : IsK34Packing G P) :
    Disjoint P ((uncoveredEdges G P).image edgePiece) := by
  rw [Finset.disjoint_right]
  rintro s hs hsP
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hs
  exact hP.card_ne_two hsP (card_edgePiece (not_isDiag_of_mem_uncoveredEdges he))

theorem card_image_edgePiece (P : Finset (Finset V)) :
    ((uncoveredEdges G P).image edgePiece).card = (uncoveredEdges G P).card := by
  refine Finset.card_image_of_injOn ?_
  intro e he f hf hef
  exact edgePiece_injOn (not_isDiag_of_mem_uncoveredEdges he) (not_isDiag_of_mem_uncoveredEdges hf) hef

theorem card_completion {P : Finset (Finset V)} (hP : IsK34Packing G P) :
    (completion G P).card = P.card + (uncoveredEdges G P).card := by
  rw [completion, Finset.card_union_of_disjoint (disjoint_image_edgePiece hP), card_image_edgePiece]

theorem totalGain_completion {P : Finset (Finset V)} (hP : IsK34Packing G P) :
    totalGain (completion G P) = totalGain P := by
  rw [completion, totalGain, Finset.sum_union (disjoint_image_edgePiece hP)]
  have hzero : ∑ s ∈ (uncoveredEdges G P).image edgePiece, gainOf s = 0 := by
    refine Finset.sum_eq_zero ?_
    intro s hs
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hs
    exact gainOf_edgePiece (not_isDiag_of_mem_uncoveredEdges he)
  rw [hzero, totalGain, Nat.add_zero]

theorem card_completion_add_totalGain {P : Finset (Finset V)} (hP : IsK34Packing G P) :
    (completion G P).card + totalGain P = (graphEdges G).card := by
  have h := (isExactPartition_completion hP.toIsPacking).card_add_totalGain
  rwa [totalGain_completion hP] at h

theorem totalGain_le_and_card_completion_eq {P : Finset (Finset V)} (hP : IsK34Packing G P) :
    totalGain P ≤ (graphEdges G).card ∧ (completion G P).card = (graphEdges G).card - totalGain P := by
  have h := card_completion_add_totalGain hP
  omega

end PaperIV.PhysicalCompletion

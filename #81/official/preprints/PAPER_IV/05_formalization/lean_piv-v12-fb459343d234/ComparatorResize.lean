import OptimalCoreDistance
import PaperIV.ClassCopyEdit

/-! Resizing a defective split comparator. This changes the comparator, not
the actual clique root in G retained by the stability theorem. -/
namespace PaperIV.SublinearResearch
open Finset PaperIV.DefectComparatorGraph PaperIV.EditMetric PaperIV.ClassCopyEdit
open scoped symmDiff

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem exists_resize_core (C D : Finset V) (hd : Disjoint C D)
    (t : ℕ) (ht : t ≤ (univ \ D).card) :
    ∃ C' : Finset V, Disjoint C' D ∧ C'.card = t ∧
      ((C ∆ C').card : ℚ) = |(C.card : ℚ)-t| := by
  classical
  have hCU : C ⊆ univ \ D := by
    intro x hx
    exact mem_sdiff.mpr ⟨mem_univ _,fun hD => disjoint_left.mp hd hx hD⟩
  by_cases hsmall : t ≤ C.card
  · obtain ⟨C',hsub,hcard⟩ := exists_subset_card_eq hsmall
    have hsym : C ∆ C' = C \ C' := by
      ext x
      simp only [mem_symmDiff,mem_sdiff]
      have hx := @hsub x
      tauto
    refine ⟨C',Disjoint.mono_left hsub hd,hcard,?_⟩
    rw [hsym,card_sdiff_of_subset hsub,hcard,Nat.cast_sub hsmall,
      abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hsmall))]
  · obtain ⟨C',hsub,hsubU,hcard⟩ := exists_subsuperset_card_eq hCU (by omega) ht
    have hd' : Disjoint C' D := by
      apply disjoint_left.mpr
      intro x hx hD
      exact (mem_sdiff.mp (hsubU hx)).2 hD
    have hsym : C ∆ C' = C' \ C := by
      ext x
      simp only [mem_symmDiff,mem_sdiff]
      have hx := @hsub x
      tauto
    refine ⟨C',hd',hcard,?_⟩
    rw [hsym,card_sdiff_of_subset hsub,hcard,Nat.cast_sub (by omega),
      abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast (show C.card ≤ t by omega)))]
    ring

/-- Every changed edge touches a vertex whose core/exterior role changed. -/
theorem comparator_resize_edit_le (C C' D : Finset V) :
    editDist (defSplitGraph C D (univ \ (C ∪ D))).edgeFinset
      (defSplitGraph C' D (univ \ (C' ∪ D))).edgeFinset ≤
      (C ∆ C').card*Fintype.card V := by
  classical
  apply (card_le_card (show
      (defSplitGraph C D (univ \ (C ∪ D))).edgeFinset ∆
        (defSplitGraph C' D (univ \ (C' ∪ D))).edgeFinset ⊆ incident (C ∆ C') from ?_)).trans
      (card_incident_le _)
  intro e he
  induction e using Sym2.ind with
  | _ x y =>
    by_cases hx : x ∈ C ∆ C'
    · exact mem_biUnion.mpr ⟨x,hx,by simp [PaperIV.ClassCopyEdit.star]⟩
    by_cases hy : y ∈ C ∆ C'
    · exact mem_biUnion.mpr ⟨y,hy,by simp [PaperIV.ClassCopyEdit.star]⟩
    have hxC : x ∈ C ↔ x ∈ C' := by simp only [mem_symmDiff] at hx; tauto
    have hyC : y ∈ C ↔ y ∈ C' := by simp only [mem_symmDiff] at hy; tauto
    have hadj : (defSplitGraph C D (univ \ (C ∪ D))).Adj x y ↔
        (defSplitGraph C' D (univ \ (C' ∪ D))).Adj x y := by
      simp only [defSplitGraph_adj_iff,mem_union,mem_sdiff,mem_univ,true_and,hxC,hyC]
    have hmem : s(x,y) ∈ (defSplitGraph C D (univ \ (C ∪ D))).edgeFinset ↔
        s(x,y) ∈ (defSplitGraph C' D (univ \ (C' ∪ D))).edgeFinset := by
      simpa only [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] using hadj
    rcases mem_symmDiff.mp he with h | h
    · exact False.elim (h.2 (hmem.mp h.1))
    · exact False.elim (h.2 (hmem.mpr h.1))

theorem exists_optimal_comparator_near_root {n s : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {C D H : Finset (Fin n)} (hR : E32.IsDefectRoot G s C D H)
    {j : ℕ} (hjs : s ≤ j) (hjn : j ≤ n)
    (hj : PaperIV.ExtremalClassification.OptimalCore (n+s) j) :
    ∃ T : SimpleGraph (Fin n), ∃ _inst : DecidableRel T.Adj,
      E32.IsAdmissibleExtremal T s ∧
        (editDist G.edgeFinset T.edgeFinset : ℚ) ≤
          E32.rootEdit G C D H + (n : ℚ)*|(C.card : ℚ)+s-j| := by
  classical
  have ht : j-s ≤ (univ \ D).card := by
    rw [card_sdiff_of_subset (subset_univ _),card_univ,Fintype.card_fin,hR.card_def]
    omega
  obtain ⟨C',hd',hcard,hchange⟩ := exists_resize_core C D hR.disjCD (j-s) ht
  let H' := univ \ (C' ∪ D)
  let T := defSplitGraph C' D H'
  have hH : H = univ \ (C ∪ D) := by
    ext x
    simp only [mem_sdiff,mem_univ,true_and,mem_union]
    constructor
    · intro hx
      exact fun h => h.elim (fun hc => disjoint_left.mp hR.disjCH hc hx)
        (fun hd => disjoint_left.mp hR.disjDH hd hx)
    · intro hx
      rcases hR.cover x with hc | hd | hh
      · exact False.elim (hx (Or.inl hc))
      · exact False.elim (hx (Or.inr hd))
      · exact hh
  have hnear : E32.NearestCore (n+s) (C'.card+s) := by
    rw [hcard,Nat.sub_add_cancel hjs]
    exact (E32.nearestCore_iff_optimalCore _ _).mpr hj
  refine ⟨T,inferInstance,⟨C',D,H',hd',?_,?_,?_,hR.card_def,rfl,by simpa using hnear⟩,?_⟩
  · exact Disjoint.mono_left subset_union_left disjoint_sdiff
  · exact Disjoint.mono_left subset_union_right disjoint_sdiff
  · intro x
    by_cases hc : x ∈ C'
    · exact Or.inl hc
    by_cases hd : x ∈ D
    · exact Or.inr (Or.inl hd)
    · exact Or.inr (Or.inr (by simp [H',hc,hd]))
  · have he := comparator_resize_edit_le C C' D
    rw [← hH] at he
    have htri := editDist_triangle G.edgeFinset (defSplitGraph C D H).edgeFinset T.edgeFinset
    have heq : ((C ∆ C').card : ℚ) = |(C.card : ℚ)+s-j| := by
      rw [hchange,Nat.cast_sub hjs]
      congr 1
      ring
    have heQ : (editDist (defSplitGraph C D H).edgeFinset T.edgeFinset : ℚ) ≤
        (C ∆ C').card*n := by
      have heN : editDist (defSplitGraph C D H).edgeFinset T.edgeFinset ≤ (C ∆ C').card*n := by
        simpa only [T,H',Fintype.card_fin] using he
      exact_mod_cast heN
    have htQ : (editDist G.edgeFinset T.edgeFinset : ℚ) ≤
        E32.rootEdit G C D H + (editDist (defSplitGraph C D H).edgeFinset T.edgeFinset : ℚ) := by
      exact_mod_cast htri
    rw [heq] at heQ
    nlinarith only [heQ,htQ]

end PaperIV.SublinearResearch

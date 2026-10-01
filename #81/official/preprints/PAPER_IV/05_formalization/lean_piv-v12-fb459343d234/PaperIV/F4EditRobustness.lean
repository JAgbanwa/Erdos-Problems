import PaperIV.VertexCopyWBridge
import PaperIV.EditMetric

/-! # Edit robustness of the mixed fractional defect

This module proves the deletion half needed for the final near-H1 entry
argument.  It works directly with the real optimum used by `F4'`.
-/

namespace PaperIV.F4EditRobustness

open Finset PaperIV.FarRounding
open PaperIV.VertexCopyMonotone
open scoped symmDiff

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj]

theorem isItem_mono (hGH : G ≤ H) {K : Finset V} (hK : IsItem G K) :
    IsItem H K := by
  refine ⟨?_, hK.2⟩
  intro a ha b hb hab
  exact hGH (hK.1 a ha b hb hab)

theorem items_subset (hGH : G ≤ H) : items G ⊆ items H := by
  intro K hK
  exact mem_items.mpr (isItem_mono hGH (mem_items.mp hK))

/-- Restrict a real fractional packing to a spanning subgraph. -/
noncomputable def restrictMono (hGH : G ≤ H) (x : FracPacking H ℝ) :
    FracPacking G ℝ where
  weight := x.weight
  weight_nonneg := x.weight_nonneg
  capacity := by
    intro e he
    have hsub := items_subset hGH
    calc
      ∑ K ∈ items G, (if e ∈ pairs K then x.weight K else 0)
          ≤ ∑ K ∈ items H, (if e ∈ pairs K then x.weight K else 0) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg hsub
            intro K _ _
            split_ifs
            · exact x.weight_nonneg K
            · exact le_rfl
      _ ≤ 1 := x.capacity e (by
        rw [SimpleGraph.mem_edgeFinset] at he ⊢
        exact SimpleGraph.edgeSet_mono hGH he)

theorem restrictMono_value (hGH : G ≤ H) (x : FracPacking H ℝ) :
    (restrictMono hGH x).value =
      ∑ K ∈ items G, gainF ℝ K * x.weight K := rfl

/-- A packing of a spanning subgraph extends by zero to the ambient graph. -/
noncomputable def liftMono (hGH : G ≤ H) (x : FracPacking G ℝ) :
    FracPacking H ℝ where
  weight := fun K => if K ∈ items G then x.weight K else 0
  weight_nonneg := by
    intro K
    split_ifs
    · exact x.weight_nonneg K
    · exact le_rfl
  capacity := by
    intro e heH
    classical
    by_cases heG : e ∈ G.edgeFinset
    · have hsub := items_subset hGH
      calc
        ∑ K ∈ items H,
            (if e ∈ pairs K then (if K ∈ items G then x.weight K else 0) else 0)
            = ∑ K ∈ items G,
                (if e ∈ pairs K then (if K ∈ items G then x.weight K else 0) else 0) := by
                  symm
                  apply Finset.sum_subset hsub
                  intro K _ hKG
                  simp [hKG]
        _ = ∑ K ∈ items G, (if e ∈ pairs K then x.weight K else 0) := by
              apply Finset.sum_congr rfl
              intro K hK
              simp [hK]
        _ ≤ 1 := x.capacity e heG
    · have hzero : ∀ K ∈ items H,
          (if e ∈ pairs K then (if K ∈ items G then x.weight K else 0) else 0) = 0 := by
        intro K hKH
        by_cases hKG : K ∈ items G
        · have hpairs := pairs_subset_edgeFinset (mem_items.mp hKG)
          have hep : e ∉ pairs K := fun hep => heG (hpairs hep)
          simp [hep]
        · simp [hKG]
      rw [Finset.sum_congr rfl hzero]
      simp

theorem liftMono_value (hGH : G ≤ H) (x : FracPacking G ℝ) :
    (liftMono hGH x).value = x.value := by
  classical
  rw [FracPacking.value, FracPacking.value]
  have hsub := items_subset hGH
  symm
  calc
    ∑ K ∈ items G, gainF ℝ K * x.weight K =
        ∑ K ∈ items G, gainF ℝ K *
          (if K ∈ items G then x.weight K else 0) := by
            apply Finset.sum_congr rfl
            intro K hK
            simp [hK]
    _ = ∑ K ∈ items H, gainF ℝ K *
          (if K ∈ items G then x.weight K else 0) := by
            apply Finset.sum_subset hsub
            intro K _ hKG
            simp [hKG]

theorem optVal_mono (hGH : G ≤ H) : optVal G ≤ optVal H := by
  obtain ⟨x, hx⟩ := exists_fracPacking_value_eq_optVal G
  have h := le_optVal (liftMono hGH x)
  rwa [liftMono_value, hx] at h

/-- Every item lost on passing to a subgraph touches a deleted real edge. -/
theorem lost_item_meets_removedEdges (hGH : G ≤ H) {K : Finset V}
    (hKH : K ∈ items H) (hKG : K ∉ items G) :
    ∃ e ∈ H.edgeFinset \ G.edgeFinset, e ∈ pairs K := by
  classical
  have hitemH := mem_items.mp hKH
  have hnclique : ¬ (∀ a ∈ K, ∀ b ∈ K, a ≠ b → G.Adj a b) := by
    intro hc
    exact hKG (mem_items.mpr ⟨hc, hitemH.2⟩)
  push_neg at hnclique
  obtain ⟨a, ha, b, hb, hab, hnG⟩ := hnclique
  refine ⟨s(a, b), Finset.mem_sdiff.mpr ⟨?_, ?_⟩, ?_⟩
  · rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact hitemH.1 a ha b hb hab
  · simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hnG
  · exact mk_mem_pairs.mpr ⟨ha, hb, hab⟩

theorem gainF_nonneg_real {K : Finset V} (hK : IsItem H K) :
    (0 : ℝ) ≤ gainF ℝ K := by
  rcases hK.2 with h3 | h4
  · rw [gainF, h3]
    norm_num
  · rw [gainF, h4]
    have hc : Nat.choose 4 2 = 6 := by decide
    rw [hc]
    norm_num

theorem gainF_le_five_real {K : Finset V} (hK : IsItem H K) :
    gainF ℝ K ≤ 5 := by
  rcases hK.2 with h3 | h4
  · rw [gainF, h3]
    norm_num
  · rw [gainF, h4]
    have hc : Nat.choose 4 2 = 6 := by decide
    rw [hc]
    norm_num

/-- Real version of the incidence budget: a family whose every item touches a
member of `B` has total mass at most `|B|`. -/
theorem sum_weight_le_card_of_meets_real (x : FracPacking H ℝ)
    (B : Finset (Sym2 V)) (hB : B ⊆ H.edgeFinset)
    (D : Finset (Finset V)) (hD : D ⊆ items H)
    (hmeet : ∀ K ∈ D, ∃ e ∈ B, e ∈ pairs K) :
    ∑ K ∈ D, x.weight K ≤ (B.card : ℝ) := by
  classical
  have hrow : ∀ K ∈ D,
      x.weight K ≤ ∑ e ∈ B, (if e ∈ pairs K then x.weight K else 0) := by
    intro K hK
    obtain ⟨e, heB, heK⟩ := hmeet K hK
    have hone : (if e ∈ pairs K then x.weight K else 0) = x.weight K := by simp [heK]
    calc
      x.weight K = (if e ∈ pairs K then x.weight K else 0) := hone.symm
      _ ≤ ∑ f ∈ B, (if f ∈ pairs K then x.weight K else 0) := by
        apply Finset.single_le_sum (fun f _ => by
          by_cases hf : f ∈ pairs K
          · simp [hf, x.weight_nonneg K]
          · simp [hf]) heB
  calc
    ∑ K ∈ D, x.weight K
        ≤ ∑ K ∈ D, ∑ e ∈ B, (if e ∈ pairs K then x.weight K else 0) :=
          Finset.sum_le_sum hrow
    _ = ∑ e ∈ B, ∑ K ∈ D, (if e ∈ pairs K then x.weight K else 0) :=
          Finset.sum_comm
    _ ≤ ∑ e ∈ B, ∑ K ∈ items H,
          (if e ∈ pairs K then x.weight K else 0) := by
          apply Finset.sum_le_sum
          intro e he
          apply Finset.sum_le_sum_of_subset_of_nonneg hD
          intro K _ _
          split_ifs
          · exact x.weight_nonneg K
          · exact le_rfl
    _ ≤ ∑ _e ∈ B, (1 : ℝ) :=
          Finset.sum_le_sum fun e he => x.capacity e (hB he)
    _ = (B.card : ℝ) := by simp

/-- The value discarded by deleting edges is at most five per deleted edge. -/
theorem lost_value_le_five_removed (hGH : G ≤ H) (x : FracPacking H ℝ) :
    x.value - (restrictMono hGH x).value ≤
      5 * ((H.edgeFinset \ G.edgeFinset).card : ℝ) := by
  classical
  let D := items H \ items G
  have hGsubH := items_subset hGH
  have hdiff : x.value - (restrictMono hGH x).value =
      ∑ K ∈ D, gainF ℝ K * x.weight K := by
    rw [FracPacking.value, restrictMono_value]
    rw [← Finset.sum_sdiff hGsubH]
    ring
  have hmass : ∑ K ∈ D, x.weight K ≤
      ((H.edgeFinset \ G.edgeFinset).card : ℝ) := by
    apply sum_weight_le_card_of_meets_real x (H.edgeFinset \ G.edgeFinset)
    · exact Finset.sdiff_subset
    · exact Finset.sdiff_subset
    · intro K hK
      exact lost_item_meets_removedEdges hGH
        (Finset.mem_sdiff.mp hK).1 (Finset.mem_sdiff.mp hK).2
  rw [hdiff]
  calc
    ∑ K ∈ D, gainF ℝ K * x.weight K
        ≤ ∑ K ∈ D, 5 * x.weight K := by
          apply Finset.sum_le_sum
          intro K hK
          exact mul_le_mul_of_nonneg_right
            (gainF_le_five_real (mem_items.mp (Finset.mem_sdiff.mp hK).1))
            (x.weight_nonneg K)
    _ = 5 * ∑ K ∈ D, x.weight K := by rw [Finset.mul_sum]
    _ ≤ 5 * ((H.edgeFinset \ G.edgeFinset).card : ℝ) := by linarith

/-- Deleting `t` edges decreases the mixed fractional optimum by at most
`5t`. -/
theorem optVal_le_add_five_removed (hGH : G ≤ H) :
    optVal H ≤ optVal G + 5 * ((H.edgeFinset \ G.edgeFinset).card : ℝ) := by
  obtain ⟨x, hx⟩ := exists_fracPacking_value_eq_optVal H
  have hrestricted := le_optVal (restrictMono hGH x)
  have hlost := lost_value_le_five_removed hGH x
  rw [hx] at hlost
  linarith

/-- The mixed fractional optimum is five-Lipschitz in labelled edit distance. -/
theorem abs_sub_optVal_le_five_editDist (G H : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] :
    |optVal G - optVal H| ≤
      5 * (PaperIV.EditMetric.editDist G.edgeFinset H.edgeFinset : ℝ) := by
  classical
  let J : SimpleGraph V := G ⊓ H
  letI : DecidableRel J.Adj := Classical.decRel _
  let EJ : Finset (Sym2 V) := @SimpleGraph.edgeFinset V J J.fintypeEdgeSet
  have hJG : J ≤ G := by
    dsimp [J]
    exact inf_le_left
  have hJH : J ≤ H := by
    dsimp [J]
    exact inf_le_right
  have hGdel := optVal_le_add_five_removed hJG
  have hHdel := optVal_le_add_five_removed hJH
  change optVal G ≤ optVal J + 5 * ((G.edgeFinset \ EJ).card : ℝ) at hGdel
  change optVal H ≤ optVal J + 5 * ((H.edgeFinset \ EJ).card : ℝ) at hHdel
  have hJGopt := optVal_mono hJG
  have hJHopt := optVal_mono hJH
  have hGsub : G.edgeFinset \ EJ ⊆
      G.edgeFinset ∆ H.edgeFinset := by
    intro e he
    rw [Finset.mem_sdiff] at he
    have heG := he.1
    have heH : e ∉ H.edgeFinset := by
      intro heH
      apply he.2
      simpa [EJ, J, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using
        And.intro heG heH
    simp [Finset.mem_symmDiff, heG, heH]
  have hHsub : H.edgeFinset \ EJ ⊆
      G.edgeFinset ∆ H.edgeFinset := by
    intro e he
    rw [Finset.mem_sdiff] at he
    have heH := he.1
    have heG : e ∉ G.edgeFinset := by
      intro heG
      apply he.2
      simpa [EJ, J, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using
        And.intro heG heH
    simp [Finset.mem_symmDiff, heG, heH]
  have hGcard : ((G.edgeFinset \ EJ).card : ℝ) ≤
      PaperIV.EditMetric.editDist G.edgeFinset H.edgeFinset := by
    unfold PaperIV.EditMetric.editDist
    exact_mod_cast Finset.card_le_card hGsub
  have hHcard : ((H.edgeFinset \ EJ).card : ℝ) ≤
      PaperIV.EditMetric.editDist G.edgeFinset H.edgeFinset := by
    unfold PaperIV.EditMetric.editDist
    exact_mod_cast Finset.card_le_card hHsub
  rw [abs_le]
  constructor
  · have hstep : optVal H ≤ optVal G +
        5 * (PaperIV.EditMetric.editDist G.edgeFinset H.edgeFinset : ℝ) := by
      have hm := mul_le_mul_of_nonneg_left hHcard (show (0 : ℝ) ≤ 5 by norm_num)
      have hmid : optVal J + 5 * ((H.edgeFinset \ EJ).card : ℝ) ≤
          optVal G + 5 * ((H.edgeFinset \ EJ).card : ℝ) := by
        exact add_le_add hJGopt (le_refl _)
      exact hHdel.trans (hmid.trans (add_le_add (le_refl _) hm))
    linarith
  · have hstep : optVal G ≤ optVal H +
        5 * (PaperIV.EditMetric.editDist G.edgeFinset H.edgeFinset : ℝ) := by
      have hm := mul_le_mul_of_nonneg_left hGcard (show (0 : ℝ) ≤ 5 by norm_num)
      have hmid : optVal J + 5 * ((G.edgeFinset \ EJ).card : ℝ) ≤
          optVal H + 5 * ((G.edgeFinset \ EJ).card : ℝ) := by
        exact add_le_add hJHopt (le_refl _)
      exact hGdel.trans (hmid.trans (add_le_add (le_refl _) hm))
    linarith

/-- The mixed defect is six-Lipschitz in labelled edit distance. -/
theorem abs_sub_F4'_le_six_editDist (G H : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] :
    |PaperIV.VertexCopyGate.F4' G - PaperIV.VertexCopyGate.F4' H| ≤
      6 * (PaperIV.EditMetric.editDist G.edgeFinset H.edgeFinset : ℝ) := by
  have hopt := abs_sub_optVal_le_five_editDist G H
  have hGHnat := Finset.card_le_card_sdiff_add_card
    (s := G.edgeFinset) (t := H.edgeFinset)
  have hHGnat := Finset.card_le_card_sdiff_add_card
    (s := H.edgeFinset) (t := G.edgeFinset)
  have hGHsub : G.edgeFinset \ H.edgeFinset ⊆ G.edgeFinset ∆ H.edgeFinset := by
    intro e he
    simp only [Finset.mem_sdiff] at he
    simp [Finset.mem_symmDiff, he.1, he.2]
  have hHGsub : H.edgeFinset \ G.edgeFinset ⊆ G.edgeFinset ∆ H.edgeFinset := by
    intro e he
    simp only [Finset.mem_sdiff] at he
    simp [Finset.mem_symmDiff, he.1, he.2]
  have hGHcard : ((G.edgeFinset.card : ℕ) : ℝ) ≤
      H.edgeFinset.card + PaperIV.EditMetric.editDist G.edgeFinset H.edgeFinset := by
    have hs := Finset.card_le_card hGHsub
    have ht : G.edgeFinset.card ≤
        H.edgeFinset.card + (G.edgeFinset ∆ H.edgeFinset).card := by omega
    unfold PaperIV.EditMetric.editDist
    exact_mod_cast ht
  have hHGcard : ((H.edgeFinset.card : ℕ) : ℝ) ≤
      G.edgeFinset.card + PaperIV.EditMetric.editDist G.edgeFinset H.edgeFinset := by
    have hs := Finset.card_le_card hHGsub
    have ht : H.edgeFinset.card ≤
        G.edgeFinset.card + (G.edgeFinset ∆ H.edgeFinset).card := by omega
    unfold PaperIV.EditMetric.editDist
    exact_mod_cast ht
  rw [PaperIV.VertexCopyGate.F4'_eq G, PaperIV.VertexCopyGate.F4'_eq H,
    F4, F4, abs_le] at ⊢
  rw [abs_le] at hopt
  constructor <;> nlinarith

end PaperIV.F4EditRobustness

import A4S1.IndepAllMain
import PaperIV.DefectComparatorLower
import PaperIV.DefectComparatorRootedDefect
import PaperIV.SplitCompleteSharpLower
import PaperIV.E11K10

/-! Public conclusions for the v1.0 increment. Thresholds may depend on the
fixed rooted defect. The lower bound allows cliques of arbitrary order. -/
namespace PaperIV.DefectSharpPublication

open Finset PaperIV.FarRounding PaperIV.RootedSimplicialDefect
  PaperIV.DefectTargetArithmetic PaperIV.DefectComparatorGraph

theorem rooted_defect_eventual (s : ℕ) :
    ∃ N, ∀ n, N ≤ n → ∀ G : SimpleGraph (Fin n), ∀ [DecidableRel G.Adj],
      RootedDefectAt G s →
      ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ defectTarget s n :=
  A4S1.IndepAll.a4Sharp_all_indep s

theorem comparator_baseline_eq_target (n s : ℕ) (hn : 2 * s + 2 ≤ n) :
    let k := (n + s + 1) / 3
    k * (n - k) - (k - s).choose 2 = defectTarget s n := by
  dsimp
  set k := (n + s + 1) / 3 with hk
  have hsk : s ≤ k := by omega
  have hkn : k ≤ n := by omega
  have hpos : 1 ≤ k - s := by omega
  have hkpos : 1 ≤ k := by omega
  have hcrit := SplitCompleteSharpLower.critical_baseline_eq_targetSize (n + s) (by omega)
  change k * (n + s - k) - k.choose 2 = PaperIV.FarRounding.targetSize (n + s) at hcrit
  have hchoose : k.choose 2 + (s + 1).choose 2 =
      (k - s).choose 2 + k * s := by
    have h1 := PaperIV.SplitUniformIncidence.mul_pred_eq_two_mul_choose_two k
    have h2 := PaperIV.SplitUniformIncidence.mul_pred_eq_two_mul_choose_two (k - s)
    have h3 := PaperIV.SplitUniformIncidence.mul_pred_eq_two_mul_choose_two (s + 1)
    have hks : k - s + s = k := Nat.sub_add_cancel hsk
    have hkp : k - 1 + 1 = k := Nat.sub_add_cancel hkpos
    have hsp : k - s - 1 + 1 = k - s := Nat.sub_add_cancel hpos
    simp only [Nat.add_sub_cancel] at h3
    nlinarith
  have hprod : k * (n + s - k) = k * (n - k) + k * s := by
    have : n + s - k = n - k + s := by omega
    rw [this, Nat.mul_add]
  unfold defectTarget
  rw [← hcrit, Nat.sub_sub, hchoose, hprod]
  omega

private def initial (n a : ℕ) : Finset (Fin n) :=
  univ.filter fun x => x.val < a

private theorem card_initial (n a : ℕ) (ha : a ≤ n) : (initial n a).card = a := by
  have himg : (initial n a).image Fin.val = range a := by
    ext m
    simp only [initial, mem_image, mem_filter, mem_univ, true_and, mem_range]
    constructor
    · rintro ⟨x, hx, rfl⟩; exact hx
    · intro hm; exact ⟨⟨m, by omega⟩, hm, rfl⟩
  calc (initial n a).card = ((initial n a).image Fin.val).card :=
      (card_image_of_injective _ Fin.val_injective).symm
    _ = a := by rw [himg, card_range]

theorem exists_defect_lower_witness (s n : ℕ) (hn : 2 * s + 2 ≤ n) :
    ∃ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
      RootedDefectAt G s ∧ ∀ Q : CliquePartition G, defectTarget s n ≤ Q.size := by
  classical
  let k := (n + s + 1) / 3
  have hsk : s ≤ k := by dsimp [k]; omega
  have hkn : k ≤ n := by dsimp [k]; omega
  let C := initial n (k - s)
  let U := initial n k
  let D := U \ C
  let H := Uᶜ
  have hCU : C ⊆ U := by
    intro x hx
    simp only [C, U, initial, mem_filter, mem_univ, true_and] at *
    omega
  have hc : C.card = k - s := card_initial n _ (by omega)
  have hu : U.card = k := card_initial n _ hkn
  have hd : D.card = s := by rw [card_sdiff_of_subset hCU, hu, hc]; omega
  have hh : H.card = n - k := by simp [H, card_compl, hu]
  have hCD : Disjoint C D := disjoint_sdiff_self_right
  have hCH : Disjoint C H := disjoint_compl_right.mono_left hCU
  have hDH : Disjoint D H := disjoint_compl_right.mono_left sdiff_subset
  have hcover : ∀ x : Fin n, x ∈ C ∨ x ∈ D ∨ x ∈ H := by
    intro x
    simp only [D, H, mem_sdiff, mem_compl]
    tauto
  refine ⟨defSplitGraph C D H, inferInstance,
    DefectComparatorRootedDefect.rootedDefectAt_defSplitGraph hCD hDH hCH hcover
      (by omega), ?_⟩
  intro Q
  have hl := DefectComparatorLower.cliquePartition_size_ge_defect_baseline hCD hDH
    (disjoint_union_left.mpr ⟨hCH, hDH⟩) Q
  rw [hc, hd, hh, Nat.sub_add_cancel hsk] at hl
  rw [comparator_baseline_eq_target n s hn] at hl
  exact hl

/-- The sharp eventual maximum, with an unrestricted lower bound. -/
theorem rooted_defect_maximum (s : ℕ) :
    ∃ N, ∀ n, N ≤ n →
      (∀ G : SimpleGraph (Fin n), ∀ [DecidableRel G.Adj], RootedDefectAt G s →
        ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ defectTarget s n) ∧
      (∃ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj), RootedDefectAt G s ∧
        ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size = defectTarget s n ∧
          ∀ R : CliquePartition G, Q.size ≤ R.size) := by
  obtain ⟨N, hN⟩ := rooted_defect_eventual s
  refine ⟨max N (2 * s + 2), fun n hn => ?_⟩
  have hlarge : N ≤ n := (le_max_left _ _).trans hn
  refine ⟨hN n hlarge, ?_⟩
  obtain ⟨G, inst, hG, hl⟩ := exists_defect_lower_witness s n ((le_max_right _ _).trans hn)
  letI := inst
  obtain ⟨Q, hQ4, hQ⟩ := hN n hlarge G hG
  have heq : Q.size = defectTarget s n := le_antisymm hQ (hl Q)
  exact ⟨G, inst, hG, Q, hQ4, heq, fun R => heq.trans_le (hl R)⟩

theorem order_three_insufficient (n : ℕ) (hn : n % 6 = 4)
    (Q : CliquePartition (⊤ : SimpleGraph (Fin n))) (hQ : Q.OrderAtMost 3) :
    targetSize n < Q.size := E11.targetSize_lt_of_orderAtMost_three_aux n hn Q hQ

end PaperIV.DefectSharpPublication

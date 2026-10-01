import ExplicitFixedStability

/-! Discrete localization to the full set of optimal core sizes. The second
maximizer in the residue-one case must not be discarded. -/
namespace PaperIV.SublinearResearch
open PaperIV PaperIV.FarRounding PaperIV.ExtremalClassification

theorem optimal_core_distance_sq (m k : ℕ) (hm : 2 ≤ m) :
    ∃ j : ℕ, OptimalCore m j ∧
      ((k : ℚ)-j)^2 ≤ (PaperIV.targetSize m : ℚ)-splitBaseline m k := by
  let q := (m+1)/3
  let r := (m+1)%3
  have hr : r < 3 := by dsimp [r]; omega
  have hdiv : m+1 = 3*q+r := by dsimp [q,r]; omega
  have hdivq : (m : ℚ)+1 = 3*q+r := by exact_mod_cast hdiv
  have hqle : q ≤ m := by dsimp [q]; omega
  have hqout : q ≤ m-q := by dsimp [q]; omega
  have hc : q.choose 2 ≤ q*(m-q) := by
    rw [Nat.choose_two_right]
    exact (Nat.div_le_self _ _).trans (Nat.mul_le_mul_left q (by omega))
  have hbase : splitBaseline (m : ℚ) q = (PaperIV.targetSize m : ℚ) := by
    have h := PaperIV.SplitCompleteSharpLower.critical_baseline_eq_targetSize m hm
    change q*(m-q)-q.choose 2 = PaperIV.targetSize m at h
    have h' := congrArg (fun x : ℕ => (x : ℚ)) h
    push_cast [Nat.cast_sub hc, Nat.cast_sub hqle, Nat.cast_choose_two] at h'
    exact h'
  by_cases ht : r = 2 ∧ q < k
  · refine ⟨q+1,Or.inr ⟨by dsimp [r] at ht; omega,rfl⟩,?_⟩
    have hkg : (q : ℚ)+1 ≤ k := by exact_mod_cast ht.2
    have hrq : (r : ℚ) = 2 := by exact_mod_cast ht.1
    rw [← hbase]
    unfold splitBaseline
    push_cast
    nlinarith [sq_nonneg ((k : ℚ)-q-1)]
  · refine ⟨q,Or.inl rfl,?_⟩
    rw [← hbase]
    unfold splitBaseline
    have hint : 0 ≤ ((k : ℚ)-q)*((k : ℚ)-q-1) ∧
        0 ≤ ((k : ℚ)-q)*((k : ℚ)-q+1) := by
      rcases lt_trichotomy k q with hk | hk | hk
      · have hkq : (k : ℚ)+1 ≤ q := by exact_mod_cast hk
        constructor <;> nlinarith
      · subst k; norm_num
      · have hkq : (q : ℚ)+1 ≤ k := by exact_mod_cast hk
        constructor <;> nlinarith
    interval_cases r <;> norm_num at hdivq ht
    · nlinarith only [hdivq,hint.2]
    · nlinarith only [hdivq,hint.1]
    · have hkq : (k : ℚ) ≤ q := by exact_mod_cast (show k ≤ q by omega)
      nlinarith [sq_nonneg ((k : ℚ)-q)]

/-- The selected optimum is close to the actual root furnished by fixed-defect
stability. No assertion that the original root already has optimal size. -/
theorem fixed_defect_optimal_size_distance (s n : ℕ)
    (hn : FixedExplicit.stabilityThreshold s ≤ n)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : PaperIV.RootedSimplicialDefect.RootedDefectAt G s)
    (δ : ℚ) (hδ0 : 0 ≤ δ) (hδ : δ ≤ FixedExplicit.stabilityGamma s*(n : ℚ)^2)
    (hlow : ∀ Q : CliquePartition G, Q.OrderAtMost 4 →
      (PaperIV.DefectTargetArithmetic.defectTarget s n : ℚ)-δ ≤ Q.size) :
    ∃ C D H : Finset (Fin n), E32.IsDefectRoot G s C D H ∧
      (E32.rootEdit G C D H : ℚ) ≤ FixedExplicit.stabilityConstant s*δ ∧
      ∃ j : ℕ, OptimalCore (n+s) j ∧
        ((C.card : ℚ)+s-j)^2 ≤ (1+4*FixedExplicit.stabilityConstant s)*δ := by
  obtain ⟨C,D,H,hR,he,hlo,hhi⟩ := FixedExplicit.fixed_defect_edit_and_size_explicit s n hn G hG δ hδ0 hδ hlow
  have hsum := hR.card_sum
  have htwo := hR.two_le
  have hm : 2 ≤ n+s := by omega
  obtain ⟨j,hj,hjbound⟩ := optimal_core_distance_sq (n+s) (C.card+s) hm
  have hid := E32.rootBaseline_add_choose C.card s H.card hR.core_le_hosts
  have hc : C.card.choose 2 ≤ (C.card+s)*H.card := by
    rw [Nat.choose_two_right]
    exact (Nat.div_le_self _ _).trans (Nat.mul_le_mul (by omega) (by have := hR.core_le_hosts; omega))
  have hc' : (C.card+s).choose 2 ≤ (C.card+s)*(H.card+s) := by
    rw [Nat.choose_two_right]
    exact (Nat.div_le_self _ _).trans (Nat.mul_le_mul_left _ (by have := hR.core_le_hosts; omega))
  have htarget := E32.targetSize_ge_choose n s (by omega)
  have hidq := congrArg (fun x : ℕ => (x : ℚ)) hid
  push_cast [Nat.cast_sub hc,Nat.cast_sub hc',Nat.cast_choose_two] at hidq
  have hsumq : (C.card : ℚ)+s+H.card = n := by exact_mod_cast hsum
  have heq : (PaperIV.DefectTargetArithmetic.defectTarget s n : ℚ)-E32.rootBaseline C D H =
      (PaperIV.targetSize (n+s) : ℚ)-splitBaseline (n+s) (C.card+s) := by
    unfold PaperIV.DefectTargetArithmetic.defectTarget E32.rootBaseline
    rw [hR.card_def]
    rw [Nat.cast_sub htarget,Nat.cast_sub hc]
    push_cast
    unfold splitBaseline
    simp only [Nat.cast_choose_two, Nat.cast_add, Nat.cast_one,
      PaperIV.FarRounding.targetSize, PaperIV.targetSize]
    nlinarith only [hidq,hsumq]
  refine ⟨C,D,H,hR,he,j,hj,?_⟩
  rw [heq] at hhi
  push_cast at hjbound
  exact hjbound.trans hhi

end PaperIV.SublinearResearch

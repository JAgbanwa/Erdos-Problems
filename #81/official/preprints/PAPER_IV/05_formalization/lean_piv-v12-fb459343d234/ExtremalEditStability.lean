import ComparatorResize

/-! Quantitative edit stability to the exact optimal-size extremal family.
The original real clique root is retained upstream; the resized comparator's
core is not asserted to remain a clique in the original graph.
This is the quantitative comparison relevant to arXiv:2609.20871v1, Cor. 5.5.
-/
namespace PaperIV.SublinearResearch
open PaperIV.FarRounding PaperIV.RootedSimplicialDefect PaperIV.DefectTargetArithmetic
open PaperIV.EditMetric

theorem fixed_defect_exact_extremal_edit (s n : ℕ)
    (hn : FixedExplicit.stabilityThreshold s ≤ n)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : RootedDefectAt G s)
    (δ : ℚ) (hδ0 : 0 ≤ δ) (hδ : δ ≤ FixedExplicit.stabilityGamma s*(n : ℚ)^2)
    (hlow : ∀ Q : CliquePartition G, Q.OrderAtMost 4 → (defectTarget s n : ℚ)-δ ≤ Q.size) :
    ∃ T : SimpleGraph (Fin n), ∃ _inst : DecidableRel T.Adj,
      E32.IsAdmissibleExtremal T s ∧
        (editDist G.edgeFinset T.edgeFinset : ℝ) ≤
          (FixedExplicit.stabilityConstant s : ℝ)*δ + (n : ℝ)*
            Real.sqrt ((1+4*(FixedExplicit.stabilityConstant s : ℝ))*(δ : ℝ)) := by
  classical
  obtain ⟨C,D,H,hR,he,j,hj,hjsq⟩ := fixed_defect_optimal_size_distance s n hn G hG δ hδ0 hδ hlow
  have hnsmall : 3*s+8 ≤ n := by
    unfold FixedExplicit.stabilityThreshold FixedExplicit.deletionBase at hn
    omega
  have hjs : s ≤ j := by
    unfold PaperIV.ExtremalClassification.OptimalCore at hj
    omega
  have hjn : j ≤ n := by
    unfold PaperIV.ExtremalClassification.OptimalCore at hj
    omega
  obtain ⟨T,inst,hT,hbound⟩ := exists_optimal_comparator_near_root hR hjs hjn hj
  letI := inst
  refine ⟨T,inst,hT,?_⟩
  have hsq : |(C.card : ℝ)+s-j|^2 ≤
      (1+4*(FixedExplicit.stabilityConstant s : ℝ))*(δ : ℝ) := by
    rw [sq_abs]
    exact_mod_cast hjsq
  have hsqrt := Real.le_sqrt_of_sq_le hsq
  have heR : (E32.rootEdit G C D H : ℝ) ≤
      (FixedExplicit.stabilityConstant s : ℝ)*δ := by exact_mod_cast he
  have hbR : (editDist G.edgeFinset T.edgeFinset : ℝ) ≤
      E32.rootEdit G C D H + (n : ℝ)*|(C.card : ℝ)+s-j| := by exact_mod_cast hbound
  exact hbR.trans (add_le_add heR (mul_le_mul_of_nonneg_left hsqrt (by positivity)))

end PaperIV.SublinearResearch

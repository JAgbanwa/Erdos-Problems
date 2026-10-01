import E34.L11Main

/-!
The explicit E34 removal bound is linear in the defect at each fixed accuracy.
This module exposes the quantifiers needed for defects s(n)=o(n), without
substituting a growing defect in the fixed-s sharp-threshold theorem.
-/
namespace PaperIV.SublinearResearch
open PaperIV.RootedSimplicialDefect

private theorem ratio_budget {n s p : ℚ} (hn : 0 < n) (hs : 0 ≤ s)
    (hp : 0 ≤ p) (h : s ≤ n / (16*p+1)) : 8*s*p < n := by
  have hd : 0 < 16*p+1 := by linarith
  have hm := (le_div_iff₀ hd).mp h
  nlinarith only [hm, hn, hs]

noncomputable def editDefectRatio (ε : ℚ) : ℚ :=
  1 / (16 * (E34.mVq ε : ℚ) ^ (E34.mVq ε + 1) + 1)

theorem editDefectRatio_pos (ε : ℚ) : 0 < editDefectRatio ε := by
  unfold editDefectRatio
  positivity

theorem edit_close_of_small_defect_ratio (ε : ℚ) (hε : 0 < ε)
    {n s : ℕ} (hn : max (E34.mVq ε) 1 ≤ n)
    (hs : (s : ℚ) ≤ editDefectRatio ε * n)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : RootedDefectAt G s) :
    ∃ H : SimpleGraph (Fin n), H.IsChordal ∧
      ((symmDiff G.edgeSet H.edgeSet).ncard : ℚ) ≤ ε * (n : ℚ)^2 := by
  have hn1 : 1 ≤ n := (le_max_right _ _).trans hn
  have hnm : E34.mVq ε ≤ n := (le_max_left _ _).trans hn
  let p : ℕ := (E34.mVq ε) ^ (E34.mVq ε + 1)
  have hpq : (p : ℚ) = (E34.mVq ε : ℚ) ^ (E34.mVq ε + 1) := by simp [p]
  have hden : (0 : ℚ) < 16 * (p : ℚ) + 1 := by positivity
  have hs' : (s : ℚ) ≤ (n : ℚ) / (16 * (p : ℚ) + 1) := by
    rw [editDefectRatio, ← hpq, div_mul_eq_mul_div, one_mul] at hs
    exact hs
  have hnq : (0 : ℚ) < n := by exact_mod_cast (show 0 < n by omega)
  have hp0 : (0 : ℚ) ≤ p := Nat.cast_nonneg p
  have hs0 : (0 : ℚ) ≤ s := Nat.cast_nonneg s
  have hstrict : (8 : ℚ) * s * p < n := ratio_budget hnq hs0 hp0 hs'
  have hstrictN : 8 * s * p < n := by exact_mod_cast hstrict
  have hthreshold : E34.NeditE s ε ≤ n := by
    unfold E34.NeditE E34.NeditV
    apply max_le hnm
    exact max_le hnm (by dsimp [p] at hstrictN; omega)
  exact E34.editApproxExplicit_final s ε hε n hthreshold G hG

theorem uniform_chordal_edit (ε : ℚ) (hε : 0 < ε) :
    ∃ θ : ℚ, 0 < θ ∧ ∃ N : ℕ, ∀ n s : ℕ, N ≤ n →
      (s : ℚ) ≤ θ * n → ∀ G : SimpleGraph (Fin n), ∀ [DecidableRel G.Adj],
      RootedDefectAt G s →
      ∃ H : SimpleGraph (Fin n), H.IsChordal ∧
        ((symmDiff G.edgeSet H.edgeSet).ncard : ℚ) ≤ ε * (n : ℚ)^2 :=
  ⟨editDefectRatio ε, editDefectRatio_pos ε, max (E34.mVq ε) 1,
    fun _ _ hn hs G _ hG => edit_close_of_small_defect_ratio ε hε hn hs G hG⟩

end PaperIV.SublinearResearch
#print axioms PaperIV.SublinearResearch.uniform_chordal_edit

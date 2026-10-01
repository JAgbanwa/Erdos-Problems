import RefinedFractionalBound

namespace PaperIV.SublinearResearch
open Finset PaperIV.FarRounding PaperIV.RootedSimplicialDefect

theorem high_star_basic_margin (n s : ℚ) (hn : 8 ≤ n)
    (hs : 0 ≤ s) (hsn : 2*s ≤ n) :
    (5*n-1-12*s)^2/192+1 ≤ realTarget (n-s) := by
  have hp := mul_nonneg hs (show 0 ≤ n-2*s by linarith)
  have hnprod := mul_nonneg (show 0 ≤ n-8 by linarith) (show 0 ≤ n+8 by linarith)
  unfold realTarget
  nlinarith

/-- Basic shifted bound, for every admissible defect, before rounding.
For 4s<=n the separate refined theorem saves C(s+1,2) more. -/
theorem certified_shifted_fractional_bound {n s : ℕ} (hn : 8 ≤ n) (hs : s ≤ n)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : RootedDefectAt G s)
    {w : ℚ} (hw : CertifiedFractionalOptimum G w) :
    (G.edgeFinset.card : ℚ)-w ≤ (targetSize (n-s) : ℚ)+(n : ℚ)*s := by
  have hnq : (8 : ℚ) ≤ n := by exact_mod_cast hn
  have hs0 : (0 : ℚ) ≤ s := Nat.cast_nonneg _
  have hcast : ((n-s : ℕ) : ℚ) = (n : ℚ)-s := Nat.cast_sub hs
  by_cases hsmall : 2*s ≤ n
  · obtain ⟨c,hcn,α,ha0,hac,htri,hfour⟩ := certified_star_accounts (by omega) G hG hw
    have hcnq : (c : ℚ) ≤ n := by exact_mod_cast hcn
    have hcharge := exception_charge_le s (n-c)
    rw [Nat.cast_sub hcn] at hcharge
    by_cases hc : (c : ℚ) ≤ ((n : ℚ)+1)/2
    · have hbase := integral_baseline_le_target (n-s) c
      rw [hcast] at hbase
      have hp := mul_nonneg (show 0 ≤ (n : ℚ)-2*c+1 by linarith)
        (show 0 ≤ (c : ℚ)-α by linarith)
      unfold splitBaseline at hbase
      simp only [Nat.cast_choose_two] at htri
      nlinarith only [htri,hbase,hp,hcharge]
    · have hc4 : 4 ≤ c := by
        have : (4 : ℚ) < c := by linarith
        exact_mod_cast this.le
      have hhigh := high_star_combined (n : ℚ) s c α ((G.edgeFinset.card : ℚ)-w)
        (by linarith) hcnq
        (by simp only [Nat.cast_choose_two] at htri; linarith)
        (by
          have hf := hfour hc4
          norm_num [Nat.cast_choose_two,div_div] at hf ⊢
          exact hf)
      have hmargin := high_star_basic_margin (n : ℚ) s hnq hs0 (by exact_mod_cast hsmall)
      have hfloor := FixedL4.continuous_le_targetSize_add (n-s)
      rw [hcast] at hfloor
      unfold realTarget at hmargin
      nlinarith only [hhigh,hmargin,hfloor]
  · have hslarge : (n : ℚ) ≤ 2*s := by exact_mod_cast (show n ≤ 2*s by omega)
    obtain ⟨_,y,_,hy⟩ := hw
    have hw0 : 0 ≤ w := by
      rw [← hy]
      exact sum_nonneg (fun e _ => y.price_nonneg e)
    have hedgen : G.edgeFinset.card ≤ n.choose 2 := by
      simpa using G.card_edgeFinset_le_card_choose_two
    have hedge : (G.edgeFinset.card : ℚ) ≤ (n : ℚ)*((n : ℚ)-1)/2 := by
      have he : (G.edgeFinset.card : ℚ) ≤ (n.choose 2 : ℚ) := by exact_mod_cast hedgen
      simpa only [Nat.cast_choose_two] using he
    have htarget0 : (0 : ℚ) ≤ targetSize (n-s) := Nat.cast_nonneg _
    have hp := mul_nonneg (show 0 ≤ (n : ℚ) by positivity) (show 0 ≤ 2*(s : ℚ)-n by linarith)
    nlinarith

end PaperIV.SublinearResearch
#print axioms PaperIV.SublinearResearch.certified_shifted_fractional_bound

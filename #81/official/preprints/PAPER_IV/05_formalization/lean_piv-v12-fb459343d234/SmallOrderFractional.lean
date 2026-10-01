import UniformFractionalBound

/-! Removing the artificial n >= 8 restriction. Small-order checks below are
kernel proofs of rational inequalities, not graph enumeration or solver output.
The graph-theoretic input is the same certified maximum-star account.
-/
namespace PaperIV.SublinearResearch
open Finset PaperIV.FarRounding PaperIV.RootedSimplicialDefect

theorem small_high_envelope_shifted {n s c : ℕ} (hn : n < 8) (hs : s ≤ n)
    (hc : c < n) (hc4 : 4 ≤ c) (hhigh : n+1 < 2*c) :
    (c : ℚ)*(5*n-4*c-1)/12+s*((n : ℚ)-c) ≤
      (targetSize (n-s) : ℚ)+(n : ℚ)*s := by
  interval_cases n <;> interval_cases c <;> interval_cases s <;>
    norm_num [targetSize] at *

theorem small_high_envelope_refined {n s c : ℕ} (hn : n < 8) (hs : 4*s ≤ n)
    (hc : c < n) (hc4 : 4 ≤ c) (hhigh : n+1 < 2*c) :
    (c : ℚ)*(5*n-4*c-1)/12+s*((n : ℚ)-c) ≤
      (targetSize (n-s) : ℚ)+(n : ℚ)*s-((s+1).choose 2 : ℚ) := by
  have hsn : s ≤ n := by omega
  interval_cases n <;> interval_cases c <;> interval_cases s <;>
    norm_num [targetSize] at *

theorem certified_fractional_le_edge_count {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {w : ℚ} (hw : CertifiedFractionalOptimum G w) :
    (G.edgeFinset.card : ℚ)-w ≤ (n.choose 2 : ℚ) := by
  obtain ⟨_,y,_,hy⟩ := hw
  have hw0 : 0 ≤ w := by
    rw [← hy]
    exact sum_nonneg (fun e _ => y.price_nonneg e)
  have he : (G.edgeFinset.card : ℚ) ≤ (n.choose 2 : ℚ) := by
    exact_mod_cast (show G.edgeFinset.card ≤ n.choose 2 by
      simpa using G.card_edgeFinset_le_card_choose_two)
  linarith

/-- The shifted fractional bound holds at every order, including the empty graph. -/
theorem certified_shifted_fractional_bound_all_orders {n s : ℕ} (hs : s ≤ n)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : RootedDefectAt G s)
    {w : ℚ} (hw : CertifiedFractionalOptimum G w) :
    (G.edgeFinset.card : ℚ)-w ≤ (targetSize (n-s) : ℚ)+(n : ℚ)*s := by
  by_cases hn : 8 ≤ n
  · exact certified_shifted_fractional_bound hn hs G hG hw
  by_cases hn0 : n = 0
  · have he := certified_fractional_le_edge_count G hw
    have hs0 : s = 0 := by omega
    simpa [hn0,hs0,targetSize] using he
  obtain ⟨c,hcn,α,ha0,hac,htri,hfour⟩ := certified_star_accounts_strict (by omega) G hG hw
  have hcharge := exception_charge_le s (n-c)
  rw [Nat.cast_sub hcn.le] at hcharge
  by_cases hc : (c : ℚ) ≤ ((n : ℚ)+1)/2
  · have hbase := integral_baseline_le_target (n-s) c
    rw [Nat.cast_sub hs] at hbase
    have hp := mul_nonneg (show 0 ≤ (n : ℚ)-2*c+1 by linarith)
      (show 0 ≤ (c : ℚ)-α by linarith)
    unfold splitBaseline at hbase
    simp only [Nat.cast_choose_two] at htri
    nlinarith only [htri,hbase,hp,hcharge]
  · have hhigh : n+1 < 2*c := by
      exact_mod_cast (show (n : ℚ)+1 < 2*c by linarith)
    by_cases hc4 : 4 ≤ c
    · have he := high_star_exact_envelope (n : ℚ) s c α ((G.edgeFinset.card : ℚ)-w)
        (by linarith) (by exact_mod_cast hcn.le)
        (by simp only [Nat.cast_choose_two] at htri; linarith)
        (by
          have hf := hfour hc4
          norm_num [Nat.cast_choose_two,div_div] at hf ⊢
          exact hf)
      exact he.trans (small_high_envelope_shifted (by omega) hs hcn hc4 hhigh)
    · have hn4 : n = 4 := by omega
      have hc3 : c = 3 := by omega
      have ht : (3 : ℚ) ≤ (targetSize (n-s) : ℚ)+(n : ℚ)*s := by
        subst n
        interval_cases s <;> norm_num [targetSize]
      norm_num [hn4,hc3] at htri
      linarith

/-- The retained-charge improvement also holds at every order on its band 4s <= n. -/
theorem certified_refined_fractional_bound_all_orders {n s : ℕ} (hs : 4*s ≤ n)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : RootedDefectAt G s)
    {w : ℚ} (hw : CertifiedFractionalOptimum G w) :
    (G.edgeFinset.card : ℚ)-w ≤
      (targetSize (n-s) : ℚ)+(n : ℚ)*s-((s+1).choose 2 : ℚ) := by
  by_cases hn : 8 ≤ n
  · exact certified_refined_fractional_bound hn hs G hG hw
  by_cases hn0 : n = 0
  · have he := certified_fractional_le_edge_count G hw
    have hs0 : s = 0 := by omega
    simpa [hn0,hs0,targetSize] using he
  have hsn : s ≤ n := by omega
  obtain ⟨c,hcn,α,ha0,hac,htri,hfour⟩ := certified_star_accounts_strict (by omega) G hG hw
  by_cases hc : (c : ℚ) ≤ ((n : ℚ)+1)/2
  · have hcN : 2*c ≤ n+1 := by
      exact_mod_cast (show 2*(c : ℚ) ≤ n+1 by linarith)
    have hsqN : s ≤ n-c := by omega
    rw [exception_charge_exact s (n-c) hsqN,Nat.cast_sub hcn.le] at htri
    have hbase := integral_baseline_le_target (n-s) c
    rw [Nat.cast_sub hsn] at hbase
    have hp := mul_nonneg (show 0 ≤ (n : ℚ)-2*c+1 by linarith)
      (show 0 ≤ (c : ℚ)-α by linarith)
    unfold splitBaseline at hbase
    simp only [Nat.cast_choose_two,Nat.cast_add,Nat.cast_one] at htri ⊢
    nlinarith only [htri,hbase,hp]
  · have hhigh : n+1 < 2*c := by
      exact_mod_cast (show (n : ℚ)+1 < 2*c by linarith)
    by_cases hc4 : 4 ≤ c
    · have hcharge := exception_charge_le s (n-c)
      rw [Nat.cast_sub hcn.le] at hcharge
      have he := high_star_exact_envelope (n : ℚ) s c α ((G.edgeFinset.card : ℚ)-w)
        (by linarith) (by exact_mod_cast hcn.le)
        (by simp only [Nat.cast_choose_two] at htri; linarith)
        (by
          have hf := hfour hc4
          norm_num [Nat.cast_choose_two,div_div] at hf ⊢
          exact hf)
      exact he.trans (small_high_envelope_refined (by omega) hs hcn hc4 hhigh)
    · have hn4 : n = 4 := by omega
      have hc3 : c = 3 := by omega
      have ht : (3 : ℚ) ≤ (targetSize (n-s) : ℚ)+(n : ℚ)*s-
          ((s+1).choose 2 : ℚ) := by
        subst n
        have : s ≤ 1 := by omega
        interval_cases s <;> norm_num [targetSize]
      norm_num [hn4,hc3] at htri
      linarith

end PaperIV.SublinearResearch
#print axioms PaperIV.SublinearResearch.certified_shifted_fractional_bound_all_orders
#print axioms PaperIV.SublinearResearch.certified_refined_fractional_bound_all_orders

import Mathlib

/-!
Arithmetic for a refinement of Okechukwu, arXiv:2609.20871v1, Lemma 3.1.
These are accounting lemmas, NOT yet a theorem bounding F4 of a graph.
The graph-level producer of the signed-star inequalities remains separate.
-/
namespace PaperIV.SublinearResearch
open Finset

def starBaseline (n c : ℚ) : ℚ := c*(n-c)-c*(c-1)/2
def realTarget (n : ℚ) : ℚ := (2*n+1)^2/24
def refinedRealTarget (n s : ℚ) : ℚ := realTarget (n-s)+n*s-s*(s+1)/2

theorem twice_sum_range_rat (n : ℕ) :
    2 * (∑ j ∈ range n, (j : ℚ)) = (n : ℚ)*((n : ℚ)-1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ]; push_cast; nlinarith

/-- Last rows cannot all spend s exceptional edges. -/
theorem exception_charge_exact (s q : ℕ) (hsq : s ≤ q) :
    (∑ j ∈ range q, ((min s j : ℕ) : ℚ)) =
      (s : ℚ)*q-(s : ℚ)*((s : ℚ)+1)/2 := by
  induction q, hsq using Nat.le_induction with
  | base =>
    have he : (∑ j ∈ range s, ((min s j : ℕ) : ℚ)) = ∑ j ∈ range s, (j : ℚ) := by
      apply sum_congr rfl
      intro j hj
      rw [min_eq_right (Nat.le_of_lt (mem_range.mp hj))]
    rw [he]
    nlinarith [twice_sum_range_rat s]
  | succ q hq ih =>
    rw [sum_range_succ, min_eq_left hq, ih]
    push_cast
    ring

theorem retained_star_shift (n s c : ℚ) :
    starBaseline n c+s*(n-c)-s*(s+1)/2 =
      starBaseline (n-s) c+n*s-s*(s+1)/2 := by
  unfold starBaseline
  ring

theorem starBaseline_le_realTarget (n c : ℚ) : starBaseline n c ≤ realTarget n := by
  unfold starBaseline realTarget
  nlinarith [sq_nonneg (6*c-2*n-1)]

theorem low_star_refined_bound (n s c α W : ℚ)
    (hc : c ≤ (n+1)/2) (hα : α ≤ c)
    (hstar : W ≤ starBaseline n c-(n-2*c+1)*(c-α)+
      s*(n-c)-s*(s+1)/2) : W ≤ refinedRealTarget n s := by
  have hprod : 0 ≤ (n-2*c+1)*(c-α) := mul_nonneg (by linarith) (by linarith)
  have hid := retained_star_shift n s c
  have hb := starBaseline_le_realTarget (n-s) c
  unfold refinedRealTarget
  linarith

/-- A whole unit of room covers the floor correction in the large-root branch. -/
theorem high_star_refined_margin (n s : ℚ) (hn : 8 ≤ n)
    (hs : 0 ≤ s) (hsn : 4*s ≤ n) :
    n*s+(5*n-1-12*s)^2/192+1 ≤ refinedRealTarget n s := by
  have hprod : 0 ≤ s*(n-4*s) := mul_nonneg hs (by linarith)
  have hnprod : 0 ≤ (n-8)*(n+8) := mul_nonneg (by linarith) (by linarith)
  -- Rewrite the quadratic remainder into nonnegative terms on 0 ≤ s ≤ n/4.
  have haux : 0 ≤ (n-4*s)*(n+38) := mul_nonneg (by linarith) (by linarith)
  have hns : 0 ≤ n*s := mul_nonneg (by linarith) hs
  unfold refinedRealTarget realTarget
  nlinarith

theorem refined_gain_over_old (n s : ℚ) :
    realTarget n+n*s-refinedRealTarget n s =
      n*s/3+s^2/3+2*s/3 := by
  unfold refinedRealTarget realTarget
  ring

end PaperIV.SublinearResearch
#print axioms PaperIV.SublinearResearch.exception_charge_exact
#print axioms PaperIV.SublinearResearch.low_star_refined_bound
#print axioms PaperIV.SublinearResearch.high_star_refined_margin

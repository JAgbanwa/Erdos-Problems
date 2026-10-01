import Mathlib.Tactic

namespace FixedDefectStability

theorem twice_choose (a : ℕ) : 2*a.choose 2+a=a*a := by
  rw [Nat.choose_two_right]
  have hh := Nat.div_mul_cancel (Nat.even_mul_pred_self a).two_dvd
  rcases a with _ | a
  · simp
  · simp only [Nat.add_sub_cancel] at hh ⊢
    nlinarith only [hh]

theorem choose_sub_identity (c s : ℕ) (hs : s ≤ c) :
    (c-s).choose 2+s*c=c.choose 2+(s+1).choose 2 := by
  have h1 := twice_choose c
  have h2 := twice_choose (c-s)
  have h3 := twice_choose (s+1)
  have hc : c-s+s=c := by omega
  have hsq := congrArg (fun x : ℕ => x*x) hc
  nlinarith only [h1,h2,h3,hc,hsq]

/-- Deleting r further clique vertices costs at most r times the ambient order. -/
theorem core_deletion_bound (c s r k e n : ℕ)
    (hcard : k+s+r=c) (hcn : c ≤ n) :
    e-k.choose 2 ≤ (e-(c-s).choose 2)+r*n := by
  have hc : c-s=k+r := by omega
  have hk := twice_choose k
  have hkr := twice_choose (k+r)
  have hcost : (k+r).choose 2 ≤ k.choose 2+r*n := by
    have hp := Nat.mul_le_mul_left r (show k+r ≤ n by omega)
    nlinarith only [hk,hkr,hp,Nat.zero_le r]
  rw [hc]
  omega

/-- Numerical account for a literal clique root, including both incidence
charges for exceptional vertices. Graph existence is proved separately. -/
theorem clique_edit_bound (s : ℕ) (δ A m R E nt rn d : ℚ)
    (hδ : 0 ≤ δ) (hA : 0 ≤ A) (hm : 0 ≤ m) (hR : 0 ≤ R)
    (hbudget : A+m/(2000*((s:ℚ)+1)^2)+R ≤ δ)
    (hnt : nt ≤ 800*((s:ℚ)+1)^2*R)
    (hE : E ≤ R+nt) (hr : rn ≤ 16*s*E)
    (hedit : d ≤ A+m+E+2*rn+2*nt) :
    d ≤ 40000*((s:ℚ)+1)^3*δ := by
  have hs : (0:ℚ) ≤ s := Nat.cast_nonneg _
  have hS2 : 1 ≤ ((s:ℚ)+1)^2 := by nlinarith only [hs,sq_nonneg (s:ℚ)]
  have hden : 0 < 2000*((s:ℚ)+1)^2 := by positivity
  have hb : 2000*((s:ℚ)+1)^2*(A+R)+m ≤ 2000*((s:ℚ)+1)^2*δ := by
    have hh := (div_le_iff₀ hden).mp
      (show m/(2000*((s:ℚ)+1)^2) ≤ δ-A-R by linarith only [hbudget])
    nlinarith only [hh]
  have hpaid : A+R ≤ δ := by
    have := div_nonneg hm hden.le
    linarith only [hbudget,this]
  have hRm : R ≤ δ := by linarith only [hpaid,hA]
  have hep := mul_le_mul_of_nonneg_left hE (show (0:ℚ) ≤ 1+32*s by positivity)
  have hntp := mul_le_mul_of_nonneg_left hnt (show (0:ℚ) ≤ 3+32*s by positivity)
  have hd : d ≤ A+m+(1+32*s+(3+32*s)*800*((s:ℚ)+1)^2)*R := by
    nlinarith only [hedit,hr,hep,hntp]
  have hcoef : (1:ℚ)+32*s+(3+32*s)*800*((s:ℚ)+1)^2 ≤
      38000*((s:ℚ)+1)^3 := by
    nlinarith only [hs,sq_nonneg (s:ℚ),mul_nonneg hs (sq_nonneg (s:ℚ))]
  have hRc := mul_le_mul_of_nonneg_right hcoef hR
  have hApaid : A ≤ 2000*((s:ℚ)+1)^2*A := by
    nlinarith only [mul_nonneg hA (sub_nonneg.mpr hS2),hA]
  have hRpaid := mul_le_mul_of_nonneg_left hRm
    (show (0:ℚ) ≤ 38000*((s:ℚ)+1)^3 by positivity)
  have hsmall : 2000*((s:ℚ)+1)^2 ≤ 2000*((s:ℚ)+1)^3 := by
    nlinarith only [hs,sq_nonneg (s:ℚ),mul_nonneg hs (sq_nonneg (s:ℚ))]
  have hsmallp := mul_le_mul_of_nonneg_right hsmall hδ
  have hR0 : 0 ≤ 2000*((s:ℚ)+1)^2*R := by positivity
  nlinarith only [hd,hRc,hApaid,hb,hRpaid,hsmallp,hR0]

end FixedDefectStability
#print axioms FixedDefectStability.core_deletion_bound
#print axioms FixedDefectStability.clique_edit_bound

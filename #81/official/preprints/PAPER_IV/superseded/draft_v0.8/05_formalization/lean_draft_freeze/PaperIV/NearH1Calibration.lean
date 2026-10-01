import Mathlib

/-!
# Exact scalar calibration for the near H1 constructor

This is the Lean counterpart of `checks/near_h1_calibration.py`.  It contains
no graph-theoretic assumption: each premise is the numeric output of one
explicit bridge, and the conclusion is precisely the parameter window used by
the physical RD09 constructor.
-/

namespace PaperIV.NearH1Calibration

def eps : ℚ := 1 / 10^12
def eta : ℚ := 1 / 10^16

/-- The terminal deficit absorbs the linear sharp-envelope correction at the
fixed threshold `2·10^13`. -/
theorem delta_small {n delta : ℚ}
    (hn : 2 * (10 : ℚ) ^ 13 ≤ n)
    (hdelta : delta ≤ (eta + 6 * eps) * n ^ 2 + n / 6 + 1 / 24) :
    delta ≤ (61 : ℚ) / 10 * eps * n ^ 2 := by
  dsimp [eta, eps] at hdelta ⊢
  nlinarith [sq_nonneg (n - 2 * (10 : ℚ) ^ 13)]

/-- Missing pairs inside the comparator core force only a tiny loss from that
core when it is replaced by a maximum clique. -/
theorem excluded_core_small {n u : ℚ}
    (hn : 2 * (10 : ℚ) ^ 13 ≤ n) (hu : 0 ≤ u)
    (hmissing : u * (u + 1) / 2 ≤ eps * n ^ 2) :
    u ≤ 3 * n / (2 * 10^6) := by
  unfold eps at hmissing
  have hn0 : 0 ≤ n := by positivity
  by_contra h
  have hgt : 3 * n / (2 * 10^6) < u := lt_of_not_ge h
  have hsquare : (3 * n / (2 * 10^6)) ^ 2 < u ^ 2 := by
    nlinarith [sq_nonneg (u - 3 * n / (2 * 10^6))]
  nlinarith

/-- The physical edit account of the comparator core is a tiny fraction of the
squared root size.  This is the only place where the excluded-core bound and
the edit budget interact, and it uses exactly the four facts listed. -/
theorem edit_mass_small {n u a mA : ℚ}
    (hn : 2 * (10 : ℚ) ^ 13 ≤ n)
    (hu : u ≤ 3 * n / (2 * 10 ^ 6))
    (ha : 33 * n / 100 ≤ a)
    (hedit : mA ≤ eps * n ^ 2 + u * n) :
    mA ≤ a ^ 2 / 65536 := by
  have hn0 : (0 : ℚ) ≤ n := by linarith
  have hun : u * n ≤ 3 * n / (2 * 10 ^ 6) * n :=
    mul_le_mul_of_nonneg_right hu hn0
  have hsq : (33 * n / 100) ^ 2 ≤ a ^ 2 := by
    have h0 : (0 : ℚ) ≤ 33 * n / 100 := by linarith
    nlinarith
  unfold eps at hedit
  nlinarith

/-- Complete scalar output needed downstream. -/
theorem calibration {n k u a delta residual mA : ℚ}
    (hn : 2 * (10 : ℚ) ^ 13 ≤ n)
    (hu : 0 ≤ u)
    (hdelta : delta ≤ (eta + 6 * eps) * n ^ 2 + n / 6 + 1 / 24)
    (hres : residual ^ 2 ≤ 24 * delta)
    (hresDef : residual = 6 * k - 2 * n - 1)
    (hmissing : u * (u + 1) / 2 ≤ eps * n ^ 2)
    (ha : a = k - u)
    (hedit : mA ≤ eps * n ^ 2 + u * n) :
    delta ≤ (61 : ℚ) / 10 * eps * n ^ 2 ∧
    u ≤ 3 * n / (2 * 10^6) ∧
    33 * n / 100 ≤ a ∧
    n - 3 * a ≤ a / 64 ∧
    3 * a - n ≤ a / 64 ∧
    1024 ≤ a ∧
    mA ≤ a ^ 2 / 65536 := by
  have hn0 : 0 ≤ n := by positivity
  have hd := delta_small hn hdelta
  have hus := excluded_core_small hn hu hmissing
  have hrsq' : residual ^ 2 ≤ 24 * ((61 : ℚ) / 10 * eps * n ^ 2) :=
    hres.trans (by linarith)
  have hresUp : residual ≤ n / 10000 := by
    by_contra h
    have hgt : n / 10000 < residual := lt_of_not_ge h
    dsimp [eps] at hrsq'
    nlinarith [sq_nonneg (residual - n / 10000)]
  have hresLo : -(n / 10000) ≤ residual := by
    by_contra h
    have hgt : residual < -(n / 10000) := lt_of_not_ge h
    dsimp [eps] at hrsq'
    nlinarith [sq_nonneg (residual + n / 10000)]
  have hkUp : 6 * k - 2 * n - 1 ≤ n / 10000 := by linarith
  have hkLo : -(n / 10000) ≤ 6 * k - 2 * n - 1 := by linarith
  have haLarge : 33 * n / 100 ≤ a := by
    rw [ha]
    linarith
  refine ⟨hd, hus, haLarge, ?_, ?_, ?_, edit_mass_small hn hus haLarge hedit⟩
  · rw [ha]
    linarith
  · rw [ha]
    linarith
  · linarith

end PaperIV.NearH1Calibration

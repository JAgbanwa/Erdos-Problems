/-
  Paper I — arithmetic core (Milestone A).  Self-contained, over ℚ.
  Should compile GREEN under Lean/Mathlib v4.28.0 (only ring / nlinarith).
  Every identity below was validated symbolically (residual 0) and numerically.

  Roles (paper equation numbers):
    Rq                = R(p,q) = (2p²−2pq−q²)/12            (7.1)
    seven_two/four/six= the three orbit-candidate identities (7.2)/(7.4)/(7.6)
    U/D/H_ge          = each orbit candidate ≥ R − p/2       (⇒ M ≥ R − p/2, since M = min)
    assembly_eq       = C(p,2) − 2R + p = (p+q)²/6 + p/2     (8.2)
    final_bound       = (p+q)²/6 + p/2 + b₁ ≤ n²/6 + n       (8.3)→(8.4)
-/
import Mathlib

namespace PaperI
open scoped BigOperators

/-- R(p,q) = (2p² − 2pq − q²)/12. -/
def Rq (p q : ℚ) : ℚ := (2*p^2 - 2*p*q - q^2) / 12

/-- Orbit objective pieces for a pure profile: s = |S|, o = p − s. -/
def Aq (s q : ℚ) : ℚ := s*(s - 1 - q) / 2
def Bq (s o : ℚ) : ℚ := s*o
def Cq (o : ℚ) : ℚ := o*(o - 1) / 2

/-- The three canonical cover candidates. -/
def Uq (s o q : ℚ) : ℚ := (Aq s q + Bq s o + Cq o) / 3
def Dq (s o q : ℚ) : ℚ := Aq s q + Cq o
def Hq (s o q : ℚ) : ℚ := Aq s q + (Bq s o + Cq o) / 3

/-! ### Orbit-candidate identities (paper 7.2 / 7.4 / 7.6), with o = p − s. -/

theorem seven_two (p s q : ℚ) :
    12 * (Uq s (p - s) q - Rq p q) = q*(2*(p - s) + q) - 2*p := by
  unfold Uq Aq Bq Cq Rq; ring

theorem seven_four (p s q : ℚ) :
    12 * (Dq s (p - s) q - Rq p q)
      = 12*(p - s)^2 - 6*(p - s)*(2*p - q) + (2*p - q)^2 - 6*p := by
  unfold Dq Aq Cq Rq; ring

theorem seven_six (p s q : ℚ) :
    12 * (Hq s (p - s) q - Rq p q) = (2*s - q)^2 + 2*q*(p - s) - 2*p - 4*s := by
  unfold Hq Aq Bq Cq Rq; ring

/-! ### Each candidate ≥ R − p/2  (assumptions: q ≥ 1 orbit domain, 0 ≤ o = p−s, s ≤ p, 0 ≤ p). -/

theorem U_ge (p s q : ℚ) (hq : 0 ≤ q) (ho : 0 ≤ p - s) (hp : 0 ≤ p) :
    Uq s (p - s) q ≥ Rq p q - p/2 := by
  have h := seven_two p s q
  nlinarith [h, mul_nonneg hq (by nlinarith : (0:ℚ) ≤ 2*(p - s) + q), hp]

theorem D_ge (p s q : ℚ) (hp : 0 ≤ p) :
    Dq s (p - s) q ≥ Rq p q - p/2 := by
  have h := seven_four p s q
  nlinarith [h, sq_nonneg (4*(p - s) - (2*p - q)), sq_nonneg (2*p - q), hp]

theorem H_ge (p s q : ℚ) (hq : 0 ≤ q) (ho : 0 ≤ p - s) :
    Hq s (p - s) q ≥ Rq p q - p/2 := by
  have h := seven_six p s q
  nlinarith [h, sq_nonneg (2*s - q), mul_nonneg hq ho]

/-- M(κ^S) = min{U,D,H} ≥ R − p/2 (o ≥ 3); the o ≤ 2 case uses only U,D. -/
theorem M_ge_of_min (p s q : ℚ) (hq : 0 ≤ q) (ho : 0 ≤ p - s) (hp : 0 ≤ p) :
    min (Uq s (p - s) q) (min (Dq s (p - s) q) (Hq s (p - s) q)) ≥ Rq p q - p/2 := by
  have hU := U_ge p s q hq ho hp
  have hD := D_ge p s q hp
  have hH := H_ge p s q hq ho
  exact le_min hU (le_min hD hH)

/-! ### Assembly identity (8.2) and final conversion (8.3)→(8.4). -/

theorem assembly_eq (p q : ℚ) :
    p*(p - 1)/2 - 2*(Rq p q) + p = (p + q)^2/6 + p/2 := by
  unfold Rq; ring

/-- Final bound: with p+q ≤ n and p/2 + b₁ ≤ n, the constructed deficit is ≤ n²/6 + n. -/
theorem final_bound (p q b1 n : ℚ)
    (h1 : 0 ≤ p + q) (h2 : p + q ≤ n) (h3 : p/2 + b1 ≤ n) :
    (p + q)^2/6 + p/2 + b1 ≤ n^2/6 + n := by
  have hsq : (p + q)^2 ≤ n^2 := by nlinarith [h1, h2]
  nlinarith [hsq, h3]

end PaperI

-- ===== A-ARITH sorry-free audit (reporting protocol) =====
#print axioms PaperI.seven_two
#print axioms PaperI.seven_four
#print axioms PaperI.seven_six
#print axioms PaperI.U_ge
#print axioms PaperI.D_ge
#print axioms PaperI.H_ge
#print axioms PaperI.M_ge_of_min
#print axioms PaperI.assembly_eq
#print axioms PaperI.final_bound

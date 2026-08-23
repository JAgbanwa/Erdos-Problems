import PaperII.EdgeCount
import PaperII.L9
import PaperII.Arith

/-!
# Paper II — `Φ_τ` of the complete-split graph (ledger L10 = Corollary 6.3)

From the edge count `|E(S_{p,q})| = C(p,2) + p*q` and the terminal cover value `τ₃*(S_{p,q})` (L9):

* saturated branch `q ≥ p-1`:  `Φ_τ = p*q - C(p,2) = F_n(p)`  (`n = p+q`);
* nonsaturated branch `q ≤ p-1` (`p ≥ 3`):  `Φ_τ = (C(p,2) + p*q)/3`.

`Fsat` is the integer functional from `PaperII.Arith` (`2·Fsat n p = p*(2n+1-3p)`), which L11 maximizes.
-/

open scoped BigOperators

namespace PaperII

/-- L10, saturated branch — closed form `Φ_τ = p*q - C(p,2)`. -/
theorem phiTau_completeSplit_sat (p q : ℕ) (hp : 2 ≤ p) (hq : p - 1 ≤ q) :
    phiTau (completeSplit p q) = (p : ℝ) * q - (p.choose 2 : ℝ) := by
  unfold phiTau
  rw [completeSplit_card_edgeFinset, tau3star_completeSplit_sat p q hp hq]
  push_cast
  ring

/-- L10, nonsaturated branch — closed form `Φ_τ = (C(p,2) + p*q)/3`. -/
theorem phiTau_completeSplit_unsat (p q : ℕ) (hp : 3 ≤ p) (hq : q ≤ p - 1) :
    phiTau (completeSplit p q) = ((p.choose 2 : ℝ) + (p : ℝ) * q) / 3 := by
  unfold phiTau
  rw [completeSplit_card_edgeFinset, tau3star_completeSplit_unsat p q hp hq]
  push_cast
  ring

/-- Bridge to the arithmetic functional `Fsat` (saturated branch): `Φ_τ(S_{p,q}) = F_{p+q}(p)`.
    This is the form consumed by the L12 maximization. -/
theorem phiTau_completeSplit_sat_eq_Fsat (p q : ℕ) (hp : 2 ≤ p) (hq : p - 1 ≤ q) :
    phiTau (completeSplit p q) = ((Fsat (p + q) p : ℤ) : ℝ) := by
  rw [phiTau_completeSplit_sat p q hp hq]
  have hdvd : 2 ∣ p * (p - 1) := (Nat.even_mul_pred_self p).two_dvd
  -- `2·C(p,2) = p*(p-1)`, cast to ℝ with `↑(p-1) = ↑p - 1`.
  have hnat : 2 * p.choose 2 = p * (p - 1) := by
    rw [Nat.choose_two_right]; exact Nat.mul_div_cancel' hdvd
  have hchoose : (2 : ℝ) * (p.choose 2 : ℝ) = (p : ℝ) * ((p : ℝ) - 1) := by
    have hc : ((2 * p.choose 2 : ℕ) : ℝ) = ((p * (p - 1) : ℕ) : ℝ) := by exact_mod_cast hnat
    push_cast [Nat.cast_pred (show 0 < p by omega)] at hc
    linarith [hc]
  -- `2·Fsat = twoFsat = p*(2(p+q)+1-3p)`.
  have h2 : (2 : ℝ) * ((Fsat (p + q) p : ℤ) : ℝ) = ((twoFsat (p + q) p : ℤ) : ℝ) := by
    have := two_mul_Fsat (p + q) p
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) this
  -- Reduce to a polynomial identity by clearing the ×2.
  have key : (2 : ℝ) * ((p : ℝ) * q - (p.choose 2 : ℝ)) = (2 : ℝ) * ((Fsat (p + q) p : ℤ) : ℝ) := by
    rw [h2]
    simp only [twoFsat]
    push_cas
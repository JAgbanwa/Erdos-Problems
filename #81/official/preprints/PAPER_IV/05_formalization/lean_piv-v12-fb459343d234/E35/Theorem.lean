import E35.Main
import E35.Edit
import E33.ClosedForms
import E34.L11Main

/-!
# E35 — T2/T3: Theorem C above a tower of polynomial height in `s`

* **`Fexp_le_tower`**: `E33.Fexp E34.NeditE s ≤ tower2 (Ptower s)` with the explicit polynomial
  `Ptower s = cT·(s+1)^1680`, `cT = hIter + cFar + 841780`,
  `cFar = cPoly·(128·10^82)^105`, `cPoly = 4·17664^5·9000^105 + 3006`,
  `hIter = 4·8^5·2208^5·4500^105·(2·10^16)^105` (the iteration count of §6.3 at `η₀`).
* **`theoremC_tower`**: Theorem C for every `n ≥ tower2 (Ptower s)`.
* **`theoremC_tower_uniform`**, **`theoremC_tower_uniform_sMax`**: all defects `s ≤ S` at once
  when `tower2 (Ptower S) ≤ n`; in particular all `s ≤ sMaxT n`.
-/

namespace E35

open E19 A4S1.IndepAll

/-- `cFar = cPoly·(128·10^82)^105`. -/
def cFar : ℕ := cPoly * (128 * 10 ^ 82) ^ 105

/-- The leading constant of the tower height, `cT = hIter + cFar + 841780`. -/
def cT : ℕ := E18.Numeric.hIter + cFar + 841780

/-- **The explicit polynomial tower height** `Ptower s = cT·(s+1)^1680`. -/
def Ptower (s : ℕ) : ℕ := cT * (s + 1) ^ 1680

set_option exponentiation.threshold 2000 in
theorem Ptower_mono : Monotone Ptower := by
  intro a b h
  unfold Ptower
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (show a + 1 ≤ b + 1 by omega) 1680)

/-! ## The far margin `η_s` -/

/-- The far margin `η_s = ε_s²/64 − ε_s⁴/(2¹⁷(s+1))`. -/
def etaS (s : ℕ) : ℚ := epsS s ^ 2 / 64 - epsS s ^ 4 / (2 ^ 17 * ((s : ℚ) + 1))

theorem epsS_pos (s : ℕ) : 0 < epsS s := by unfold epsS; positivity

theorem epsS_le_one (s : ℕ) : epsS s ≤ 1 := by
  unfold epsS
  have : (1 : ℚ) ≤ ((s : ℚ) + 1) ^ 8 := one_le_pow₀ (by linarith [(Nat.cast_nonneg s : (0 : ℚ) ≤ s)])
  rw [div_le_one (by positivity)]; nlinarith

theorem etaS_ge (s : ℕ) : epsS s ^ 2 / 128 ≤ etaS s := by
  unfold etaS
  have h0 := epsS_pos s
  have h1 := epsS_le_one s
  have hx : (1 : ℚ) ≤ (s : ℚ) + 1 := by linarith [(Nat.cast_nonneg s : (0 : ℚ) ≤ s)]
  have hE : epsS s ^ 4 ≤ epsS s ^ 2 := pow_le_pow_of_le_one h0.le h1 (by norm_num)
  have : epsS s ^ 4 / (2 ^ 17 * ((s : ℚ) + 1)) ≤ epsS s ^ 2 / 128 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (0 : ℚ) ≤ epsS s ^ 2 := by positivity
    nlinarith
  linarith

theorem etaS_pos (s : ℕ) : 0 < etaS s := lt_of_lt_of_le (by have := epsS_pos s; positivity) (etaS_ge s)

theorem etaS_le_one (s : ℕ) : etaS s ≤ 1 := by
  unfold etaS
  have h0 := epsS_pos s
  have h1 := epsS_le_one s
  have : 0 ≤ epsS s ^ 4 / (2 ^ 17 * ((s : ℚ) + 1)) := by positivity
  have : epsS s ^ 2 ≤ 1 := pow_le_one₀ h0.le h1
  linarith

theorem inv_etaS_le (s : ℕ) : 1 / etaS s ≤ 128 * 10 ^ 82 * ((s : ℚ) + 1) ^ 16 := by
  have h := etaS_ge s
  have h0 := epsS_pos s
  rw [div_le_iff₀ (etaS_pos s)]
  have e : 128 * 10 ^ 82 * ((s : ℚ) + 1) ^ 16 * (epsS s ^ 2 / 128) = 1 := by
    unfold epsS; field_simp
  have : 0 ≤ 128 * 10 ^ 82 * ((s : ℚ) + 1) ^ 16 := by positivity
  nlinarith

/-- **`NfarE η_s ≤ tower2 (cFar·(s+1)^1680)`.** -/
theorem NfarE_etaS_le (s : ℕ) : E18.NfarE (etaS s) ≤ tower2 (cFar * (s + 1) ^ 1680) := by
  refine (NfarE_le_tower_poly _ (etaS_pos s) (etaS_le_one s)).trans (tower2_mono ?_)
  apply Nat.ceil_le.2
  have hp : (0 : ℝ) < (etaS s : ℝ) := by exact_mod_cast etaS_pos s
  have hinv : ((1 / etaS s : ℚ) : ℝ) ≤ ((128 * 10 ^ 82 * ((s : ℚ) + 1) ^ 16 : ℚ) : ℝ) := by
    exact_mod_cast inv_etaS_le s
  push_cast at hinv
  have h105 : (1 / (etaS s : ℝ)) ^ 105 ≤ (128 * 10 ^ 82 * ((s : ℝ) + 1) ^ 16) ^ 105 :=
    pow_le_pow_left₀ (by positivity) hinv 105
  have e : (cPoly : ℝ) / (etaS s : ℝ) ^ 105 = cPoly * (1 / (etaS s : ℝ)) ^ 105 := by
    rw [div_pow, one_pow]; ring
  rw [e]
  unfold cFar
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow]
  have hc : ((128 * 10 ^ 82 : ℕ) : ℝ) = 128 * 10 ^ 82 := by norm_num
  have hy : (((s + 1 : ℕ)) : ℝ) = (s : ℝ) + 1 := by push_cast; ring
  rw [hc, hy]
  have : (0 : ℝ) ≤ (cPoly : ℝ) := Nat.cast_nonneg _
  calc (cPoly : ℝ) * (1 / (etaS s : ℝ)) ^ 105
      ≤ cPoly * (128 * 10 ^ 82 * ((s : ℝ) + 1) ^ 16) ^ 105 := mul_le_mul_of_nonneg_left h105 this
    _ = cPoly * (128 * 10 ^ 82) ^ 105 * ((s : ℝ) + 1) ^ 1680 := by
        generalize (128 * 10 ^ 82 : ℝ) = C
        generalize ((s : ℝ) + 1) = y
        rw [mul_pow, ← pow_mul]; ring

/-! ## Tower arithmetic -/

theorem four_mul_le_two_pow' (n : ℕ) (hn : 4 ≤ n) : 4 * n ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih => rw [pow_succ]; omega

theorem tower2_ge_four (p : ℕ) (hp : 2 ≤ p) : 4 ≤ tower2 p := by
  have : tower2 2 = 4 := by decide +kernel
  rw [← this]; exact tower2_mono hp

theorem tower2_pow_four_le (p : ℕ) (hp : 3 ≤ p) : tower2 p ^ 4 ≤ tower2 (p + 1) := by
  obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
  rw [tower2_succ (p' + 1), tower2_succ p', ← pow_mul]
  exact Nat.pow_le_pow_right (by norm_num)
    (by have := four_mul_le_two_pow' _ (tower2_ge_four p' (by omega)); rw [mul_comm]; exact this)

theorem le_tower_of_le_two_pow {a Y : ℕ} (h : a ≤ 2 ^ Y) : a ≤ tower2 (3 * Y + 2) := by
  refine h.trans ((Nat.pow_le_pow_right (by norm_num) ?_).trans (two_pow_two_pow_le_tower2 _))
  exact le_trans (Nat.lt_two_pow_self).le (Nat.pow_le_pow_right (by norm_num) (by omega))

theorem x_pow_le_two_pow (x k : ℕ) : x ^ k ≤ 2 ^ (k * x) := by
  rw [pow_mul']
  exact Nat.pow_le_pow_left (Nat.lt_two_pow_self).le k

theorem fexp_arith (N tp c : ℕ) (h22 : 22 ≤ tp) (hN : N ≤ 4 * tp) (hc : c ≤ tp) :
    N + (N * N + 1) * c + 1 ≤ tp ^ 4 := by
  have h1 : N * N + 1 ≤ 17 * (tp * tp) := by nlinarith
  have h2 : (N * N + 1) * c ≤ 17 * (tp * tp) * tp := Nat.mul_le_mul h1 hc
  have h3 : 22 * (tp * tp * tp) ≤ tp ^ 4 := by
    have : tp ^ 4 = tp * (tp * tp * tp) := by ring
    rw [this]; exact Nat.mul_le_mul_right _ h22
  have h4 : tp ≤ tp * tp * tp := by
    have : 1 ≤ tp * tp := by nlinarith
    nlinarith
  nlinarith

set_option exponentiation.threshold 2000 in
set_option maxRecDepth 10000 in
/-- **T2: `Fexp NeditE s ≤ tower2 (Ptower s)`**, `Ptower s = cT·(s+1)^1680`. -/
theorem Fexp_le_tower (s : ℕ) : E33.Fexp E34.NeditE s ≤ tower2 (Ptower s) := by
  rw [E33.Fexp_eq, E33.N0_eq]
  set Y := Yedit s with hY
  set X := (s + 1) ^ 1680 with hX
  set p := E18.Numeric.hIter + 7 + cFar * X + (3 * Y + 2) with hp
  set tp := tower2 p with htp
  have hx1 : 1 ≤ s + 1 := by omega
  have hX1 : 1 ≤ X := by rw [hX]; exact Nat.one_le_pow 1680 (s + 1) hx1
  have hxX : s + 1 ≤ X := by
    rw [hX]
    calc s + 1 = (s + 1) ^ 1 := (pow_one _).symm
      _ ≤ (s + 1) ^ 1680 := Nat.pow_le_pow_right hx1 (by norm_num)
  have hYx : 16 * (s + 1) + 337 ≤ Y := by rw [hY]; unfold Yedit Eedit; omega
  -- the pieces
  have hmono1 : tower2 (E18.Numeric.hIter + 7) ≤ tp := tower2_mono (by omega)
  have hmono2 : tower2 (cFar * X) ≤ tp := tower2_mono (by omega)
  have hmono3 : tower2 (3 * Y + 2) ≤ tp := tower2_mono (by omega)
  have hstab : E33.stabThreshold ≤ tp := E33.stabThreshold_le_tower.trans hmono1
  have hsmall : ∀ a : ℕ, a ≤ 2 ^ Y → a ≤ tp :=
    fun a ha => (le_tower_of_le_two_pow ha).trans hmono3
  have hc16 : 16 * 10 ^ 100 * (s + 1) ^ 16 ≤ tp := by
    apply hsmall
    calc 16 * 10 ^ 100 * (s + 1) ^ 16 ≤ 2 ^ 337 * 2 ^ (16 * (s + 1)) :=
          Nat.mul_le_mul (by norm_num) (x_pow_le_two_pow (s + 1) 16)
      _ = 2 ^ (337 + 16 * (s + 1)) := by rw [← pow_add]
      _ ≤ 2 ^ Y := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hc50 : 10 ^ 50 * (s + 1) ^ 8 ≤ tp := by
    apply hsmall
    calc 10 ^ 50 * (s + 1) ^ 8 ≤ 2 ^ 167 * 2 ^ (8 * (s + 1)) :=
          Nat.mul_le_mul (by norm_num) (x_pow_le_two_pow (s + 1) 8)
      _ = 2 ^ (167 + 8 * (s + 1)) := by rw [← pow_add]
      _ ≤ 2 ^ Y := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hc41 : 10 ^ 41 * (s + 1) ^ 8 ≤ tp := by
    apply hsmall
    calc 10 ^ 41 * (s + 1) ^ 8 ≤ 2 ^ 137 * 2 ^ (8 * (s + 1)) :=
          Nat.mul_le_mul (by norm_num) (x_pow_le_two_pow (s + 1) 8)
      _ = 2 ^ (137 + 8 * (s + 1)) := by rw [← pow_add]
      _ ≤ 2 ^ Y := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hs3 : s + 3 ≤ tp := by
    apply hsmall
    exact le_trans (by omega) (Nat.lt_two_pow_self (n := Y)).le
  have h22 : 22 ≤ tp := by
    apply le_trans _ (hsmall (2 ^ 5) (Nat.pow_le_pow_right (by norm_num) (by omega)))
    norm_num
  have hed : E34.NeditE s (epsS s ^ 4 / (2 ^ 19 * ((s : ℚ) + 1))) ≤ tp :=
    (NeditE_le_tower s).trans hmono3
  have hfar : E18.NfarE (epsS s ^ 2 / 64 - epsS s ^ 4 / (2 ^ 17 * ((s : ℚ) + 1))) ≤ tp :=
    (NfarE_etaS_le s).trans hmono2
  -- `N₀ ≤ 4 tp`
  set N := max (max E33.stabThreshold (16 * 10 ^ 100 * (s + 1) ^ 16))
      (E34.NeditE s (epsS s ^ 4 / (2 ^ 19 * ((s : ℚ) + 1))))
    + E18.NfarE (epsS s ^ 2 / 64 - epsS s ^ 4 / (2 ^ 17 * ((s : ℚ) + 1)))
    + 10 ^ 50 * (s + 1) ^ 8 + s + 3 with hN
  have hN4 : N ≤ 4 * tp := by
    have : max (max E33.stabThreshold (16 * 10 ^ 100 * (s + 1) ^ 16))
        (E34.NeditE s (epsS s ^ 4 / (2 ^ 19 * ((s : ℚ) + 1)))) ≤ tp :=
      max_le (max_le hstab hc16) hed
    omega
  -- `Fexp ≤ tp^4 ≤ tower2 (p+1)`
  clear_value N tp p X Y
  have hF : N + (N * N + 1) * 10 ^ 41 * (s + 1) ^ 8 + 1 ≤ tp ^ 4 := by
    rw [mul_assoc]
    exact fexp_arith N tp _ h22 hN4 hc41
  have hp3 : 3 ≤ p := by omega
  rw [htp] at hF
  refine hF.trans ((tower2_pow_four_le p hp3).trans (tower2_mono ?_))
  -- `p + 1 ≤ Ptower s`
  unfold Ptower cT
  rw [← hX]
  have e : (E18.Numeric.hIter + cFar + 841780) * X
      = E18.Numeric.hIter * X + cFar * X + 841780 * X := by ring
  rw [e]
  have a1 : E18.Numeric.hIter ≤ E18.Numeric.hIter * X := Nat.le_mul_of_pos_right _ hX1
  have a2 : 3 * Y + 10 ≤ 841780 * X := by
    rw [hY]; unfold Yedit Eedit; omega
  omega

/-! ## T3: Theorem C above the tower -/

open PaperIV.FarRounding PaperIV.RootedSimplicialDefect PaperIV.DefectTargetArithmetic in
/-- **T3: Theorem C above `tower2 (Ptower s)`.**  Every graph of order `n ≥ tower2 (Ptower s)`
with a rooted simplicial defect of size `s` has an order-`≤ 4` clique partition of size at most
`defectTarget s n`. -/
theorem theoremC_tower (s n : ℕ) (hn : tower2 (Ptower s) ≤ n)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hdef : RootedDefectAt G s) :
    ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ defectTarget s n :=
  E34.theoremC_fully_explicit_final s n ((Fexp_le_tower s).trans hn) G hdef

open PaperIV.FarRounding PaperIV.RootedSimplicialDefect PaperIV.DefectTargetArithmetic in
/-- **T3, uniform form**: if `tower2 (Ptower S) ≤ n` then Theorem C holds at order `n` for all
defects `s ≤ S` simultaneously. -/
theorem theoremC_tower_uniform (n S : ℕ) (hn : tower2 (Ptower S) ≤ n) :
    ∀ s : ℕ, s ≤ S → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      RootedDefectAt G s →
        ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ defectTarget s n := by
  intro s hs G _ hdef
  exact theoremC_tower s n ((tower2_mono (Ptower_mono hs)).trans hn) G hdef

/-- The largest defect covered at order `n`: `sMaxT n = max {S ≤ n | tower2 (Ptower S) ≤ n}`
(an explicit inverse of `S ↦ tower2 (Ptower S)`). -/
def sMaxT (n : ℕ) : ℕ := Nat.findGreatest (fun S => tower2 (Ptower S) ≤ n) n

theorem tower2_Ptower_sMaxT_le {n : ℕ} (h0 : tower2 (Ptower 0) ≤ n) :
    tower2 (Ptower (sMaxT n)) ≤ n :=
  Nat.findGreatest_spec (P := fun S => tower2 (Ptower S) ≤ n) (Nat.zero_le n) h0

open PaperIV.FarRounding PaperIV.RootedSimplicialDefect PaperIV.DefectTargetArithmetic in
/-- **T3, uniform form with the explicit inverse**: for `n ≥ tower2 (Ptower 0)`, Theorem C holds
at order `n` for all defects `s ≤ sMaxT n`. -/
theorem theoremC_tower_uniform_sMax (n : ℕ) (h0 : tower2 (Ptower 0) ≤ n) :
    ∀ s : ℕ, s ≤ sMaxT n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      RootedDefectAt G s →
        ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ defectTarget s n :=
  theoremC_tower_uniform n (sMaxT n) (tower2_Ptower_sMaxT_le h0)

end E35

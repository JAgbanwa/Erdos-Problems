/-
# Nibble — the arithmetic behind the refined Dross cut condition

This file isolates the *pure real-arithmetic* core of the refined cut estimate that upgrades the
uniform transfer certificate of `Nibble/DrossFlowDense.lean` from minimum degree `(15/16)|V|` all
the way down to the Dross density `(9/10)|V|`.

Write `n = |V|`, and for an edge `e` let `σ(e) = n - 2 - codeg(e)` be its *codegree defect*.  For a
cut `S` of the edge set write `K = |S|`, `L = |Sᶜ|`, `m = K + L = |E|`, `A = ∑_{e ∈ S} σ(e)`,
`C = ∑_{e ∉ S} σ(e)`, and let `X` be the number of opposite pairs crossing the cut.  The cut
condition for the balanced base weight is exactly `3n(LA - KC) ≤ 2mX` (the base weight cancels),
and `Nibble.cut_master` derives it from six combinatorial inputs.

The heart of the matter is `Nibble.cutT_nonneg`, a concavity-in-`m` interpolation between two
explicit polynomial certificates (`Nibble.cutT_nonneg_left`, `Nibble.cutT_nonneg_right`).

Sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Real.StarOrdered
import Mathlib.Tactic.Bound
import Mathlib.Tactic.Positivity

namespace Nibble

/-! ### The concave envelope `φ` -/

/-- `cutPhi n t` is the bound `(t+2)(21n/20) - t - t²/2` on the number of edges of `G` that are
*not* opposite partners of an edge with codegree defect `t`. -/
noncomputable def cutPhi (n t : ℝ) : ℝ := (t + 2) * (21 * n / 20) - t - t ^ 2 / 2

/-- `cutT n g d m` is the quantity whose nonnegativity rules out a deficient cut.  It is quadratic
in `m` with leading coefficient `-(17n/10 + g)`. -/
noncomputable def cutT (n g d m : ℝ) : ℝ :=
  (17 * n / 20) * (n * (n - 1) - 2 * m) * (m - (3 / 2) * n * d)
    - m * ((n / 5 - 2) * cutPhi n g + g * (m - (3 / 2) * n * d))

/-! ### The two endpoint certificates -/

/-- The explicit positive combination certifying the left endpoint `m = (9/20)n²`. -/
theorem cutSOS_left_core (n g w s t r : ℝ) (hn : 0 ≤ n) (hg : 0 ≤ g) (hw : 0 ≤ w)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hr : 0 ≤ r) :
    0 ≤ (1561/12750) * (n^4) +
      (168557/204000) * (w*n^4) +
      (3227/10200) * (s*n^3) +
      (121/4250) * (t*n^3) +
      (82/1275) * (r*n^3) +
      (97/1020) * (g*s*n^2) +
      (181/5100) * (g*t*n^2) +
      (1549/102000) * (g*t*n^3) +
      (1519/3400) * (g*r*n^3) +
      (3227/20400) * (w*w*n^3) +
      (361/8160) * (w*t*n^3) +
      (97/102000) * (t*t*n^2) +
      (97/2040) * (g*g*g*n^2) +
      (181/10200) * (g*g*t*n^2) +
      (97/2040) * (g*w*w*n^2) +
      (97/20400) * (w*w*t*n^2) +
      (97/20400) * (w*t*r*n^2) +
      (97/204000) * (t*t*r*n^2) := by positivity

/-- The explicit positive combination certifying the right endpoint `m = m₂`. -/
theorem cutSOS_right_core (n g w s t r : ℝ) (hn : 0 ≤ n) (hg : 0 ≤ g) (hw : 0 ≤ w)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hr : 0 ≤ r) :
    0 ≤ (83979501/44000000) * (n^3) +
      (79149/11000000) * (n^4) +
      (9441961/88000000000) * (n^5) +
      (6002847/2000000) * (g*n^3) +
      (5011958319/616000000) * (w*n^3) +
      (36071605701/43120000000) * (w*n^4) +
      (812483481/156800000) * (g*w*n^3) +
      (9853/40000) * (g*t*n^2) +
      (14560731/7840000) * (w*s*n^2) +
      (2) * (s*s) +
      (17/200) * (s*t*n^1) +
      (2510357/88000000) * (s*t*n^2) +
      (9853/8000) * (g*g*g*n^2) +
      (10442009/7840000) * (g*w*w*n^2) +
      (1) * (g*w*s) +
      (14165643/88000000) * (g*w*t*n^2) +
      (786069/15680000) * (g*w*r*n^2) +
      (1) * (g*s*r) +
      (39/40) * (g*s*r*n^1) +
      (33862243/176000000) * (g*t*r*n^2) +
      (59/40) * (w*w*s*n^1) +
      (786069/15680000) * (w*w*r*n^2) +
      (1) * (w*s*s) +
      (21/40) * (w*s*r*n^1) +
      (16145643/176000000) * (w*t*r*n^2) +
      (1) * (s*s*r) +
      (59/400) * (s*t*r*n^1) +
      (2639269/3200000) * ((g - (1/50)*n)^2*n^3) +
      (21/40) * ((g - (17/200)*n)^2*s*n^1)
 := by positivity

/-- **Left endpoint.**  At `m = (9/20)n²` the quantity `cutT` is nonnegative. -/
theorem cutT_nonneg_left (n g d : ℝ) (hn : 20 ≤ n) (hg : 0 ≤ g) (hd : 0 ≤ d)
    (hgd : g + d ≤ n / 5 - 2)
    (hS : (9 / 20) * n ^ 2 ≤ cutPhi n (g + d) + cutPhi n g + (3 / 2) * n * d) :
    0 ≤ cutT n g d ((9 / 20) * n ^ 2) := by
  have h := cutSOS_left_core n g (n / 5 - 2 - g - d)
    (cutPhi n (g + d) + cutPhi n g + (3 / 2) * n * d - (9 / 20) * n ^ 2) (n - 20) d
    (by linarith) hg (by linarith) (by linarith) (by linarith) hd
  simp only [cutPhi] at h
  simp only [cutT, cutPhi]
  linarith only [h]

/-- **Right endpoint.**  At `m = m₂` the quantity `cutT` is nonnegative. -/
theorem cutT_nonneg_right (n g d : ℝ) (hn : 20 ≤ n) (hg : 0 ≤ g) (hd : 0 ≤ d)
    (hgd : g + d ≤ n / 5 - 2)
    (hS : (9 / 20) * n ^ 2 ≤ cutPhi n (g + d) + cutPhi n g + (3 / 2) * n * d) :
    0 ≤ cutT n g d (cutPhi n (g + d) + cutPhi n g + (3 / 2) * n * d) := by
  have h := cutSOS_right_core n g (n / 5 - 2 - g - d)
    (cutPhi n (g + d) + cutPhi n g + (3 / 2) * n * d - (9 / 20) * n ^ 2) (n - 20) d
    (by linarith) hg (by linarith) (by linarith) (by linarith) hd
  simp only [cutPhi] at h
  simp only [cutT, cutPhi]
  linarith only [h]

/-! ### Concavity interpolation -/

/-- **The interpolation.**  `cutT n g d ·` is a concave quadratic in its last argument, so its
nonnegativity at `m = (9/20)n²` and at `m = m₂` propagates to every `m` in between. -/
theorem cutT_nonneg (n g d m : ℝ) (hn : 20 ≤ n) (hg : 0 ≤ g) (hd : 0 ≤ d)
    (hgd : g + d ≤ n / 5 - 2) (hm1 : (9 / 20) * n ^ 2 ≤ m)
    (hm2 : m < cutPhi n (g + d) + cutPhi n g + (3 / 2) * n * d) :
    0 ≤ cutT n g d m := by
  set M1 : ℝ := (9 / 20) * n ^ 2 with hM1
  set M2 : ℝ := cutPhi n (g + d) + cutPhi n g + (3 / 2) * n * d with hM2
  have hS : M1 ≤ M2 := le_trans hm1 hm2.le
  have h1 := cutT_nonneg_left n g d hn hg hd hgd hS
  have h2 := cutT_nonneg_right n g d hn hg hd hgd hS
  have key : (M2 - M1) * cutT n g d m
      = (M2 - m) * cutT n g d M1 + (m - M1) * cutT n g d M2
        + (M2 - M1) * ((17 * n / 10 + g) * ((m - M1) * (M2 - m))) := by
    simp only [cutT]; ring
  have hlt : 0 < M2 - M1 := by linarith only [hm1, hm2]
  have hnn : 0 ≤ (M2 - M1) * cutT n g d m := by
    rw [key]
    have t1 : 0 ≤ (M2 - m) * cutT n g d M1 :=
      mul_nonneg (by linarith) h1
    have t2 : 0 ≤ (m - M1) * cutT n g d M2 :=
      mul_nonneg (by linarith) h2
    have t3 : 0 ≤ (M2 - M1) * ((17 * n / 10 + g) * ((m - M1) * (M2 - m))) :=
      mul_nonneg hlt.le (mul_nonneg (by linarith)
        (mul_nonneg (by linarith) (by linarith)))
    linarith only [t1, t2, t3]
  exact le_of_mul_le_mul_left (by linarith only [hnn]) hlt

/-! ### Nonnegativity of `φ` -/

theorem cutPhi_nonneg {n t : ℝ} (hn : 20 ≤ n) (ht : 0 ≤ t) (htq : t ≤ n / 5 - 2) :
    0 ≤ cutPhi n t := by
  simp only [cutPhi]
  nlinarith only [ht, htq]

/-! ### The master cut inequality -/

set_option maxHeartbeats 400000 in
/-- **The master cut inequality.**  The six combinatorial inputs on the left force the cut
condition `3n(LA - KC) ≤ 2mX` at the Dross density. -/
theorem cut_master {n K L A C X : ℝ}
    (hn : 20 ≤ n) (hK : 0 ≤ K) (hL : 0 ≤ L) (hA0 : 0 ≤ A) (hC0 : 0 ≤ C)
    (hA : A ≤ (n / 5 - 2) * K) (hC : C ≤ (n / 5 - 2) * L)
    (hAC : (17 * n / 20) * (n * (n - 1) - 2 * (K + L)) ≤ A + C)
    (hm1 : (9 / 20) * n ^ 2 ≤ K + L)
    (hX0 : 0 ≤ X)
    (hXK : 2 * K * (K * L - (A + 2 * K) * (21 * n / 20) + A) + A ^ 2 ≤ 2 * K * X)
    (hXL : 2 * L * (K * L - (C + 2 * L) * (21 * n / 20) + C) + C ^ 2 ≤ 2 * L * X) :
    3 * n * (L * A - K * C) ≤ 2 * (K + L) * X := by
  rcases eq_or_lt_of_le hK with hK0 | hKpos
  · have hA' : A = 0 := le_antisymm (by rw [← hK0] at hA; linarith) hA0
    rw [hA', ← hK0]
    have : 0 ≤ 2 * (0 + L) * X := by
      have : (0:ℝ) ≤ 2 * (0 + L) := by linarith only [hL]
      exact mul_nonneg this hX0
    linarith only [this]
  rcases eq_or_lt_of_le hL with hL0 | hLpos
  · have hC' : C = 0 := le_antisymm (by rw [← hL0] at hC; linarith) hC0
    rw [hC', ← hL0]
    have : 0 ≤ 2 * (K + 0) * X := by
      have : (0:ℝ) ≤ 2 * (K + 0) := by linarith only [hKpos]
      exact mul_nonneg this hX0
    linarith only [this]
  have hmpos : 0 < K + L := by linarith only [hKpos, hLpos]
  set m : ℝ := K + L with hm
  set al : ℝ := A / K with hal
  set ga : ℝ := C / L with hga
  have hAeq : A = al * K := by rw [hal]; field_simp
  have hCeq : C = ga * L := by rw [hga]; field_simp
  have hal0 : 0 ≤ al := div_nonneg hA0 hK
  have hga0 : 0 ≤ ga := div_nonneg hC0 hL
  have halq : al ≤ n / 5 - 2 := by rw [hal, div_le_iff₀ hKpos]; linarith only [hA]
  have hgaq : ga ≤ n / 5 - 2 := by rw [hga, div_le_iff₀ hLpos]; linarith only [hC]
  have hn0 : (0:ℝ) < n := by linarith only [hga0, hgaq]
  rcases le_or_gt al ga with hag | hag
  · have hle : L * A - K * C ≤ 0 := by
      rw [hAeq, hCeq]
      nlinarith only [mul_nonneg hK hL, hag]
    have h1 : 0 ≤ 3 * n * (-(L * A - K * C)) := mul_nonneg (by linarith) (by linarith)
    have h2 : 0 ≤ 2 * m * X := mul_nonneg (by linarith) hX0
    linarith only [h1, h2]
  -- the two flow bounds on `X`
  have hXal : K * L - K * cutPhi n al ≤ X := by
    have h2 : 2 * K * (K * L - K * cutPhi n al) ≤ 2 * K * X := by
      simp only [cutPhi]
      rw [hAeq] at hXK
      linarith only [hXK]
    exact le_of_mul_le_mul_left h2 (by linarith)
  have hXga : K * L - L * cutPhi n ga ≤ X := by
    have h2 : 2 * L * (K * L - L * cutPhi n ga) ≤ 2 * L * X := by
      simp only [cutPhi]
      rw [hCeq] at hXL
      linarith only [hXL]
    exact le_of_mul_le_mul_left h2 (by linarith)
  set Y : ℝ := m - (3 / 2) * n * (al - ga) with hYdef
  have hYpos : 0 < Y := by
    rw [hYdef]
    linarith only [hm1, hn, sq_nonneg n,
      mul_le_mul_of_nonneg_left (show al - ga ≤ n / 5 - 2 by linarith only [halq, hga0])
        (show (0 : ℝ) ≤ 3 / 2 * n by linarith only [hn])]
  have hgoal : 3 * n * (L * A - K * C) = 3 * n * (K * L * (al - ga)) := by
    rw [hAeq, hCeq]; ring
  rcases le_or_gt (m * cutPhi n al) (L * Y) with h1 | h1
  · rw [hgoal]
    have e1 : 2 * m * (K * L - K * cutPhi n al) ≤ 2 * m * X :=
      mul_le_mul_of_nonneg_left hXal (by linarith)
    have e2 : 2 * K * (m * cutPhi n al) ≤ 2 * K * (L * Y) :=
      mul_le_mul_of_nonneg_left h1 (by linarith)
    rw [hYdef] at e2
    linarith only [e1, e2]
  rcases le_or_gt (m * cutPhi n ga) (K * Y) with h2 | h2
  · rw [hgoal]
    have e1 : 2 * m * (K * L - L * cutPhi n ga) ≤ 2 * m * X :=
      mul_le_mul_of_nonneg_left hXga (by linarith)
    have e2 : 2 * L * (m * cutPhi n ga) ≤ 2 * L * (K * Y) :=
      mul_le_mul_of_nonneg_left h2 (by linarith)
    rw [hYdef] at e2
    linarith only [e1, e2]
  exfalso
  have hsum : m * Y < m * (cutPhi n al + cutPhi n ga) := by
    have hKL : K * Y + L * Y < m * cutPhi n ga + m * cutPhi n al := by linarith only [h1, h2]
    linarith only [hKL, hm]
  have hT0 : Y < cutPhi n al + cutPhi n ga := lt_of_mul_lt_mul_left hsum (by linarith)
  have hgaal : ga + (al - ga) = al := by ring
  have hT := cutT_nonneg n ga (al - ga) m hn hga0 (by linarith) (by linarith)
    (by rw [hm]; linarith) (by rw [hgaal]; rw [hYdef] at hT0; linarith)
  simp only [cutT] at hT
  have hYm : m - (3 / 2) * n * (al - ga) = Y := hYdef.symm
  rw [hYm] at hT
  -- `hT : 0 ≤ (17n/20)(n(n-1) - 2m) * Y - m*((n/5-2) * cutPhi n ga + ga * Y)`
  have hphiga : 0 ≤ cutPhi n ga := cutPhi_nonneg hn hga0 hgaq
  have hLm : L ≤ m := by rw [hm]; linarith only [hKpos]
  have hstep1 : al * (K * Y) < al * (m * cutPhi n ga) := by
    have : 0 < al := lt_of_le_of_lt hga0 hag
    exact mul_lt_mul_of_pos_left h2 this
  have hstep2 : al * (m * cutPhi n ga) ≤ (n / 5 - 2) * (m * cutPhi n ga) :=
    mul_le_mul_of_nonneg_right halq (mul_nonneg (by linarith) hphiga)
  have hstep3 : ga * (L * Y) ≤ ga * (m * Y) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hLm hYpos.le) hga0
  have hRY : (17 * n / 20) * (n * (n - 1) - 2 * m) * Y ≤ (A + C) * Y :=
    mul_le_mul_of_nonneg_right (by rw [hm] at hAC ⊢; linarith) hYpos.le
  rw [hAeq, hCeq] at hRY
  nlinarith only [hT, hstep1, hstep2, hstep3, hRY]

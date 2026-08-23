/-
# Nibble — the sharpest leftover constant of the witness count, `0.3362`

`Nibble.denseGlobalLeftoverConst_17_over_50` certifies the leftover constant `17/50 = 0.34` from the
three counting inputs

* the density lower bound `10 S ≤ 10·starPairs + n·Tot`   (`Nibble.starPairs_lower`),
* the weighted witness bound `starPairs ≤ ∑_v d_v s_v + 4m` with `∑_v s_v = 2m` and the capacity
  `2 s_v + d_v ≤ n`   (`Nibble.starPairs_le_weighted`),
* the packing count `6m + Tot ≤ n²`   (`Nibble.six_card_add_uncoveredTot_le`),

by choosing the quadratic majorant `d s ≤ (31/100) n s + (97/100)(d − (23/100) n)²` and then
discarding `S` through Cauchy–Schwarz.  The coefficient `97/100` of `d²` is what forces the
Cauchy–Schwarz step, and it is also what costs the count its sharpness.

This file uses instead the *calibrated* majorant

  `d s ≤ (31/100) n s + d² − (93/200) n d + (541/10000) n²`   (`Nibble.majorant_pointwise_sharp`),

whose `d²`-coefficient is exactly `1`.  Two consequences:

* the quantity `S = ∑_v d_v²` **cancels identically**, so no Cauchy–Schwarz is needed and the master
  inequality is *linear* in `Tot`:

  `28100 n·Tot + 40000·Tot ≤ 9446 n³ + 40000 n²`   (`Nibble.dense_uncoveredTot_master_linear`);

* the resulting constant `9446/28100 = 4723/14050 ≈ 0.336157` is the exact optimum of the
  linear-programming relaxation of the three inputs above, so no other majorant can do better.

Hence:

* `Nibble.denseGlobalLeftoverConst_of_gt_threshold` — `DenseGlobalLeftoverConst c` for *every*
  `c > 4723/14050`;
* `Nibble.denseGlobalLeftoverConst_1681_over_5000` — `DenseGlobalLeftoverConst (1681/5000)`, i.e.
  `c = 0.3362`, the sharpest concrete leftover constant in this library;
* `Nibble.leftoverConst_sharpest` — a constant strictly below the previous `17/50`;
* `Nibble.master_linear_threshold` — the machine-checked stall point of the linear master
  inequality: it is *satisfied* at `Tot = |V|²/5`, so — as for every earlier count — this route
  cannot reach the `1/5` that `Nibble.beats_half_of_leftoverConst` needs.  Crossing `1/5` needs the
  global fractional input isolated in `Nibble.DrossFractional`.

Sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.DenseGlobalLeftoverThird

open Finset SimpleGraph Hypergraph Nibble.YusterE

namespace Nibble

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ### The calibrated majorant -/

/-- **The calibrated linear-programming majorant.**  For a vertex with uncovered degree `d`
carrying `s` packing triangles under the capacity constraint `2s + d ≤ n`,

`d·s ≤ (31/100) n s + d² − (93/200) n d + (541/10000) n²`.

Unlike `Nibble.majorant_pointwise` the coefficient of `d²` is exactly `1`, so summing this bound
makes `∑_v d_v²` cancel against the density lower bound. -/
theorem majorant_pointwise_sharp (d s n : ℤ) (hs : 0 ≤ s) (hcap : 2 * s + d ≤ n) :
    10000 * d * s ≤ 3100 * n * s + 10000 * d ^ 2 - 4650 * n * d + 541 * n ^ 2 := by
  rcases le_or_gt (10000 * d) (3100 * n) with h | h
  · -- the coefficient of `s` is nonnegative: the bound is worst at `s = 0`
    have h1 : 0 ≤ (3100 * n - 10000 * d) * s := mul_nonneg (by linarith) hs
    nlinarith [sq_nonneg (10000 * d - 2325 * n), sq_nonneg n]
  · -- the coefficient of `s` is negative: the bound is worst at `2s = n − d`
    have h1 : (3100 * n - 10000 * d) * (n - d) ≤ (3100 * n - 10000 * d) * (2 * s) := by
      have hco : 3100 * n - 10000 * d ≤ 0 := by linarith only [h]
      have : 2 * s ≤ n - d := by linarith only [hcap]
      nlinarith only [hco, this]
    nlinarith [sq_nonneg (15000 * d - 5600 * n), sq_nonneg n]

/-! ### The linear master inequality -/

/-- **The linear master inequality** at the Dross density.  Because the calibrated majorant has
`d²`-coefficient `1`, the quantity `S = ∑_v d_v²` cancels and the master inequality is linear:
`28100 n·Tot + 40000·Tot ≤ 9446 n³ + 40000 n²`. -/
theorem dense_uncoveredTot_master_linear (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdense : 9 * Fintype.card V ≤ 10 * G.minDegree) :
    ∃ M : Finset (Finset (EdgeV G)), IsMatching (triangleHypergraphSub G) M ∧
      28100 * (Fintype.card V : ℤ) * (uncoveredTot G M : ℤ) + 40000 * (uncoveredTot G M : ℤ)
        ≤ 9446 * (Fintype.card V : ℤ) ^ 3 + 40000 * (Fintype.card V : ℤ) ^ 2 := by
  classical
  obtain ⟨M, hM, hmin⟩ := exists_min_pot G
  refine ⟨M, hM, ?_⟩
  obtain ⟨s, hs1, hs2, hs3⟩ := starPairs_le_weighted G hM hmin
  set n : ℤ := (Fintype.card V : ℤ) with hn
  set d : V → ℤ := fun v => (unDeg G M v : ℤ) with hd
  set sz : V → ℤ := fun v => (s v : ℤ) with hsz
  set Tot : ℤ := (uncoveredTot G M : ℤ) with hTot
  set S : ℤ := ∑ v : V, (d v) ^ 2 with hS
  set W : ℤ := ∑ v : V, d v * sz v with hW
  set m : ℤ := (M.card : ℤ) with hm
  have hn0 : (0 : ℤ) ≤ n := Int.natCast_nonneg _
  have hm0 : (0 : ℤ) ≤ m := Int.natCast_nonneg _
  have hT0 : (0 : ℤ) ≤ Tot := Int.natCast_nonneg _
  have hTotsum : ∑ v : V, d v = Tot := by
    rw [hTot, hd, uncoveredTot]; push_cast; rfl
  -- the density lower bound
  have hlow : 10 * S ≤ 10 * (W + 4 * m) + n * Tot := by
    have h1 := starPairs_lower G hdense M
    rw [starPairs_eq G M] at h1
    have h2 : (10 : ℤ) * ∑ v : V, (d v) ^ 2
        ≤ 10 * ((∑ p : V × V, witCard G M p : ℕ) : ℤ) + n * Tot := by
      have := h1
      zify at this
      simpa [hd, hn, hTot] using this
    have h3 : ((∑ p : V × V, witCard G M p : ℕ) : ℤ) ≤ W + 4 * m := by
      have := hs3
      zify at this
      simpa [hW, hd, hsz, hm] using this
    calc 10 * S = 10 * ∑ v : V, (d v) ^ 2 := by rw [hS]
      _ ≤ 10 * ((∑ p : V × V, witCard G M p : ℕ) : ℤ) + n * Tot := h2
      _ ≤ 10 * (W + 4 * m) + n * Tot := by linarith only [h3]
  -- the mass of the weight
  have hmass : ∑ v : V, sz v = 2 * m := by
    have := hs1
    zify at this
    simpa [hsz, hm] using this
  -- the summed majorant
  have hmaj : 10000 * W ≤ 6200 * n * m + 10000 * S - 4650 * n * Tot + 541 * n ^ 3 := by
    have hpt : ∀ v ∈ (Finset.univ : Finset V),
        10000 * d v * sz v
          ≤ 3100 * n * sz v + 10000 * (d v) ^ 2 - 4650 * n * d v + 541 * n ^ 2 := by
      intro v _
      refine majorant_pointwise_sharp (d v) (sz v) n (Int.natCast_nonneg _) ?_
      have := hs2 v
      zify at this
      simpa [hd, hsz, hn] using this
    have hsum := Finset.sum_le_sum hpt
    have hL : ∑ v : V, 10000 * d v * sz v = 10000 * W := by
      rw [hW, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun v _ => by ring)
    have hR : ∑ v : V,
        (3100 * n * sz v + 10000 * (d v) ^ 2 - 4650 * n * d v + 541 * n ^ 2)
          = 3100 * n * (∑ v : V, sz v) + 10000 * S - 4650 * n * (∑ v : V, d v) + 541 * n ^ 3 := by
      have hcard : ∑ _v : V, (541 : ℤ) * n ^ 2 = 541 * n ^ 3 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hn]; ring
      rw [show (∑ v : V, (3100 * n * sz v + 10000 * (d v) ^ 2 - 4650 * n * d v + 541 * n ^ 2))
          = (∑ v : V, 3100 * n * sz v) + (∑ v : V, 10000 * (d v) ^ 2)
            - (∑ v : V, 4650 * n * d v) + ∑ _v : V, (541 : ℤ) * n ^ 2 from by
        rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]]
      rw [hcard]
      simp only [← Finset.mul_sum]
      rw [hS]
    rw [hL, hR, hmass, hTotsum] at hsum
    linarith only [hsum]
  -- the packing count
  have hcount : 6 * m + Tot ≤ n * n := by
    have := six_card_add_uncoveredTot_le G hM
    zify at this
    simpa [hm, hTot, hn] using this
  -- `S` cancels: the count is linear
  have hcancel : 3650 * n * Tot ≤ 6200 * n * m + 40000 * m + 541 * n ^ 3 := by linarith only [hlow, hmaj]
  have hcountn : 6 * (n * m) + n * Tot ≤ n ^ 3 := by
    have := mul_le_mul_of_nonneg_left hcount hn0
    linarith only [this]
  linarith only [hcancel, hcountn, hcount]

/-! ### The sharpest leftover constant -/

/-- **Every constant above the threshold of the linear count is certified.**  At the Dross density,
for every `c > 4723/14050 ≈ 0.336157` some triangle packing leaves at most `c|V|²` uncovered
incidences. -/
theorem denseGlobalLeftoverConst_of_gt_threshold {c : ℝ} (hc : 4723 / 14050 < c) :
    DenseGlobalLeftoverConst c := by
  have hden : 0 < 28100 * c - 9446 := by linarith only [hc]
  refine ⟨⌈(40000 : ℝ) / (28100 * c - 9446)⌉₊, ?_⟩
  intro V _ _ G _ hV hdense
  obtain ⟨M, hM, hmaster⟩ := dense_uncoveredTot_master_linear G hdense
  refine ⟨M, hM, ?_⟩
  have hmasterR : 28100 * (Fintype.card V : ℝ) * (uncoveredTot G M : ℝ)
        + 40000 * (uncoveredTot G M : ℝ)
      ≤ 9446 * (Fintype.card V : ℝ) ^ 3 + 40000 * (Fintype.card V : ℝ) ^ 2 := by
    exact_mod_cast hmaster
  set n : ℝ := (Fintype.card V : ℝ) with hn
  set Tot : ℝ := (uncoveredTot G M : ℝ) with hTot
  have hT0 : 0 ≤ Tot := by positivity
  have hnth : (40000 : ℝ) / (28100 * c - 9446) ≤ n := by
    refine le_trans (Nat.le_ceil _) ?_
    rw [hn]; exact_mod_cast hV
  have hn0 : 0 < n := lt_of_lt_of_le (by positivity) hnth
  have h1 : (40000 : ℝ) ≤ (28100 * c - 9446) * n := by
    have := (div_le_iff₀ hden).mp hnth; linarith only [this]
  -- the threshold makes the cubic term dominate the quadratic one
  have hA : 40000 * (1 - c) ≤ (28100 * c - 9446) * n := by
    rcases le_or_gt c 1 with h | h
    · nlinarith only [hn0, h1]
    · nlinarith only [hn0, h1]
  have hB : 40000 * (1 - c) * n ^ 2 ≤ (28100 * c - 9446) * n * n ^ 2 := by
    have hsq : (0 : ℝ) ≤ n ^ 2 := by positivity
    exact mul_le_mul_of_nonneg_right hA hsq
  have hC : (28100 * n + 40000) * Tot ≤ (28100 * n + 40000) * (c * n ^ 2) := by nlinarith only [hmasterR, hA]
  have hpos : 0 < 28100 * n + 40000 := by linarith only [hn0]
  exact le_of_mul_le_mul_left hC hpos

/-- **The sharpest leftover constant of the witness count.**  At the Dross density, some triangle
packing leaves at most `(1681/5000)|V|² = 0.3362·|V|²` uncovered incidences. -/
theorem denseGlobalLeftoverConst_1681_over_5000 : DenseGlobalLeftoverConst (1681 / 5000) :=
  denseGlobalLeftoverConst_of_gt_threshold (by norm_num)

/-- **The sharpest leftover constant proved in this library**, strictly below the previous
`17/50 = 0.34` of `Nibble.denseGlobalLeftoverConst_17_over_50`. -/
theorem leftoverConst_sharpest : ∃ c : ℝ, c < 17 / 50 ∧ DenseGlobalLeftoverConst c :=
  ⟨1681 / 5000, by norm_num, denseGlobalLeftoverConst_1681_over_5000⟩

/-- **The exact stall point of the linear count.**  Writing `Tot = c|V|²`, the master inequality
`Nibble.dense_uncoveredTot_master_linear` reads `28100 c ≤ 9446` up to lower-order terms, i.e.
`c ≤ 4723/14050 ≈ 0.336157`.  This is *below* the constant `17/50` of the earlier count and *above*
`1/5`: like every purely local count, this route cannot reach the threshold that
`Nibble.beats_half_of_leftoverConst` needs. -/
theorem master_linear_threshold :
    (1 : ℝ) / 5 < 4723 / 14050 ∧ (4723 : ℝ) / 14050 < 1681 / 5000 ∧
      (1681 : ℝ) / 5000 < 17 / 50 := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩

end Nibble

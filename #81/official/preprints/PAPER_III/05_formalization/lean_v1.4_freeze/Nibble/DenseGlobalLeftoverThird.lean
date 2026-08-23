/-
# Nibble — sharpening the leftover constant to `17/50`

`Nibble.denseGlobalLeftoverConst_377_over_1000` bounds the witness count of a packing triangle by
the *global* maximum uncovered star `D ≤ (|V| + 4)/2`.  This file replaces that crude input by two
sharper ones and pushes the leftover constant from `377/1000 ≈ 0.3770` down to `17/50 = 0.34`.

The two new inputs, for a potential-minimal matching `M` (write `d_v` for the uncovered star size
at `v`, `Tot = ∑_v d_v`, `S = ∑_v d_v²`, `m = |M|`, `n = |V|`):

* `Nibble.witness_pair_bound` — the witnesses of a packing triangle all sit on *one* of its edges
  `pq`, so their number is at most `min(d_p, d_q) ≤ (d_p + d_q)/2`, not `D`;
* `Nibble.two_mul_card_triAt_add_unDeg_le` — the **capacity** bound `2 t_v + d_v ≤ deg_G v ≤ n`,
  where `t_v` counts the packing triangles through `v`: a triangle through `v` eats two covered
  edges at `v`.

Writing `s_v` for the number of packing triangles whose witness-carrying edge contains `v`
(so `∑_v s_v = 2m` and `2 s_v + d_v ≤ n`), the count of `Nibble.DenseGlobalLeftoverBelowHalf`
becomes

  `10 S ≤ 10 (∑_v d_v s_v + 4m) + n Tot`.

The linear-programming bound `d_v s_v ≤ (31/100) n s_v + (97/100)(d_v − (23/100) n)²`
(`Nibble.majorant_pointwise`, a single quadratic majorant valid for all `0 ≤ 2 s_v ≤ n − d_v`)
turns this into the master inequality

  `90000 Tot² + 1348600 n² Tot ≤ 463939 n⁴ + 2000000 n³`   (`Nibble.dense_uncoveredTot_master_sharp`)

which forces `Tot ≤ (17/50)|V|²` for large `|V|`:

* `Nibble.denseGlobalLeftoverConst_17_over_50` — `DenseGlobalLeftoverConst (17/50)`;
* `Nibble.leftoverConst_sharp` — the sharpest constant proved here;
* `Nibble.master_sharp_threshold` — the machine-checked stall point: the master inequality is
  *satisfied* at `Tot = |V|²/5`, so this count cannot reach the `1/5` that
  `Nibble.beats_half_of_leftoverConst` would need.

Sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.WitnessPair

open Finset SimpleGraph Hypergraph Nibble.YusterE

namespace Nibble

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ### The weighted witness bound -/

/-- **The weighted witness bound.**  There is a weight `s` on the vertices — the number of packing
triangles whose witness-carrying edge contains the vertex — with total mass `2m`, obeying the
capacity bound `2 s_v + d_v ≤ n`, and carrying the whole witness count. -/
theorem starPairs_le_weighted (G : SimpleGraph V) [DecidableRel G.Adj]
    {M : Finset (Finset (EdgeV G))} (hM : IsMatching (triangleHypergraphSub G) M)
    (hmin : ∀ M' : Finset (Finset (EdgeV G)), IsMatching (triangleHypergraphSub G) M' →
      uncoveredTot G M' ≤ uncoveredTot G M → uncoveredPot G M ≤ uncoveredPot G M') :
    ∃ s : V → ℕ,
      (∑ v : V, s v = 2 * M.card) ∧
      (∀ v : V, 2 * s v + unDeg G M v ≤ Fintype.card V) ∧
      (∑ p : V × V, witCard G M p ≤ (∑ v : V, unDeg G M v * s v) + 4 * M.card) := by
  classical
  have hex : ∀ T : Finset (EdgeV G), ∃ P : Finset V, T ∈ M →
      (P.card = 2 ∧ P ⊆ triOf G T ∧
        ∑ p ∈ (triOf G T) ×ˢ (triOf G T), witCard G M p ≤ (∑ v ∈ P, unDeg G M v) + 4) := by
    intro T
    by_cases hT : T ∈ M
    · obtain ⟨P, h1, h2, h3⟩ := witness_pair_bound G hM hmin hT
      exact ⟨P, fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨∅, fun h => absurd h hT⟩
  choose pk hpk using hex
  set s : V → ℕ := fun v => (M.filter (fun T => v ∈ pk T)).card with hs
  have hfilter : ∀ T : Finset (EdgeV G),
      (Finset.univ.filter (fun v : V => v ∈ pk T)) = pk T := by
    intro T; ext v; simp
  refine ⟨s, ?_, ?_, ?_⟩
  · -- total mass
    have h : ∀ v : V, s v = ∑ T ∈ M, (if v ∈ pk T then 1 else 0) := by
      intro v; rw [hs]; exact Finset.card_filter _ _
    simp_rw [h]
    rw [Finset.sum_comm]
    have h2 : ∀ T ∈ M, ∑ _v : V, (if _v ∈ pk T then 1 else 0) = 2 := by
      intro T hT
      rw [← Finset.card_filter, hfilter T, (hpk T hT).1]
    rw [Finset.sum_congr rfl h2, Finset.sum_const, smul_eq_mul, mul_comm]
  · -- capacity
    intro v
    have hsub : M.filter (fun T => v ∈ pk T) ⊆ triAt G M v := by
      intro T hT
      rw [Finset.mem_filter] at hT
      exact (mem_triAt G).mpr ⟨hT.1, (hpk T hT.1).2.1 hT.2⟩
    have hle : s v ≤ (triAt G M v).card := Finset.card_le_card hsub
    have hcap := two_mul_card_triAt_add_unDeg_le G hM v
    have hdeg := degree_le_card G v
    omega
  · -- the witness count
    have hstep := starPairs_le_triOf G hM hmin
    have hfib : ∀ T ∈ M, ∑ p ∈ (triOf G T) ×ˢ (triOf G T), witCard G M p
        ≤ (∑ v ∈ pk T, unDeg G M v) + 4 := fun T hT => (hpk T hT).2.2
    have h1 : ∑ T ∈ M, ∑ p ∈ (triOf G T) ×ˢ (triOf G T), witCard G M p
        ≤ ∑ T ∈ M, ((∑ v ∈ pk T, unDeg G M v) + 4) := Finset.sum_le_sum hfib
    have h2 : ∑ T ∈ M, ((∑ v ∈ pk T, unDeg G M v) + 4)
        = (∑ T ∈ M, ∑ v ∈ pk T, unDeg G M v) + 4 * M.card := by
      rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_comm]
    have h3 : ∑ T ∈ M, ∑ v ∈ pk T, unDeg G M v = ∑ v : V, unDeg G M v * s v := by
      have hin : ∀ T : Finset (EdgeV G), ∑ v ∈ pk T, unDeg G M v
          = ∑ v : V, (if v ∈ pk T then unDeg G M v else 0) := by
        intro T
        rw [← Finset.sum_filter, hfilter T]
      simp_rw [hin]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun v _ => ?_)
      rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
      simp only [hs]
      ring
    omega

/-! ### The quadratic majorant -/

/-- **The linear-programming majorant.**  For a vertex with uncovered degree `d` carrying `s`
packing triangles under the capacity constraint `2s + d ≤ n`,
`d·s ≤ (31/100) n s + (97/100) (d − (23/100) n)²`. -/
theorem majorant_pointwise (d s n : ℤ) (hs : 0 ≤ s) (hcap : 2 * s + d ≤ n) :
    10000 * (100 * d - 31 * n) * s ≤ 97 * (100 * d - 23 * n) ^ 2 := by
  rcases le_or_gt (100 * d) (31 * n) with h | h
  · have h1 : 10000 * (100 * d - 31 * n) * s ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by nlinarith) hs
    nlinarith [sq_nonneg (100 * d - 23 * n)]
  · have hpos : (0 : ℤ) < 100 * d - 31 * n := by linarith
    have hstep : 10000 * (100 * d - 31 * n) * s ≤ 5000 * (100 * d - 31 * n) * (n - d) := by
      linarith only [mul_nonneg (le_of_lt hpos) (by linarith : (0 : ℤ) ≤ n - d - 2 * s)]
    have key : 5000 * (100 * d - 31 * n) * (n - d) ≤ 97 * (100 * d - 23 * n) ^ 2 := by
      linarith only [sq_nonneg (2940000 * d - 1101200 * n), sq_nonneg n]
    linarith

/-! ### The sharpened master inequality -/

/-- **The sharpened master inequality** at the Dross density:
`90000 Tot² + 1348600 n² Tot ≤ 463939 n⁴ + 2000000 n³`. -/
theorem dense_uncoveredTot_master_sharp (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdense : 9 * Fintype.card V ≤ 10 * G.minDegree) :
    ∃ M : Finset (Finset (EdgeV G)), IsMatching (triangleHypergraphSub G) M ∧
      90000 * (uncoveredTot G M : ℤ) ^ 2
          + 1348600 * (Fintype.card V : ℤ) ^ 2 * (uncoveredTot G M : ℤ)
        ≤ 463939 * (Fintype.card V : ℤ) ^ 4 + 2000000 * (Fintype.card V : ℤ) ^ 3 := by
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
  -- the density lower bound
  have hlow : 10 * S ≤ 10 * ((W : ℤ) + 4 * m) + n * Tot := by
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
      _ ≤ 10 * (W + 4 * m) + n * Tot := by linarith
  -- the mass of the weight
  have hmass : ∑ v : V, sz v = 2 * m := by
    have := hs1
    zify at this
    simpa [hsz, hm] using this
  -- the summed majorant
  have hmaj : 1000000 * W - 620000 * n * m ≤ 970000 * S - 446200 * n * Tot + 51313 * n ^ 3 := by
    have hpt : ∀ v ∈ (Finset.univ : Finset V),
        10000 * (100 * d v - 31 * n) * sz v ≤ 97 * (100 * d v - 23 * n) ^ 2 := by
      intro v _
      refine majorant_pointwise (d v) (sz v) n (Int.natCast_nonneg _) ?_
      have := hs2 v
      zify at this
      simpa [hd, hsz, hn] using this
    have hsum := Finset.sum_le_sum hpt
    have hL : ∑ v : V, 10000 * (100 * d v - 31 * n) * sz v
        = 1000000 * W - (310000 * n) * ∑ v : V, sz v := by
      rw [hW, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun v _ => by ring)
    have hR : ∑ v : V, 97 * (100 * d v - 23 * n) ^ 2
        = 970000 * S - (446200 * n) * (∑ v : V, d v) + 51313 * n ^ 3 := by
      have hcard : ∑ _v : V, (51313 : ℤ) * n ^ 2 = 51313 * n ^ 3 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hn]
        ring
      rw [hS, Finset.mul_sum, Finset.mul_sum]
      rw [show (∑ v : V, 97 * (100 * d v - 23 * n) ^ 2)
          = (∑ v : V, 970000 * (d v) ^ 2) - (∑ v : V, 446200 * n * d v)
            + ∑ _v : V, (51313 : ℤ) * n ^ 2 from by
        rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun v _ => by ring)]
      rw [hcard, ← Finset.mul_sum]
    have hTotsum : ∑ v : V, d v = Tot := by
      rw [hTot, hd, uncoveredTot]
      push_cast
      rfl
    rw [hL, hR, hmass, hTotsum] at hsum
    linarith
  -- the packing count
  have hcount : 6 * m + Tot ≤ n * n := by
    have := six_card_add_uncoveredTot_le G hM
    zify at this
    simpa [hm, hTot, hn] using this
  -- Cauchy-Schwarz
  have hcs : Tot ^ 2 ≤ n * S := by
    have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset V)) (f := d)
    have hTotsum : ∑ v : V, d v = Tot := by
      rw [hTot, hd, uncoveredTot]; push_cast; rfl
    rw [hTotsum, Finset.card_univ] at h
    simpa [hS, hn] using h
  -- assembling
  have hA : 30000 * S + 346200 * n * Tot ≤ 51313 * n ^ 3 + 620000 * n * m + 4000000 * m := by
    linarith
  have hB : 1860000 * n * m ≤ 310000 * n ^ 3 - 310000 * n * Tot := by
    linarith only [mul_le_mul_of_nonneg_left hcount (by linarith : (0 : ℤ) ≤ 310000 * n)]
  have hC : 12000000 * m ≤ 2000000 * n ^ 2 := by linarith
  have hD : 90000 * S + 1348600 * n * Tot ≤ 463939 * n ^ 3 + 2000000 * n ^ 2 := by linarith
  have hE : 90000 * (n * S) + 1348600 * n ^ 2 * Tot ≤ 463939 * n ^ 4 + 2000000 * n ^ 3 := by
    linarith only [mul_le_mul_of_nonneg_left hD hn0]
  linarith only [hcs, hE]

/-! ### The leftover constant `17/50` -/

/-- **The sharpened leftover constant.**  At the Dross density, some triangle packing leaves at
most `(17/50)|V|²` uncovered incidences. -/
theorem denseGlobalLeftoverConst_17_over_50 : DenseGlobalLeftoverConst (17 / 50) := by
  refine ⟨5000, ?_⟩
  intro V _ _ G _ hV hdense
  obtain ⟨M, hM, hmaster⟩ := dense_uncoveredTot_master_sharp G hdense
  refine ⟨M, hM, ?_⟩
  have hmasterR : 90000 * (uncoveredTot G M : ℝ) ^ 2
        + 1348600 * (Fintype.card V : ℝ) ^ 2 * (uncoveredTot G M : ℝ)
      ≤ 463939 * (Fintype.card V : ℝ) ^ 4 + 2000000 * (Fintype.card V : ℝ) ^ 3 := by
    exact_mod_cast hmaster
  set n : ℝ := (Fintype.card V : ℝ) with hn
  set Tot : ℝ := (uncoveredTot G M : ℝ) with hTot
  have hn0 : (5000 : ℝ) ≤ n := by rw [hn]; exact_mod_cast hV
  have hT0 : 0 ≤ Tot := by positivity
  by_contra hcon
  push_neg at hcon
  nlinarith only [hcon, hmasterR, hn0, hT0, sq_nonneg (Tot - 17 / 50 * n ^ 2), sq_nonneg n]

/-- **The sharpest leftover constant proved here.** -/
theorem leftoverConst_sharp : ∃ c : ℝ, c < 1 / 2 ∧ DenseGlobalLeftoverConst c :=
  ⟨17 / 50, by norm_num, denseGlobalLeftoverConst_17_over_50⟩

/-- **Where the sharpened count stalls.**  Writing `Tot = c|V|²`, the master inequality
`Nibble.dense_uncoveredTot_master_sharp` reads `90000 c² + 1348600 c ≤ 463939` up to lower order
terms.  This *fails* at `c = 17/50`, which is why that constant is certified; but it *holds* at
`c = 1/5`, so the count cannot rule out a leftover of `|V|²/5` and therefore cannot reach the
threshold that `Nibble.beats_half_of_leftoverConst` needs. -/
theorem master_sharp_threshold :
    90000 * (1 / 5 : ℝ) ^ 2 + 1348600 * (1 / 5 : ℝ) < 463939 ∧
      463939 < 90000 * (17 / 50 : ℝ) ^ 2 + 1348600 * (17 / 50 : ℝ) := by
  constructor <;> norm_num

end Nibble

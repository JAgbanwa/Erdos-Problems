import PaperIV.FixedL4Localization
import PaperIV.IntegralStability
import PaperIV.LossBudget

/-!
# Fixed-`L = 4` localization at defect `0`, for every precision

This module proves `PaperIV.FixedL4.FixedL4Localization 0`: for **every**
`ε > 0` there are `η > 0` and `N` such that every graph of order `n ≥ N` with
rooted simplicial defect `0` (equivalently, chordal) whose certified fractional
`K₂/K₃/K₄` partition value `e(G) - w` is at least `n²/6 - η n²` contains a real
clique `A` with `| |A| - n/3 | ≤ ε n` and `D_A + e(G - A) ≤ ε n²`.

## The chain

1. **Fractional to integral** (`size_ge_edge_sub_certified`).  For a clique
   partition `Q` of order at most four, the pieces of order `3` and `4` form a
   physical mixed packing whose gain is `∑ gainOf K` (order-two pieces have gain
   `0`), so `Q.size = e(G) - ∑ gainOf K ≥ e(G) - w`.  Hence the near hypothesis
   gives the hypothesis of
   `PaperIV.IntegralStability.chordal_linear_stability_sixteen` with
   `δ = η n² + n/6`, because `targetSize n ≤ n(n+1)/6`.
2. **Mass.**  That theorem yields a clique `R` with
   `(M(n) - splitBaseline n |R|) + m/16 + A/2 ≤ δ` and
   `splitBaseline n |R| ≤ M(n)`, hence `m + A ≤ 16 δ`.
3. **Size window** (`sq_dev_le_of_targetSize_sub_baseline`).  The exact identity
   `n(n+1)/6 - splitBaseline n k = (3/2)(k - (2n+1)/6)² - 1/24` and
   `targetSize n ≥ n(n+1)/6 - 5/6` give
   `(3/2)(k - (2n+1)/6)² ≤ (M(n) - splitBaseline n k) + 1`.
4. **Calibration.**  With `ε ≤ 1` (the general case follows by monotonicity in
   `ε`) take `η = min (γ/2) (min (ε/32) (ε²/16))`; the quadratic term is the
   binding one for small `ε`, and it is what controls the square root in step 3.

The existing instance `FixedL4LocalizationAt 0 (1/100)` is untouched.
-/

namespace PaperIV.FixedL4

open Finset
open PaperIV.FarRounding
open PaperIV.RootedSimplicialDefect
open PaperIV.RootVocab

/-! ## Step 1: integral gain is dominated by the certified fractional optimum -/

/-- **Fractional to integral.**  Every clique partition of order at most four has at
least `e(G) - w` pieces, where `w` is the certified mixed `K₃/K₄` optimum. -/
theorem size_ge_edge_sub_certified {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {w : ℚ}
    (hw : CertifiedFractionalOptimum G w) (Q : CliquePartition G) (hQ : Q.OrderAtMost 4) :
    (G.edgeFinset.card : ℚ) - w ≤ (Q.size : ℚ) := by
  classical
  let P : Packing G :=
    { pieces := Q.pieces.filter (fun K => 3 ≤ K.card)
      isItem := by
        intro K hK
        obtain ⟨hKQ, h3⟩ := Finset.mem_filter.1 hK
        refine ⟨Q.isClique K hKQ, ?_⟩
        have h4 := hQ K hKQ
        omega
      edgeDisjoint := by
        intro K hK L hL hKL
        exact Q.edgeDisjoint K (Finset.mem_filter.1 hK).1 L (Finset.mem_filter.1 hL).1 hKL }
  have hgain : P.gain = ∑ K ∈ Q.pieces, gainOf K := by
    show ∑ K ∈ Q.pieces.filter (fun K => 3 ≤ K.card), gainOf K = _
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun K hK => ?_
    split_ifs with h
    · rfl
    · have h2 := Q.two_le_card K hK
      have hK2 : K.card = 2 := by omega
      simp [gainOf, hK2]
  have hle := gain_le_of_certified hw P
  have hid := PaperIV.LossBudget.size_add_gain_eq Q
  rw [hgain] at hle
  have hidQ : (Q.size : ℚ) + ((∑ K ∈ Q.pieces, gainOf K : ℕ) : ℚ) =
      (G.edgeFinset.card : ℚ) := by exact_mod_cast hid
  linarith

/-! ## Step 3: the parabola -/

/-- The integral target is at least `n(n+1)/6 - 5/6`. -/
theorem continuous_le_targetSize_add (n : ℕ) :
    (n : ℚ) * ((n : ℚ) + 1) / 6 ≤ (PaperIV.targetSize n : ℚ) + 5 / 6 := by
  have h := Nat.div_add_mod (n * (n + 1)) 6
  have hm := Nat.mod_lt (n * (n + 1)) (show 0 < 6 by norm_num)
  have h' : n * (n + 1) ≤ 6 * PaperIV.targetSize n + 5 := by
    unfold PaperIV.targetSize; omega
  have hQ : ((n * (n + 1) : ℕ) : ℚ) ≤ ((6 * PaperIV.targetSize n + 5 : ℕ) : ℚ) := by
    exact_mod_cast h'
  push_cast at hQ
  linarith

/-- **The parabola inequality.**  The target minus the split baseline at core size
`k` controls the squared distance of `k` from the continuous maximiser
`(2n+1)/6`, with explicit constant `3/2` and additive loss `1`. -/
theorem sq_dev_le_of_targetSize_sub_baseline (n : ℕ) (k : ℚ) :
    (3 / 2 : ℚ) * (k - (2 * (n : ℚ) + 1) / 6) ^ 2 ≤
      ((PaperIV.targetSize n : ℚ) - PaperIV.splitBaseline (n : ℚ) k) + 1 := by
  have h := continuous_le_targetSize_add n
  unfold PaperIV.splitBaseline
  nlinarith

/-! ## Step 4: calibration and the theorem -/

/-- The scalar calibration: with `η = min (γ/2) (min (ε/32) (ε²/16))` and `n` large,
the deficit `δ = η n² + n/6` is admissible for the stability theorem, pays the mass
bound, and the parabola forces the size window. -/
theorem calibration_arith {eps γ n eta : ℚ} (heps : 0 < eps) (heps1 : eps ≤ 1) (hγ : 0 < γ)
    (hγ1 : γ ≤ 1) (hn : 100 ≤ γ * eps ^ 2 * n) (heta0 : 0 < eta) (heta1 : eta ≤ γ / 2)
    (heta2 : eta ≤ eps / 32) (heta3 : eta ≤ eps ^ 2 / 16) :
    eta * n ^ 2 + n / 6 ≤ γ * n ^ 2 ∧ 16 * (eta * n ^ 2 + n / 6) ≤ eps * n ^ 2 ∧
      ∀ x : ℚ, (3 / 2) * x ^ 2 ≤ eta * n ^ 2 + n / 6 + 1 → |x + 1 / 6| ≤ eps * n := by
  have he2 : eps ^ 2 ≤ eps := by nlinarith
  have he21 : eps ^ 2 ≤ 1 := by nlinarith
  have he2pos : 0 < eps ^ 2 := by positivity
  have hγe : γ * eps ^ 2 ≤ γ := by nlinarith
  have hγe' : γ * eps ^ 2 ≤ eps ^ 2 := by nlinarith
  have hn0 : 0 < n := by
    by_contra h; push_neg at h
    nlinarith [mul_pos hγ he2pos]
  have hA : 100 ≤ γ * n := by nlinarith
  have hB : 100 ≤ eps ^ 2 * n := by nlinarith
  have hC : 100 ≤ eps * n := by nlinarith
  have hn1 : 100 ≤ n := by nlinarith
  refine ⟨?_, ?_, ?_⟩
  · have : n / 6 ≤ γ / 2 * n ^ 2 := by nlinarith
    nlinarith
  · have h1 : 16 * (eta * n ^ 2) ≤ eps / 2 * n ^ 2 := by nlinarith
    have h2 : 16 * (n / 6) ≤ eps / 2 * n ^ 2 := by nlinarith
    linarith
  · intro x hx
    have h1 : eta * n ^ 2 ≤ eps ^ 2 / 16 * n ^ 2 := by nlinarith
    have h2 : n / 6 + 1 ≤ eps ^ 2 / 16 * n ^ 2 := by nlinarith
    have hx2 : x ^ 2 ≤ (eps * n / 2) ^ 2 := by nlinarith
    have hpos : 0 ≤ eps * n / 2 := by positivity
    have hxabs : |x| ≤ eps * n / 2 := abs_le_of_sq_le_sq' hx2 hpos |> fun h => abs_le.2 h
    calc |x + 1 / 6| ≤ |x| + |(1 / 6 : ℚ)| := abs_add_le _ _
      _ ≤ eps * n := by rw [abs_of_pos (by norm_num : (0 : ℚ) < 1 / 6)]; linarith

/-- Localization at defect `0` for every precision `0 < ε ≤ 1`. -/
theorem fixedL4LocalizationAt_zero_of_le_one {eps : ℚ} (heps : 0 < eps) (heps1 : eps ≤ 1) :
    FixedL4LocalizationAt 0 eps := by
  classical
  obtain ⟨Ns, hNs⟩ := PaperIV.IntegralStability.chordal_linear_stability_sixteen
  have hγ := PaperIV.IntegralStability.gamma_pos
  have hγ1 : PaperIV.IntegralStability.gamma ≤ 1 := by
    norm_num [PaperIV.IntegralStability.gamma, PaperIV.NearH1Calibration.eta]
  obtain ⟨γ, hγdef⟩ : ∃ γ, γ = PaperIV.IntegralStability.gamma := ⟨_, rfl⟩
  rw [← hγdef] at hγ hγ1
  obtain ⟨eta, hetadef⟩ : ∃ eta : ℚ, eta = min (γ / 2) (min (eps / 32) (eps ^ 2 / 16)) :=
    ⟨_, rfl⟩
  have heta_pos : 0 < eta := by rw [hetadef]; positivity
  have heta1 : eta ≤ γ / 2 := hetadef ▸ min_le_left _ _
  have heta2 : eta ≤ eps / 32 := hetadef ▸ le_trans (min_le_right _ _) (min_le_left _ _)
  have heta3 : eta ≤ eps ^ 2 / 16 := hetadef ▸ le_trans (min_le_right _ _) (min_le_right _ _)
  have hc_pos : 0 < γ * eps ^ 2 := by positivity
  refine ⟨eta, heta_pos, max Ns ⌈(100 : ℚ) / (γ * eps ^ 2)⌉₊, ?_⟩
  intro n hn G _ hdef w hw hnear
  have hnNs : Ns ≤ n := le_trans (Nat.le_max_left _ _) hn
  have hnM : ⌈(100 : ℚ) / (γ * eps ^ 2)⌉₊ ≤ n := le_trans (Nat.le_max_right _ _) hn
  have hnQ : (100 : ℚ) / (γ * eps ^ 2) ≤ n := le_trans (Nat.le_ceil _) (by exact_mod_cast hnM)
  have hcn : 100 ≤ γ * eps ^ 2 * n := by
    rw [div_le_iff₀ hc_pos] at hnQ; linarith
  obtain ⟨hδγ, hδmass, hδsize⟩ :=
    calibration_arith heps heps1 hγ hγ1 hcn heta_pos heta1 heta2 heta3
  have hchordal : PaperIV.FarRounding.IsChordal G :=
    PaperIV.RootedDefectZero.isChordal_of_rootedDefect_zero hdef
  have hn0 : (0 : ℚ) ≤ n := by positivity
  have hδ0 : 0 ≤ eta * (n : ℚ) ^ 2 + (n : ℚ) / 6 := by positivity
  have hmin : ∀ Q : CliquePartition G, Q.OrderAtMost 4 →
      (PaperIV.targetSize n : ℚ) - (eta * (n : ℚ) ^ 2 + (n : ℚ) / 6) ≤ (Q.size : ℚ) := by
    intro Q hQ
    have h1 := size_ge_edge_sub_certified hw Q hQ
    have h2 := PaperIV.targetSize_cast_le_continuous n
    linarith
  obtain ⟨R, hRclique, -, -, hbase, -, hreserve, -⟩ :=
    hNs n hnNs G hchordal _ hδ0 (hγdef ▸ hδγ) hmin
  have hm0 : (0 : ℚ) ≤ ((outsideEdges G R).card : ℚ) := by positivity
  have hA0 : (0 : ℚ) ≤ (missingIncidences G R : ℚ) := by positivity
  refine ⟨⟨R, hRclique, ?_, ?_⟩⟩
  · have hpar := sq_dev_le_of_targetSize_sub_baseline n (R.card : ℚ)
    have hdev : (R.card : ℚ) - (n : ℚ) / 3 =
        ((R.card : ℚ) - (2 * (n : ℚ) + 1) / 6) + 1 / 6 := by ring
    rw [hdev]
    exact hδsize _ (by linarith)
  · linarith

/-- **Fixed-`L = 4` localization at defect `0`, for every precision.** -/
theorem fixedL4Localization_defectZero : FixedL4Localization 0 := by
  intro eps heps
  by_cases h1 : eps ≤ 1
  · exact fixedL4LocalizationAt_zero_of_le_one heps h1
  · exact fixedL4LocalizationAt_mono_eps (le_of_lt (not_le.1 h1))
      (fixedL4LocalizationAt_zero_of_le_one one_pos le_rfl)

end PaperIV.FixedL4

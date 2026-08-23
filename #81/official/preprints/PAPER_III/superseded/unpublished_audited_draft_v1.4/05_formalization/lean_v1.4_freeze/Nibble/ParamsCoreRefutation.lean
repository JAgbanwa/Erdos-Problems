/-
# Nibble — refutation of the hypergraph-level outer parameter obligations

Standalone, Mathlib-only.  `Nibble.FreedmanParamsObstruction` refutes the *type-free* parameter core
of the Freedman route.  This file upgrades that to the actual `∀`-quantified obligations sitting at
the top of both outer assembly routes, by feeding them the complete `r`-uniform hypergraph instance
of `Nibble.CompleteHypergraph`:

* `not_nibbleParamsExistThreshold` — the legacy Chebyshev obligation
  `Nibble.NibbleParamsExistThreshold` (the hypothesis of `nibbleTheoremMost_holds_of_params`) is
  FALSE.
* `not_freedmanSizedThresholdParameterCore`, `not_freedmanSizedParameterCore` — the Freedman
  hypergraph-level parameter cores (the hypotheses of
  `nibbleTheoremMostCeilSized_of_freedman_threshold_core` and
  `nibbleTheoremMostCeilSized_of_freedman_core`) are FALSE for every `β < 1/2`.

In each case the reason is the telescoping obstruction `crux_telescope_false`: the crux inequality
asks each of the `T` rounds to cover a `(1-lam)`-fraction of the *whole* vertex set, while the total
gain available across all rounds is at most `(1-μ)d/(rΔ) ≤ 1/2`.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.MostAssembly
import Nibble.MostAssemblyFreedman
import Nibble.CompleteHypergraph
import Nibble.FreedmanParamsObstruction
import Mathlib.Tactic.NormNum.BigOperators

open Finset Hypergraph

namespace Nibble

/-- An exactly `d`-regular hypergraph is majority near-regular with empty exceptional set. -/
theorem nearlyRegularMost_of_exact {V : Type*} [Fintype V] [DecidableEq V]
    {H : Finset (Finset V)} {d μ η : ℝ} (hd : 0 ≤ d) (hμ : 0 ≤ μ) (hη : 0 ≤ η)
    (hdeg : ∀ v : V, (degree H v : ℝ) = d) : NearlyRegularMost H d μ η := by
  refine ⟨∅, by simpa using mul_nonneg hη (Nat.cast_nonneg _), fun v _ => ?_⟩
  rw [hdeg v]
  exact ⟨by nlinarith, by nlinarith⟩

/-- The telescoping obstruction without the `μ ≤ 1` and `0 < p` restrictions: if the tolerance
exceeds `1`, or the retention probability vanishes, the per-round gain is nonpositive, forcing
`lam = 1` and again contradicting `lam ^ T ≤ β < 1/2`. -/
theorem crux_false_of_lam_le_one {r Δ T : ℕ} {d mu eta lam p c P Nv β : ℝ}
    (hrR : (2 : ℝ) ≤ (r : ℝ)) (hd : 0 < d) (hmu0 : 0 ≤ mu)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hΔpos : (0 : ℝ) < (Δ : ℝ))
    (hc0 : 0 ≤ c) (hq : 0 ≤ 1 - (r : ℝ) * Δ * p) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (heta : 0 ≤ eta) (hP : 0 ≤ P) (hNv : 0 < Nv)
    (hβ : β < 1 / 2) (hTβ : lam ^ T ≤ β)
    (hΔd : 2 * d ≤ (r : ℝ) * (Δ : ℝ))
    (hcrux : ∀ k, k < T →
      0 ≤ ((1 - mu) * d * (1 - (r : ℝ) * Δ * p) ^ k
            - c * ∑ i ∈ Finset.range k, (1 - (r : ℝ) * Δ * p) ^ i)
          * (p * (1 - p) ^ (r * Δ))
      ∧ (1 - lam) * Nv
          ≤ (1 - eta) * Nv * (((1 - mu) * d * (1 - (r : ℝ) * Δ * p) ^ k
                - c * ∑ i ∈ Finset.range k, (1 - (r : ℝ) * Δ * p) ^ i)
              * (p * (1 - p) ^ (r * Δ)))
            - (r : ℝ) * P) :
    False := by
  -- a nonpositive round-`0` gain already forces `lam = 1`
  have key : ((1 - mu) * d * (1 - (r : ℝ) * Δ * p) ^ 0
        - c * ∑ i ∈ Finset.range 0, (1 - (r : ℝ) * Δ * p) ^ i)
        * (p * (1 - p) ^ (r * Δ)) ≤ 0 → False := by
    intro hG0le
    rcases Nat.eq_zero_or_pos T with hT | hT
    · subst hT
      simp only [pow_zero] at hTβ
      linarith
    · obtain ⟨hgain0, hineq⟩ := hcrux 0 hT
      have hdef := round_deficit_le_gain hNv heta hP (by positivity) hgain0 hineq
      have hlam : lam = 1 := le_antisymm hlam1 (by linarith)
      rw [hlam, one_pow] at hTβ
      linarith
  have hf0 : (0 : ℝ) ≤ p * (1 - p) ^ (r * Δ) :=
    mul_nonneg hp0 (pow_nonneg (by linarith) _)
  rcases eq_or_lt_of_le hp0 with hp | hppos
  · refine key ?_
    rw [← hp]
    simp
  rcases le_or_gt mu 1 with hmu | hmu
  · refine crux_telescope_false hrR hmu hd hp0 hp1 hppos hΔpos hc0 hq hlam0 heta hP hNv hβ hTβ
      ?_ hcrux
    nlinarith
  · refine key ?_
    simp only [pow_zero, Finset.range_zero, Finset.sum_empty, mul_zero, sub_zero, mul_one]
    exact mul_nonpos_of_nonpos_of_nonneg (by nlinarith) hf0

/-- **The legacy Chebyshev parameter obligation is FALSE.**  `NibbleParamsExistThreshold` is the
hypothesis of `nibbleTheoremMost_holds_of_params`; the complete `2`-uniform hypergraph on a large
`Fin n` together with the telescoping obstruction refutes it at `β = 1/4`. -/
theorem not_nibbleParamsExistThreshold : ¬ NibbleParamsExistThreshold := by
  classical
  intro hP
  obtain ⟨μ, hμ, η, hη, d₀, hd₀, hcore⟩ := hP 2 (le_refl 2) (1 / 4) (by norm_num)
  obtain ⟨n, d, hn, hd, hd₀d, _hsize, huni, hdeg, hcodeg⟩ :=
    exists_complete_instance (r := 2) (le_refl 2) hμ hd₀ (K := 1) one_pos
  have hreg : NearlyRegularMost (completeHG n 2) d μ η :=
    nearlyRegularMost_of_exact (le_of_lt hd) (le_of_lt hμ) (le_of_lt hη) hdeg
  obtain ⟨Δ, p, c, lam, T, hp0, hp1, hcpos, _hcΔ, hq, hlam1, hlam0, hdeg0, hTβ, hcrux⟩ :=
    hcore (completeHG n 2) d hd hd₀d huni hreg hcodeg
  have hΔd : d ≤ (Δ : ℝ) := by
    obtain ⟨v⟩ : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    have h1 : (degree (completeHG n 2) v : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast hdeg0 v
    rw [hdeg v] at h1
    exact h1
  have hΔpos : (0 : ℝ) < (Δ : ℝ) := lt_of_lt_of_le hd hΔd
  have hNv : (0 : ℝ) < (Fintype.card (Fin n) : ℝ) := by
    rw [Fintype.card_fin]
    exact_mod_cast hn
  refine crux_false_of_lam_le_one (r := 2) (Δ := Δ) (T := T) (d := d) (mu := μ) (eta := η)
    (lam := lam) (p := p) (c := c)
    (P := (Fintype.card (Fin n) : ℝ) * ((Fintype.card (Fin n) : ℝ) * (Δ : ℝ) ^ 2 / c ^ 2))
    (Nv := (Fintype.card (Fin n) : ℝ)) (β := 1 / 4)
    (by norm_num) hd (le_of_lt hμ) hp0 hp1 hΔpos (le_of_lt hcpos) hq hlam0 hlam1 (le_of_lt hη)
    (by positivity) hNv (by norm_num) hTβ ?_ hcrux
  push_cast
  linarith

/-- **The Freedman hypergraph-level threshold parameter core is FALSE for `β < 1/2`.**  This is the
hypothesis consumed by `nibbleTheoremMostCeilSized_of_freedman_threshold_core`. -/
theorem not_freedmanSizedThresholdParameterCore
    {r : ℕ} (hr : 2 ≤ r) {β η d₀ K : ℝ} (hβ : β < 1 / 2) (hη : 0 ≤ η)
    (hd₀ : 0 < d₀) (hK : 0 < K) :
    ¬ FreedmanSizedThresholdParameterCore r β ((1 : ℝ) / 100) η d₀ K := by
  classical
  intro hcore
  obtain ⟨n, d, hn, hd, hd₀d, hsize, huni, hdeg, hcodeg⟩ :=
    exists_complete_instance hr (μ := (1 : ℝ) / 100) (by norm_num) hd₀ hK
  have hreg : NearlyRegularMost (completeHG n r) d ((1 : ℝ) / 100) η :=
    nearlyRegularMost_of_exact (le_of_lt hd) (by norm_num) hη hdeg
  have hceil : ∀ x : Fin n, (degree (completeHG n r) x : ℝ) ≤ (1 + (1 : ℝ) / 100) * d := by
    intro x
    rw [hdeg x]
    nlinarith
  have hsize' : (Fintype.card (Fin n) : ℝ) ≤ K * d ^ 2 := by
    rw [Fintype.card_fin]; exact hsize
  obtain ⟨Δ, p, c, lam, T, hp0, hp1, hppos, hΔ0, hcpos, hq, hlam1, hlam0, hdeg0, hTβ,
      _hsmall, hcrux⟩ :=
    hcore (completeHG n r) d hd hd₀d huni hreg hcodeg hceil hsize'
  have hΔd : d ≤ (Δ : ℝ) := by
    obtain ⟨v⟩ : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    have h1 : (degree (completeHG n r) v : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast hdeg0 v
    rw [hdeg v] at h1
    exact h1
  have hΔpos : (0 : ℝ) < (Δ : ℝ) := lt_of_lt_of_le hd hΔd
  have hNv : (0 : ℝ) < (Fintype.card (Fin n) : ℝ) := by
    rw [Fintype.card_fin]; exact_mod_cast hn
  have hrR : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  refine crux_false_of_lam_le_one (r := r) (Δ := Δ) (T := T) (d := d) (mu := (1 : ℝ) / 100)
    (eta := η) (lam := lam) (p := p) (c := c)
    (P := freedmanPenalty (Fin n) r Δ p c) (Nv := (Fintype.card (Fin n) : ℝ)) (β := β)
    hrR hd (by norm_num) hp0 hp1 hΔpos (le_of_lt hcpos) hq hlam0 hlam1 hη ?_ hNv hβ hTβ ?_ hcrux
  · unfold freedmanPenalty
    positivity
  · nlinarith

/-- **The Freedman hypergraph-level parameter core is FALSE for `β < 1/2`.**  This is the hypothesis
consumed by `nibbleTheoremMostCeilSized_of_freedman_core`. -/
theorem not_freedmanSizedParameterCore
    {r : ℕ} (hr : 2 ≤ r) {β η K : ℝ} (hβ : β < 1 / 2) (hη : 0 ≤ η) (hK : 0 < K) :
    ¬ FreedmanSizedParameterCore r β ((1 : ℝ) / 100) η K := by
  intro hcore
  refine not_freedmanSizedThresholdParameterCore hr (β := β) (η := η) (d₀ := 1) (K := K)
    hβ hη one_pos hK ?_
  intro V _ _ H d hd _hd0 huni hreg hcodeg hceil hsize
  exact hcore H d hd huni hreg hcodeg hceil hsize

end Nibble

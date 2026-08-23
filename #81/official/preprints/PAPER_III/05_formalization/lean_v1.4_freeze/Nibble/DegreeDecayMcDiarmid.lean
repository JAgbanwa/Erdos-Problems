/-
# Nibble — degree-decay and oracle reduction for the McDiarmid strategy

McDiarmid analogue of `DegreeDecay.lean`. The deterministic induction is unchanged; only the one-round
coverage penalty changes from `|V| * (|V| * Δ^2 / c^2)` to the exponential all-vertices McDiarmid
penalty.
-/
import Nibble.NibbleStrategyMcDiarmid
import Nibble.DegreeDecay

open Hypergraph Finset

namespace Nibble

variable {V : Type u} [Fintype V] [DecidableEq V]

noncomputable def McDiarmidPenalty (V : Type u) [Fintype V] (r Δ : ℕ) (p c : ℝ) : ℝ :=
  (Fintype.card V : ℝ) * ((Fintype.card V : ℝ)
    * (2 * Real.exp (-c ^ 2 / (2 * ((Δ : ℝ) ^ 2 * ((r : ℝ) * Δ * p) + (Δ : ℝ) / 3 * c)))))

/-- McDiarmid degree-decay invariant. -/
theorem degree_decay_invariant_McDiarmid (r Δ : ℕ) (p c : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hr1 : 1 ≤ r) (hΔ0 : 0 < Δ) (hc : 0 < c)
    (hVpos : ∀ H' : Finset (Finset V), IsUniform H' r → (∀ x, degree H' x ≤ Δ) →
      ∀ v : V, 0 < degree H' v →
        0 < (∑ e ∈ H'.filter (fun f => v ∈ f),
          (((H'.filter (fun f => v ∈ f)).filter
            (fun e' => ¬ Disjoint (depNbhd H' e) (depNbhd H' e'))).card : ℝ)) * ((r : ℝ) * Δ * p))
    (hsmall : ∀ H' : Finset (Finset V), IsUniform H' r → (∀ x, degree H' x ≤ Δ) →
      (∑ v : V, ENNReal.ofReal
        (2 * Real.exp (-c ^ 2 / (2 * mcdiarmidNeighborCoeffSum H' v)))) < 1)
    (hq : 0 ≤ 1 - (r : ℝ) * Δ * p)
    (H : Finset (Finset V)) (huni : IsUniform H r) (hdeg0 : ∀ x, degree H x ≤ Δ)
    (v : V) :
    ∀ k : ℕ,
      (degree H v : ℝ) * (1 - (r : ℝ) * Δ * p) ^ k
        - c * (∑ i ∈ Finset.range k, (1 - (r : ℝ) * Δ * p) ^ i)
        ≤ (degree (nibbleResidual
            (nibbleStrategyMcDiarmid r Δ p c hp0 hp1 hr1 (le_of_lt hc) hsmall) H k) v : ℝ) := by
  set R := nibbleStrategyMcDiarmid r Δ p c hp0 hp1 hr1 (le_of_lt hc) hsmall with hRdef
  set q : ℝ := 1 - (r : ℝ) * Δ * p with hqdef
  intro k
  induction k with
  | zero =>
      simp only [pow_zero, mul_one, Finset.range_zero, Finset.sum_empty, mul_zero, sub_zero]
      show (degree H v : ℝ) ≤ (degree (nibbleResidual R H 0) v : ℝ)
      have : nibbleResidual R H 0 = H := rfl
      rw [this]
  | succ k ih =>
      have huni_k : IsUniform (nibbleResidual R H k) r := nibbleResidual_uniform huni R k
      have hdeg_k : ∀ x, degree (nibbleResidual R H k) x ≤ Δ := fun x =>
        degree_nibbleResidual_le H k hdeg0 x
      have hspec := (nibbleStrategyMcDiarmid_spec r Δ p c hp0 hp1 hr1 (le_of_lt hc) hsmall
        (nibbleResidual R H k) huni_k hdeg_k).1 v
      have hstep : nibbleResidual R H (k + 1)
          = residual (nibbleResidual R H k) (R (nibbleResidual R H k)) := rfl
      rw [hstep]
      have hbound : (degree (nibbleResidual R H k) v : ℝ) * q - c
          < (degree (residual (nibbleResidual R H k) (R (nibbleResidual R H k))) v : ℝ) := by
        rw [hqdef]; exact hspec
      have hsum : q * (∑ i ∈ Finset.range k, q ^ i) + 1 = ∑ i ∈ Finset.range (k + 1), q ^ i := by
        rw [Finset.sum_range_succ', Finset.mul_sum]
        simp only [pow_succ, pow_zero]
        ring_nf
      have hmul : (degree H v : ℝ) * q ^ k - c * (∑ i ∈ Finset.range k, q ^ i) ≤
          (degree (nibbleResidual R H k) v : ℝ) := ih
      have hq_mul : ((degree H v : ℝ) * q ^ k - c * (∑ i ∈ Finset.range k, q ^ i)) * q
          ≤ (degree (nibbleResidual R H k) v : ℝ) * q := by
        exact mul_le_mul_of_nonneg_right hmul hq
      calc (degree H v : ℝ) * q ^ (k + 1) - c * (∑ i ∈ Finset.range (k + 1), q ^ i)
          = ((degree H v : ℝ) * q ^ k - c * (∑ i ∈ Finset.range k, q ^ i)) * q - c := by
            rw [← hsum]; ring
        _ ≤ (degree (nibbleResidual R H k) v : ℝ) * q - c := by linarith only [hq_mul]
        _ ≤ (degree (residual (nibbleResidual R H k) (R (nibbleResidual R H k))) v : ℝ) := by
            linarith only [hbound]

/-- Residual degree lower bound for non-exceptional vertices, McDiarmid strategy. -/
theorem residual_degree_lower_most_McDiarmid (r Δ : ℕ) (p c d μ η : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hr1 : 1 ≤ r) (hΔ0 : 0 < Δ) (hc : 0 < c)
    (hVpos : ∀ H' : Finset (Finset V), IsUniform H' r → (∀ x, degree H' x ≤ Δ) →
      ∀ v : V, 0 < degree H' v →
        0 < (∑ e ∈ H'.filter (fun f => v ∈ f),
          (((H'.filter (fun f => v ∈ f)).filter
            (fun e' => ¬ Disjoint (depNbhd H' e) (depNbhd H' e'))).card : ℝ)) * ((r : ℝ) * Δ * p))
    (hsmall : ∀ H' : Finset (Finset V), IsUniform H' r → (∀ x, degree H' x ≤ Δ) →
      (∑ v : V, ENNReal.ofReal
        (2 * Real.exp (-c ^ 2 / (2 * mcdiarmidNeighborCoeffSum H' v)))) < 1)
    (hq : 0 ≤ 1 - (r : ℝ) * Δ * p)
    (H : Finset (Finset V)) (huni : IsUniform H r) (hdeg0 : ∀ x, degree H x ≤ Δ)
    (hreg : NearlyRegularMost H d μ η) :
    ∃ Exc : Finset V, (Exc.card : ℝ) ≤ η * (Fintype.card V : ℝ) ∧
      ∀ v, v ∉ Exc → ∀ k,
        (1 - μ) * d * (1 - (r : ℝ) * Δ * p) ^ k
          - c * (∑ i ∈ Finset.range k, (1 - (r : ℝ) * Δ * p) ^ i)
          ≤ (degree (nibbleResidual
              (nibbleStrategyMcDiarmid r Δ p c hp0 hp1 hr1 (le_of_lt hc) hsmall) H k) v : ℝ) := by
  obtain ⟨Exc, hExc, hdeg⟩ := hreg
  refine ⟨Exc, hExc, ?_⟩
  intro v hv k
  have hlow : (1 - μ) * d ≤ (degree H v : ℝ) := (hdeg v hv).1
  have hinv := degree_decay_invariant_McDiarmid r Δ p c hp0 hp1 hr1 hΔ0 hc hVpos hsmall hq
    H huni hdeg0 v k
  have hpow : 0 ≤ (1 - (r : ℝ) * Δ * p) ^ k := pow_nonneg hq _
  have hstep : (1 - μ) * d * (1 - (r : ℝ) * Δ * p) ^ k
      ≤ (degree H v : ℝ) * (1 - (r : ℝ) * Δ * p) ^ k :=
    mul_le_mul_of_nonneg_right hlow hpow
  linarith only [hstep, hinv]

/-- Residual edge lower bound for the McDiarmid strategy. -/
theorem residual_edge_lower_most_McDiarmid (r Δ : ℕ) (p c d μ η : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hr1 : 1 ≤ r) (hΔ0 : 0 < Δ) (hc : 0 < c)
    (hVpos : ∀ H' : Finset (Finset V), IsUniform H' r → (∀ x, degree H' x ≤ Δ) →
      ∀ v : V, 0 < degree H' v →
        0 < (∑ e ∈ H'.filter (fun f => v ∈ f),
          (((H'.filter (fun f => v ∈ f)).filter
            (fun e' => ¬ Disjoint (depNbhd H' e) (depNbhd H' e'))).card : ℝ)) * ((r : ℝ) * Δ * p))
    (hsmall : ∀ H' : Finset (Finset V), IsUniform H' r → (∀ x, degree H' x ≤ Δ) →
      (∑ v : V, ENNReal.ofReal
        (2 * Real.exp (-c ^ 2 / (2 * mcdiarmidNeighborCoeffSum H' v)))) < 1)
    (hq : 0 ≤ 1 - (r : ℝ) * Δ * p)
    (H : Finset (Finset V)) (huni : IsUniform H r) (hdeg0 : ∀ x, degree H x ≤ Δ)
    (hreg : NearlyRegularMost H d μ η) (k : ℕ) :
    ∃ Exc : Finset V, (Exc.card : ℝ) ≤ η * (Fintype.card V : ℝ) ∧
      ((Fintype.card V : ℝ) - (Exc.card : ℝ))
        * ((1 - μ) * d * (1 - (r : ℝ) * Δ * p) ^ k
            - c * (∑ i ∈ Finset.range k, (1 - (r : ℝ) * Δ * p) ^ i))
        ≤ (r : ℝ) * ((nibbleResidual
            (nibbleStrategyMcDiarmid r Δ p c hp0 hp1 hr1 (le_of_lt hc) hsmall) H k).card : ℝ) := by
  obtain ⟨Exc, hExc, hfloor⟩ := residual_degree_lower_most_McDiarmid r Δ p c d μ η hp0 hp1 hr1
    hΔ0 hc hVpos hsmall hq H huni hdeg0 hreg
  refine ⟨Exc, hExc, ?_⟩
  set R := nibbleStrategyMcDiarmid r Δ p c hp0 hp1 hr1 (le_of_lt hc) hsmall with hRdef
  set Hk := nibbleResidual R H k with hHk
  have huni_k : IsUniform Hk r := nibbleResidual_uniform huni R k
  have hsum := sum_degree (V := V) (H := Hk) (r := r) huni_k
  have hsumR : (∑ v : V, (degree Hk v : ℝ)) = (r : ℝ) * (Hk.card : ℝ) := by
    have hnat := congrArg (Nat.cast : ℕ → ℝ) hsum
    simpa using hnat
  have h1 : ∑ v ∈ Finset.univ \ Exc, (degree Hk v : ℝ) ≤ ∑ v : V, (degree Hk v : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun i _ _ => by positivity)
  have h2 : ∑ v ∈ Finset.univ \ Exc,
        ((1 - μ) * d * (1 - (r : ℝ) * Δ * p) ^ k
          - c * (∑ i ∈ Finset.range k, (1 - (r : ℝ) * Δ * p) ^ i))
      ≤ ∑ v ∈ Finset.univ \ Exc, (degree Hk v : ℝ) := by
    refine Finset.sum_le_sum ?_
    intro v hv
    have hvnot : v ∉ Exc := (Finset.mem_sdiff.mp hv).2
    simpa [Hk, R] using hfloor v hvnot k
  have h3 : ∑ _v ∈ Finset.univ \ Exc,
        ((1 - μ) * d * (1 - (r : ℝ) * Δ * p) ^ k
          - c * (∑ i ∈ Finset.range k, (1 - (r : ℝ) * Δ * p) ^ i))
      = ((Fintype.card V : ℝ) - (Exc.card : ℝ))
          * ((1 - μ) * d * (1 - (r : ℝ) * Δ * p) ^ k
            - c * (∑ i ∈ Finset.range k, (1 - (r : ℝ) * Δ * p) ^ i)) := by
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ_diff,
        Nat.cast_sub (Finset.card_le_univ _)]
  rw [h3] at h2
  linarith only [hsumR, h1, h2]

end Nibble





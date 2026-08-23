/-
# Nibble — M8 (sharp) : exponential-tail concentration with the sum restricted to `H`

Standalone, Mathlib-only. The **sharp** companion of `McDiarmidResidual` (N3). The naive M8
instantiation sums the bounded-difference coefficients `c_e²` over the whole index type
`Finset V` of the per-edge configuration `ω : Finset V → Bool` — that is `2^|V|` terms, which
destroys the exponential bound. But toggling a bit `e ∉ H` is **inert**: `H.filter (ω · = true)`
only inspects membership of edges already in `H`, so the residual set (hence the residual degree)
does not change, and the true coefficient at `e ∉ H` is `0`.

`residualDegConfig_eq_of_notMem` records that inertia; `residualDeg_config_concentration_sharp`
uses the sharpened coefficient `fun e => if e ∈ H then C_e else 0`, so the denominator sum collapses
to `∑_{e ∈ H} C_e²` (only `|H|` terms). This is the form with which the nibble parameter tuning
closes (`c ≈ √(d log n) ≪ d`) — the replacement for the too-weak Chebyshev bound.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.McDiarmidFull
import Nibble.SumEstimate
import Nibble.Prelude

open MeasureTheory ProbabilityTheory Finset Hypergraph

namespace Nibble

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Inertia of an off-`H` toggle.** If `e ∉ H` and `ω, ω'` agree off `e`, then the two retained
sets `H.filter (ω · = true)` and `H.filter (ω' · = true)` coincide (membership in `H` never queries
the `e`-bit for an edge `≠ e`, and `e ∉ H` is filtered out either way), so the residual degree at `v`
is unchanged. Hence the true bounded-difference coefficient at an off-`H` coordinate is `0`. -/
theorem residualDegConfig_eq_of_notMem (H : Finset (Finset V)) (v : V) (e : Finset V)
    (ω ω' : Finset V → Bool) (heH : e ∉ H) (hagree : ∀ g, g ≠ e → ω g = ω' g) :
    (degree (residual H (H.filter (fun g => ω g = true))) v : ℝ)
      = (degree (residual H (H.filter (fun g => ω' g = true))) v : ℝ) := by
  have hRR : H.filter (fun g => ω g = true) = H.filter (fun g => ω' g = true) := by
    ext g
    rcases eq_or_ne g e with rfl | hge
    · simp only [Finset.mem_filter]
      exact ⟨fun h => absurd h.1 heH, fun h => absurd h.1 heH⟩
    · simp only [Finset.mem_filter, hagree g hge]
  rw [hRR]

/-- **M8 (sharp) — residual-degree concentration with the sum restricted to `H`.** For the per-edge
Bernoulli configuration `ω : Finset V → Bool`, the residual degree at `v` deviates from its mean by
`≥ ε` with probability `≤ 2·exp(−ε²/(2 ∑_{e ∈ H} C_e²))`, where `C_e = ∑_{x ∈ e ∪ support(conflicts)}
deg(x)` is the local coefficient. The denominator sums over `H` only — the exponential tail that
replaces the Chebyshev bound and makes the nibble parameter window `c ≈ √(d log n) ≪ d` feasible. -/
theorem residualDeg_config_concentration_sharp (H : Finset (Finset V)) (v : V)
    (ν : Measure Bool) [IsProbabilityMeasure ν] {ε : ℝ} (hε : 0 ≤ ε) :
    (Measure.pi (fun _ : Finset V => ν)).real
        {ω | ε ≤ |(degree (residual H (H.filter (fun g => ω g = true))) v : ℝ)
              - ∫ x, (degree (residual H (H.filter (fun g => x g = true))) v : ℝ)
                  ∂(Measure.pi (fun _ : Finset V => ν))|}
      ≤ 2 * Real.exp (-ε ^ 2 / (2 * ∑ e ∈ H,
          (∑ x ∈ e ∪ support (H.filter (fun g => ¬ Disjoint e g)), degree H x : ℝ) ^ 2)) := by
  classical
  set Cf : Finset V → ℝ := fun e =>
    (∑ x ∈ e ∪ support (H.filter (fun g => ¬ Disjoint e g)), degree H x : ℝ) with hCf
  set c : Finset V → ℝ := fun e => if e ∈ H then Cf e else 0 with hc
  have hfmeas : Measurable
      (fun ω : Finset V → Bool => (degree (residual H (H.filter (fun g => ω g = true))) v : ℝ)) :=
    measurable_of_finite _
  have hbd : ∀ (j : Finset V) (ω ω' : Finset V → Bool), (∀ i, i ≠ j → ω i = ω' i) →
      |(degree (residual H (H.filter (fun g => ω g = true))) v : ℝ)
        - (degree (residual H (H.filter (fun g => ω' g = true))) v : ℝ)| ≤ c j := by
    intro j ω ω' h
    by_cases hjH : j ∈ H
    · rw [hc]; simp only [if_pos hjH]
      exact residualDegConfig_boundedDiff H v j ω ω' (fun g hg => h g hg)
    · rw [hc]; simp only [if_neg hjH]
      rw [residualDegConfig_eq_of_notMem H v j ω ω' hjH (fun g hg => h g hg)]
      simp
  have hkey := mcdiarmid_two_sided_const ν
    (fun ω => (degree (residual H (H.filter (fun g => ω g = true))) v : ℝ))
    hfmeas.stronglyMeasurable Integrable.of_finite hbd hε
  -- rewrite the coefficient sum `∑ j, (c j)^2` to `∑ e ∈ H, (Cf e)^2`
  have hsum : (∑ j : Finset V, (c j) ^ 2) = ∑ e ∈ H, (Cf e) ^ 2 := by
    have : ∀ j : Finset V, (c j) ^ 2 = if j ∈ H then (Cf j) ^ 2 else 0 := by
      intro j; rw [hc]; by_cases hjH : j ∈ H <;> simp [hjH]
    simp_rw [this]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  rw [hsum] at hkey
  exact hkey

/-- **M8 (count-sharp) — residual-degree concentration with the true count coefficient.** This is the
same restricted-to-`H` McDiarmid bound as `residualDeg_config_concentration_sharp`, but with the
sharper coefficient `neighborCoef H v e`, i.e. the number of `v`-edges affected by toggling `e`. This
is the denominator meant for the later codegree/sum-estimate stage. -/
theorem residualDeg_config_concentration_neighborCoef (H : Finset (Finset V)) (v : V)
    (ν : Measure Bool) [IsProbabilityMeasure ν] {ε : ℝ} (hε : 0 ≤ ε) :
    (Measure.pi (fun _ : Finset V => ν)).real
        {ω | ε ≤ |(degree (residual H (H.filter (fun g => ω g = true))) v : ℝ)
              - ∫ x, (degree (residual H (H.filter (fun g => x g = true))) v : ℝ)
                  ∂(Measure.pi (fun _ : Finset V => ν))|}
      ≤ 2 * Real.exp (-ε ^ 2 / (2 * ∑ e ∈ H, (neighborCoef H v e : ℝ) ^ 2)) := by
  classical
  set c : Finset V → ℝ := fun e => if e ∈ H then (neighborCoef H v e : ℝ) else 0 with hc
  have hfmeas : Measurable
      (fun ω : Finset V → Bool => (degree (residual H (H.filter (fun g => ω g = true))) v : ℝ)) :=
    measurable_of_finite _
  have hbd : ∀ (j : Finset V) (ω ω' : Finset V → Bool), (∀ i, i ≠ j → ω i = ω' i) →
      |(degree (residual H (H.filter (fun g => ω g = true))) v : ℝ)
        - (degree (residual H (H.filter (fun g => ω' g = true))) v : ℝ)| ≤ c j := by
    intro j ω ω' h
    by_cases hjH : j ∈ H
    · rw [hc]; simp only [if_pos hjH]
      exact residualDegConfig_boundedDiff_neighborCoef H v j ω ω' (fun g hg => h g hg)
    · rw [hc]; simp only [if_neg hjH]
      rw [residualDegConfig_eq_of_notMem H v j ω ω' hjH (fun g hg => h g hg)]
      simp
  have hkey := mcdiarmid_two_sided_const ν
    (fun ω => (degree (residual H (H.filter (fun g => ω g = true))) v : ℝ))
    hfmeas.stronglyMeasurable Integrable.of_finite hbd hε
  have hsum : (∑ j : Finset V, (c j) ^ 2) = ∑ e ∈ H, (neighborCoef H v e : ℝ) ^ 2 := by
    have : ∀ j : Finset V, (c j) ^ 2 =
        if j ∈ H then (neighborCoef H v j : ℝ) ^ 2 else 0 := by
      intro j; rw [hc]; by_cases hjH : j ∈ H <;> simp [hjH]
    simp_rw [this]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  rw [hsum] at hkey
  exact hkey

end Nibble

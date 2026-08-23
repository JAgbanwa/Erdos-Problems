/-
# Nibble — M8 : exponential-tail concentration of the residual degree

Standalone, Mathlib-only. The final M8 instantiation: applying `mcdiarmid_two_sided_const` (McDiarmid
over the finite index of edges) to the residual-degree function of the per-edge Bernoulli
configuration, with the bounded-difference coefficient `residualDegConfig_boundedDiff` (N1). This
yields the EXPONENTIAL-tail concentration of `deg_residual(v)` — the bound that replaces the too-weak
Chebyshev `round_regularity_failure`, and with which the parameter tuning of the nibble closes
(`c ≈ √(d log n) ≪ d`).

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.McDiarmidFull
import Nibble.ResidualBoundedDiff
import Nibble.Prelude

open MeasureTheory ProbabilityTheory Finset Hypergraph

namespace Nibble

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **M8 — residual-degree concentration (exponential tail).** For the per-edge Bernoulli
configuration `ω : Finset V → Bool` (`retained = H.filter (ω · = true)`), the residual degree at `v`
deviates from its mean by `≥ ε` with probability `≤ 2·exp(−ε²/(2 ∑_e c_e²))`, where `c_e` is the local
bounded-difference coefficient. Exponential tail — the McDiarmid replacement for the Chebyshev bound. -/
theorem residualDeg_config_concentration (H : Finset (Finset V)) (v : V)
    (ν : Measure Bool) [IsProbabilityMeasure ν] {ε : ℝ} (hε : 0 ≤ ε) :
    (Measure.pi (fun _ : Finset V => ν)).real
        {ω | ε ≤ |(degree (residual H (H.filter (fun g => ω g = true))) v : ℝ)
              - ∫ x, (degree (residual H (H.filter (fun g => x g = true))) v : ℝ)
                  ∂(Measure.pi (fun _ : Finset V => ν))|}
      ≤ 2 * Real.exp (-ε ^ 2 / (2 * ∑ e : Finset V,
          (∑ x ∈ e ∪ support (H.filter (fun g => ¬ Disjoint e g)), degree H x : ℝ) ^ 2)) := by
  have hfmeas : Measurable
      (fun ω : Finset V → Bool => (degree (residual H (H.filter (fun g => ω g = true))) v : ℝ)) :=
    measurable_of_finite _
  refine mcdiarmid_two_sided_const ν
    (fun ω => (degree (residual H (H.filter (fun g => ω g = true))) v : ℝ))
    hfmeas.stronglyMeasurable Integrable.of_finite ?_ hε
  intro j ω ω' h
  exact residualDegConfig_boundedDiff H v j ω ω' (fun g hg => h g hg)

end Nibble

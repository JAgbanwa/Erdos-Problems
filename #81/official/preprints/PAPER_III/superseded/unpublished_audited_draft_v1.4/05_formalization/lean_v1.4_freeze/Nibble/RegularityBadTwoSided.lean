/-
# Nibble — two-sided regularity-failure event : measurability and `P < 1`

Standalone, Mathlib-only. The two-sided companion of `RegularityBad`. Where `RegularityBad` handled
the lower tail (residual degree dropping too low), this packages the *two-sided* deviation event

  `Bad₂ = {ω | ∃ v, c ≤ |deg(residual) v − E[deg(residual) v]|}`

directly from the two-sided Chebyshev bound `all_vertices_residualDeg_concentration`. It is the form
the step-2 near-regularity invariant consumes: outside `Bad₂` every residual degree stays within `c`
of its mean, so combined with mean lower/upper bounds the residual is `NearlyRegular`.

* `measurableSet_regularityBadTwoSided` — `Bad₂` is measurable.
* `regularityBadTwoSided_prob_lt_one` — `P(Bad₂) < 1` whenever `∑Var/c² < 1`.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.Basic
import Nibble.Round
import Nibble.Covered
import Nibble.Chebyshev
import Nibble.RegularityBad
import Nibble.Prelude

open MeasureTheory ProbabilityTheory Finset Hypergraph
open scoped Classical

namespace Nibble

variable {V : Type*} [DecidableEq V] [Fintype V] {Ω : Type*} [MeasureSpace Ω]
  [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- **Two-sided regularity-failure event is measurable.** -/
theorem measurableSet_regularityBadTwoSided {H : Finset (Finset V)} {p : ℝ} {c : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) :
    MeasurableSet {ω | ∃ v : V, c ≤ |(degree (Hypergraph.residual H (retainedSet H ρ ω)) v : ℝ)
      - (ℙ : Measure Ω)[fun ω => (degree (Hypergraph.residual H (retainedSet H ρ ω)) v : ℝ)]|} := by
  rw [Set.setOf_exists]
  refine MeasurableSet.iUnion (fun v => ?_)
  refine measurableSet_le measurable_const ?_
  exact ((measurable_residual_degree ρ v).sub measurable_const).abs

/-- **Two-sided regularity-failure probability is `< 1`.** If `∑Var/c² < 1`, then `P(Bad₂) < 1`. -/
theorem regularityBadTwoSided_prob_lt_one {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) {c : ℝ} (hc : 0 < c)
    (hsmall : (∑ v : V, ENNReal.ofReal
        (Var[fun ω => (degree (Hypergraph.residual H (retainedSet H ρ ω)) v : ℝ);
          (ℙ : Measure Ω)] / c ^ 2)) < 1) :
    ((ℙ : Measure Ω) {ω | ∃ v : V,
        c ≤ |(degree (Hypergraph.residual H (retainedSet H ρ ω)) v : ℝ)
          - (ℙ : Measure Ω)[fun ω => (degree (Hypergraph.residual H (retainedSet H ρ ω)) v : ℝ)]|}).toReal
      < 1 := by
  have hsub : {ω | ∃ v : V, c ≤ |(degree (Hypergraph.residual H (retainedSet H ρ ω)) v : ℝ)
        - (ℙ : Measure Ω)[fun ω => (degree (Hypergraph.residual H (retainedSet H ρ ω)) v : ℝ)]|}
      ⊆ ⋃ v ∈ (Finset.univ : Finset V),
        {ω | c ≤ |(degree (Hypergraph.residual H (retainedSet H ρ ω)) v : ℝ)
          - (ℙ : Measure Ω)[fun ω => (degree (Hypergraph.residual H (retainedSet H ρ ω)) v : ℝ)]|} := by
    intro ω hω
    obtain ⟨v, hv⟩ := hω
    exact Set.mem_biUnion (Finset.mem_univ v) hv
  have hle := (measure_mono hsub).trans (all_vertices_residualDeg_concentration ρ hc)
  have hlt := lt_of_le_of_lt hle hsmall
  have hne := (hlt.trans_le le_top).ne
  calc _ < (1 : ENNReal).toReal := (ENNReal.toReal_lt_toReal hne (by simp)).mpr hlt
    _ = 1 := by simp

end Nibble

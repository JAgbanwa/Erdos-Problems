/-
# Nibble — Module C4b-3a : union bound of the retained-degree concentration over all vertices

Standalone, Mathlib-only. Foundation for the Rödl-nibble project.

Module C4a gives, for each vertex `v`, a two-sided concentration of the retained degree with
failure probability `≤ 2·exp(-2t²/deg v)`. A union bound over all vertices shows that, except with
probability `∑_v 2·exp(-2t²/deg v)`, *every* vertex's retained degree is within `t` of its mean
`p·deg v` — the per-round regularity-preservation input to the round invariant C4.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.Basic
import Nibble.Concentration
import Nibble.Expectation
import Nibble.RoundConcentration
import Nibble.RoundConcentrationTwoSided
import Nibble.Prelude

open MeasureTheory ProbabilityTheory Finset Hypergraph

namespace Nibble

variable {V : Type*} [DecidableEq V] [Fintype V] {Ω : Type*} [MeasureSpace Ω]
  [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- **C4b-3a — all-vertices union bound.** The probability that *some* vertex's retained degree
deviates from its mean `p·deg v` by more than `t` is at most `∑_v 2·exp(-2t²/deg v)`. -/
theorem all_vertices_concentration {H : Finset (Finset V)} {p : ℝ}
    (ρ : Retention (Ω := Ω) H p) (t : ℝ) (ht : 0 ≤ t) :
    (ℙ : Measure Ω) (⋃ v ∈ (Finset.univ : Finset V),
        {ω | t < |(∑ e ∈ H.filter (fun e => v ∈ e), ρ.I e ω) - p * (degree H v : ℝ)|})
      ≤ ∑ v : V, 2 * ENNReal.ofReal (Real.exp (-2 * t ^ 2 / (degree H v : ℝ))) := by
  calc (ℙ : Measure Ω) (⋃ v ∈ (Finset.univ : Finset V),
          {ω | t < |(∑ e ∈ H.filter (fun e => v ∈ e), ρ.I e ω) - p * (degree H v : ℝ)|})
      ≤ ∑ v ∈ (Finset.univ : Finset V), (ℙ : Measure Ω)
          {ω | t < |(∑ e ∈ H.filter (fun e => v ∈ e), ρ.I e ω) - p * (degree H v : ℝ)|} :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ v : V, 2 * ENNReal.ofReal (Real.exp (-2 * t ^ 2 / (degree H v : ℝ))) :=
        Finset.sum_le_sum (fun v _ => retained_degree_concentration ρ v t ht)

end Nibble

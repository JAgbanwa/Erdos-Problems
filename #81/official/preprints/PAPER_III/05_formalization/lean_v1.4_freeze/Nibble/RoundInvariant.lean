/-
# Nibble — C4 synthesis : the round regularity invariant (whp)

Standalone, Mathlib-only. Combines the residual-degree **mean** lower bound (C4b-3b(3),
`residual_degree_expectation_lower`) with the **concentration** (Chebyshev, Layer Ch) to conclude
that, except with small probability, *every* vertex keeps a residual degree close to
`deg(v)·(1 − rΔp)` — i.e. the residual stays near-regular after one nibble round.

Failure-probability form (cleanest — no complements): the probability that *some* vertex's residual
degree drops below `deg(v)·(1−rΔp) − c` is at most `∑_v Var_v / c²`.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.Chebyshev
import Nibble.ResidualDegree
import Nibble.Prelude

open MeasureTheory ProbabilityTheory Finset Hypergraph

namespace Nibble

variable {V : Type*} [DecidableEq V] [Fintype V] {Ω : Type*} [MeasureSpace Ω]
  [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- **C4 — round regularity invariant (failure probability).** After one nibble round, the
probability that some vertex's residual degree falls below `deg(v)·(1 − rΔp) − c` is at most
`∑_v Var_v / c²`. Hence, whp, every residual degree stays `≥ deg(v)·(1−rΔp) − c`: near-regularity
is preserved. -/
theorem round_regularity_failure {H : Finset (Finset V)} {p : ℝ} {r Δ : ℕ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : IsUniform H r) (hΔ : ∀ x, degree H x ≤ Δ) {c : ℝ} (hc : 0 < c) :
    (ℙ : Measure Ω) {ω | ∃ v : V,
        (degree (residual H (retainedSet H ρ ω)) v : ℝ) ≤ (degree H v : ℝ) * (1 - r * Δ * p) - c}
      ≤ ∑ v : V, ENNReal.ofReal
          (Var[fun ω => (degree (residual H (retainedSet H ρ ω)) v : ℝ); (ℙ : Measure Ω)] / c ^ 2) := by
  refine le_trans (measure_mono ?_) (all_vertices_residualDeg_concentration ρ hc)
  intro ω hω
  obtain ⟨v, hv⟩ := hω
  rw [Set.mem_iUnion₂]
  refine ⟨v, Finset.mem_univ v, ?_⟩
  rw [Set.mem_setOf_eq]
  have hmean : (degree H v : ℝ) * (1 - r * Δ * p)
      ≤ (ℙ : Measure Ω)[fun ω => (degree (residual H (retainedSet H ρ ω)) v : ℝ)] :=
    residual_degree_expectation_lower ρ hp0 hp1 hr hΔ v
  rw [le_abs]
  right
  simp only [neg_sub]
  linarith

end Nibble

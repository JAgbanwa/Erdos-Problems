/-
# Nibble — Module C4b-2 : expected matching size lower bound

Standalone, Mathlib-only. Foundation for the Rödl-nibble project.

Each edge survives the round (enters the matching) with probability `p·(1-p)^{c(e)}` (module
C4b-1). Since `c(e) ≤ r·Δ` (module C4b-0) and `0 ≤ 1-p ≤ 1`, every survival probability is at
least `p·(1-p)^{rΔ}`; summing over the `|H|` edges lower-bounds the expected matching size:

  `∑_{e∈H} ℙ(e survives) ≥ |H| · p·(1-p)^{rΔ}`.

Multiplying by `r` (each matched edge covers `r` vertices, module A3a) turns this into the covered
vertex lower bound `E[covered] ≥ r·|H|·p·(1-p)^{rΔ}` — a definite fraction of the vertex set.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.Basic
import Nibble.Conflict
import Nibble.Survival
import Nibble.Prelude

open MeasureTheory ProbabilityTheory Finset Hypergraph

namespace Nibble

variable {V : Type*} [DecidableEq V] {Ω : Type*} [MeasureSpace Ω]
  [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- **C4b-2 — expected matching size lower bound.** For a Bernoulli retention on an `r`-uniform
hypergraph with max degree `≤ Δ`, the total survival probability (the expected number of edges
entering the round's matching) is at least `|H| · p·(1-p)^{rΔ}`. -/
theorem matching_expectation_lower {H : Finset (Finset V)} {p : ℝ} {r Δ : ℕ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : IsUniform H r) (hΔ : ∀ x, degree H x ≤ Δ) :
    (H.card : ENNReal) * ENNReal.ofReal (p * (1 - p) ^ (r * Δ))
      ≤ ∑ e ∈ H, (ℙ : Measure Ω) (ρ.A e ∩ ⋂ f ∈ conflicts H e, (ρ.A f)ᶜ) := by
  have hterm : ∀ e ∈ H,
      ENNReal.ofReal (p * (1 - p) ^ (r * Δ))
        ≤ (ℙ : Measure Ω) (ρ.A e ∩ ⋂ f ∈ conflicts H e, (ρ.A f)ᶜ) := by
    intro e he
    rw [edge_survives_prob ρ hp0 hp1 he]
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ hp0
    exact pow_le_pow_of_le_one (by linarith) (by linarith)
      (conflicts_card_le_of_uniform hr hΔ he)
  calc (H.card : ENNReal) * ENNReal.ofReal (p * (1 - p) ^ (r * Δ))
      = ∑ _e ∈ H, ENNReal.ofReal (p * (1 - p) ^ (r * Δ)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ e ∈ H, (ℙ : Measure Ω) (ρ.A e ∩ ⋂ f ∈ conflicts H e, (ρ.A f)ᶜ) :=
        Finset.sum_le_sum hterm

end Nibble

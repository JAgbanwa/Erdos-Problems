/-
# Nibble — per-round covering fraction (with parameters)

Standalone, Mathlib-only. Concrete T3 wiring: one nibble round covers a definite *fraction* of the
vertices. Combining
* `exists_large_round_matching` (∃ ω, `|matching| ≥ |H|·p·(1-p)^{rΔ}`),
* `covered_card_eq` (`|covered| = r·|matching|`),
* `edge_count_lower` (`(1-μ)·d·|V| ≤ r·|H|`),
gives: there is an outcome whose covered set has size `≥ (1-μ)·d·p·(1-p)^{rΔ}·|V|`. So the covering
fraction is `(1-μ)·d·p·(1-p)^{rΔ}`; with `p ≈ 1/d` this is a positive constant `≈ e^{-r}`, which
feeds the geometric-decay convergence (`exists_uncovered_below`) to discharge `NibbleTheorem`.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.Basic
import Nibble.Round
import Nibble.Regular
import Nibble.Covered
import Nibble.CoveredExpectation
import Nibble.Wiring
import Nibble.Prelude

open MeasureTheory ProbabilityTheory Finset Hypergraph
open scoped Classical

namespace Nibble

variable {V : Type*} [DecidableEq V] [Fintype V] {Ω : Type*} [MeasureSpace Ω]
  [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- **T3 wiring — per-round covering fraction.** There is an outcome whose round covers at least a
`(1-μ)·d·p·(1-p)^{rΔ}` fraction of the `|V|` vertices. -/
theorem exists_round_covers_fraction {H : Finset (Finset V)} {p d μ : ℝ} {r Δ : ℕ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : IsUniform H r) (hΔ : ∀ x, degree H x ≤ Δ) (hReg : NearlyRegular H d μ) :
    ∃ ω, (1 - μ) * d * (p * (1 - p) ^ (r * Δ)) * (Fintype.card V : ℝ)
      ≤ ((covered (retainedSet H ρ ω)).card : ℝ) := by
  obtain ⟨ω, hω⟩ := exists_large_round_matching ρ hp0 hp1 hr hΔ
  refine ⟨ω, ?_⟩
  have hcovR : ((covered (retainedSet H ρ ω)).card : ℝ)
      = (r : ℝ) * ((roundMatching (retainedSet H ρ ω)).card : ℝ) := by
    have hcc := covered_card_eq (R := retainedSet H ρ ω) hr (Finset.filter_subset _ _)
    rw [hcc]; push_cast; ring
  have hnn : (0 : ℝ) ≤ p * (1 - p) ^ (r * Δ) := mul_nonneg hp0 (pow_nonneg (by linarith) _)
  have hedge := edge_count_lower hr hReg
  rw [hcovR]
  nlinarith only [mul_le_mul_of_nonneg_right hedge hnn,
    mul_le_mul_of_nonneg_left hω (Nat.cast_nonneg r), hnn, hedge]

end Nibble

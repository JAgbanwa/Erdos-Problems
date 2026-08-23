/-
# Nibble — Module C2 : the retention process and its first-moment (expectation) identities

Standalone, Mathlib-only. Foundation for the Rödl-nibble project.

A *retention process* on an `r`-uniform hypergraph `H` retains each edge independently with
probability `p`, modelled by an indicator family `I e : Ω → ℝ` on a probability space `Ω`.

This module proves the linearity-of-expectation identities the nibble's analysis consumes:
* `expected_retained_count` — `E[∑_{e∈H} I e] = p · |H|`.
* `expected_retained_degree` — `E[∑_{e∈H, v∈e} I e] = p · degree H v`.

`degree` comes from `Nibble.Basic`. Must be sorry-free and axiom-clean
`[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.Basic
import Nibble.Prelude

open MeasureTheory ProbabilityTheory Finset Hypergraph

namespace Nibble

/-- A retention process on `H` with retention probability `p`: an independent family of
`[0,1]`-valued indicators, one per edge, each with mean `p` on the edges of `H`. -/
structure Retention {V : Type*} [DecidableEq V] {Ω : Type*} [MeasureSpace Ω]
    (H : Finset (Finset V)) (p : ℝ) where
  I : Finset V → Ω → ℝ
  meas : ∀ e, Measurable (I e)
  indep : iIndepFun I (ℙ : Measure Ω)
  integrable : ∀ e, Integrable (I e) (ℙ : Measure Ω)
  expect : ∀ e ∈ H, ∫ ω, I e ω ∂(ℙ : Measure Ω) = p
  zeroone : ∀ e, ∀ᵐ ω ∂(ℙ : Measure Ω), I e ω ∈ Set.Icc (0 : ℝ) 1

variable {V : Type*} [DecidableEq V] {Ω : Type*} [MeasureSpace Ω]

/-- **C2a — expected retained-edge count.** `E[∑_{e∈H} I e] = p · |H|`. -/
theorem expected_retained_count {H : Finset (Finset V)} {p : ℝ} (ρ : Retention H p) :
    ∫ ω, (∑ e ∈ H, ρ.I e ω) ∂(ℙ : Measure Ω) = p * H.card := by
  rw [integral_finset_sum H (fun e _ => ρ.integrable e)]
  rw [Finset.sum_congr rfl (fun e he => ρ.expect e he)]
  rw [Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- **C2b — expected retained degree.** The expected number of retained edges through a vertex
`v` is `p · degree H v`. -/
theorem expected_retained_degree {H : Finset (Finset V)} {p : ℝ} (ρ : Retention H p) (v : V) :
    ∫ ω, (∑ e ∈ H.filter (fun e => v ∈ e), ρ.I e ω) ∂(ℙ : Measure Ω) = p * (degree H v : ℝ) := by
  rw [integral_finset_sum _ (fun e _ => ρ.integrable e)]
  rw [Finset.sum_congr rfl (fun e he => ρ.expect e (Finset.mem_of_mem_filter e he))]
  rw [Finset.sum_const, nsmul_eq_mul, degree, mul_comm]

end Nibble

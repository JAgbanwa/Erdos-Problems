/-
# Nibble — predictable quadratic variation reduction (①-2 assembly)

Standalone, Mathlib-only. For the Freedman/Bernstein concentration of `deg_residual(v)`, the tail is
`√(W log n)` where `W = ∑_e E[Y_e² | F_{e-1}]` is the predictable quadratic variation of the Doob
martingale. Feasibility needs `W ≲ d ≪ d²` (the whole point of variance-based over McDiarmid).

This file supplies the ASSEMBLY: given the per-coordinate conditional-variance bound
`V_e ≤ p·neighborCoef(v,e)²` (the analytic HARD CORE, dispatched separately) plus off-`H` inertia, the
sum-estimate chain (`sumSq_neighborCoef_le`) bounds `W ≤ p·M·S`. In the ν₃ regime (`p ≈ ε/d`,
`M·S ≈ d²·poly`) this is `≈ d`, closing `c ≈ √(d log n) ≪ d`.

* `condQuadVar_le` — `∑_e V_e ≤ p·M·S`, from the per-coordinate bound + sum-estimate.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.SumEstimate

open Finset

namespace Hypergraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **①-2 assembly — predictable quadratic variation bound.** Given per-coordinate conditional
variances `V_e ≤ p·neighborCoef(v,e)²` for `e ∈ H` (and `V_e ≤ 0` off `H`, the inert coordinates), the
total `∑_e V_e ≤ p·M·S`, where `M, S` bound the per-edge maximum and total of `neighborCoef`. This
reduces the variance estimate to the single per-coordinate conditional-variance bound (the hard core). -/
theorem condQuadVar_le (H : Finset (Finset V)) (v : V) {p : ℝ} (hp0 : 0 ≤ p)
    (Ve : Finset V → ℝ)
    (hVe : ∀ e ∈ H, Ve e ≤ p * (neighborCoef H v e : ℝ) ^ 2)
    (hVe0 : ∀ e ∉ H, Ve e ≤ 0)
    {M S : ℝ} (hM : ∀ e ∈ H, (neighborCoef H v e : ℝ) ≤ M)
    (hS : (∑ e ∈ H, (neighborCoef H v e : ℝ)) ≤ S) (hM0 : 0 ≤ M) :
    (∑ e : Finset V, Ve e) ≤ p * (M * S) := by
  have hsplit : (∑ e : Finset V, Ve e)
      = ∑ e ∈ Finset.univ \ H, Ve e + ∑ e ∈ H, Ve e :=
    (Finset.sum_sdiff (Finset.subset_univ H)).symm
  rw [hsplit]
  have h1 : ∑ e ∈ Finset.univ \ H, Ve e ≤ 0 :=
    Finset.sum_nonpos (fun e he => hVe0 e (Finset.mem_sdiff.mp he).2)
  have h2 : ∑ e ∈ H, Ve e ≤ p * (M * S) := by
    calc ∑ e ∈ H, Ve e
        ≤ ∑ e ∈ H, p * (neighborCoef H v e : ℝ) ^ 2 := Finset.sum_le_sum hVe
      _ = p * ∑ e ∈ H, (neighborCoef H v e : ℝ) ^ 2 := by rw [Finset.mul_sum]
      _ ≤ p * (M * S) := mul_le_mul_of_nonneg_left (sumSq_neighborCoef_le H v hM hS hM0) hp0
  linarith only [h1, h2]

end Hypergraph

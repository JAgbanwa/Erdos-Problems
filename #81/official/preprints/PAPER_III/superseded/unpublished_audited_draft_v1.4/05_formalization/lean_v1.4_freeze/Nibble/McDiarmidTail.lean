/-
# Nibble — McDiarmid M7 : the bounded-differences (McDiarmid) inequality

Standalone, Mathlib-only. Assembles the Doob martingale (M1/M2) + the conditionally sub-Gaussian
increments (M6, consumed here as the hypothesis `hM6`) via Mathlib's Azuma–Hoeffding
(`measure_sum_ge_le_of_hasCondSubgaussianMGF`) to obtain McDiarmid's inequality: the deviation of a
bounded-differences function `f` above its mean has a sub-Gaussian (exponential) tail.

The martingale increments `Y i = doob μ f i − doob μ f (i-1)` telescope: `∑_{i<n+1} Y i = f − E[f]`
(via `doob_full = f`, `doob_zero = E[f]`), so Azuma applied to `Y` gives the tail directly.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.CondHoeffding
import Nibble.McDiarmid
import Nibble.Prelude

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal

namespace Nibble

variable {n : ℕ} {α : Fin n → Type*} [∀ i, MeasurableSpace (α i)]

/-- **M7 — McDiarmid's inequality (upper tail).** Given the Doob increments are conditionally
sub-Gaussian (`hM6`, the output of M6), the deviation of `f` above its mean has a sub-Gaussian tail:
`ℙ(ε ≤ f − E[f]) ≤ exp(-ε² / (2 ∑ cY))`. -/
theorem mcdiarmid_upper [StandardBorelSpace (∀ i, α i)]
    (μ : Measure (∀ i, α i)) [IsProbabilityMeasure μ]
    (f : (∀ i, α i) → ℝ) (hf : StronglyMeasurable f) (hfi : Integrable f μ)
    (cY : ℕ → ℝ≥0)
    (hM6 : ∀ k, k < n → HasCondSubgaussianMGF (exposureσ k) (exposureσ_le k)
        (fun ω => doob μ f (k + 1) ω - doob μ f k ω) (cY (k + 1)) μ)
    {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ f ω - ∫ x, f x ∂μ}
      ≤ Real.exp (-ε ^ 2 / (2 * ((∑ i ∈ Finset.range n, cY (i + 1) : ℝ≥0) : ℝ))) := by
  classical
  set Y : ℕ → (∀ i, α i) → ℝ := fun i ω => doob μ f i ω - doob μ f (i - 1) ω with hY
  set cY' : ℕ → ℝ≥0 := fun i => if i = 0 then 0 else cY i with hcY'
  -- Y 0 = 0
  have hY0 : Y 0 = 0 := by
    funext ω; simp [hY]
  -- adapted
  have hadapt : StronglyAdapted exposureFiltration Y := by
    intro i
    refine (doob_stronglyMeasurable μ f i).sub
      ((doob_stronglyMeasurable μ f (i - 1)).mono (exposureσ_mono (Nat.sub_le i 1)))
  -- h0
  have h0 : HasSubgaussianMGF (Y 0) (cY' 0) μ := by
    rw [hY0]; simpa [hcY'] using HasSubgaussianMGF.zero (μ := μ)
  -- h_subG from hM6
  have hsub : ∀ i < (n + 1) - 1, HasCondSubgaussianMGF (exposureFiltration i)
      (exposureFiltration.le i) (Y (i + 1)) (cY' (i + 1)) μ := by
    intro i hi
    have hin : i < n := by omega
    have hcy : cY' (i + 1) = cY (i + 1) := by simp [hcY']
    have hYi : Y (i + 1) = fun ω => doob μ f (i + 1) ω - doob μ f i ω := by
      funext ω; simp [hY]
    rw [hcy, hYi]
    exact hM6 i hin
  -- Azuma
  have hazuma := measure_sum_ge_le_of_hasCondSubgaussianMGF (μ := μ) (Y := Y) (cY := cY')
    (ℱ := exposureFiltration) hadapt h0 (n + 1) hsub hε
  -- telescoping sum = f - E[f]  (pointwise)
  have hsum : ∀ ω, ∑ i ∈ Finset.range (n + 1), Y i ω = f ω - ∫ x, f x ∂μ := by
    intro ω
    have htel : ∑ i ∈ Finset.range (n + 1), Y i ω
        = doob μ f n ω - doob μ f 0 ω := by
      rw [Finset.sum_range_succ' (fun i => Y i ω) n]
      have : ∀ i ∈ Finset.range n, Y (i + 1) ω = doob μ f (i + 1) ω - doob μ f i ω := by
        intro i _; simp [hY]
      rw [Finset.sum_congr rfl this,
        Finset.sum_range_sub (fun i => doob μ f i ω) n]
      simp [hY0]
    rw [htel, doob_full μ hf hfi, doob_zero μ f]
  -- rewrite the event and variance
  have hset : {ω | ε ≤ ∑ i ∈ Finset.range (n + 1), Y i ω}
      = {ω | ε ≤ f ω - ∫ x, f x ∂μ} := by
    ext ω; simp only [Set.mem_setOf_eq, hsum ω]
  have hvar : (∑ i ∈ Finset.range (n + 1), cY' i) = ∑ i ∈ Finset.range n, cY (i + 1) := by
    rw [Finset.sum_range_succ' cY' n]
    have : ∀ i ∈ Finset.range n, cY' (i + 1) = cY (i + 1) := by intro i _; simp [hcY']
    rw [Finset.sum_congr rfl this]
    simp [hcY']
  rw [hset, hvar] at hazuma
  exact hazuma

end Nibble

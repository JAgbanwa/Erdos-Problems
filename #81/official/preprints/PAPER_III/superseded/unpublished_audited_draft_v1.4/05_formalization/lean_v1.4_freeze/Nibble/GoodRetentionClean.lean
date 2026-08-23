/-
# Nibble — good-retention bridge with `hsmall` discharged

Standalone, Mathlib-only. The clean form of `exists_good_retention`: with the parameter condition
`c² > |V|·Δ²`, the abstract `hsmall` hypothesis is discharged (via `variance_sum_lt_one` and
`regularityBad_prob_toReal_le`, both ρ-independent), leaving a purely combinatorial statement. For a
`r`-uniform, max-degree-`≤ Δ` hypergraph, there is a retained subset `R' ⊆ H'` whose round preserves
near-regularity and covers `≥ |H'|·p·(1−p)^{rΔ} − |V|·(|V|·Δ²/c²)`. This is exactly what the step-2
iteration consumes to build the strategy `R` and prove the covering oracle.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.GoodRetentionFinset
import Nibble.VarianceBound
import Nibble.RegularityBadBound
import Nibble.Prelude

open MeasureTheory ProbabilityTheory Finset Hypergraph

namespace Nibble

/-- **Good retention, `hsmall` discharged.** With `c² > |V|·Δ²`, there is `R' ⊆ H'` preserving
near-regularity and covering `≥ |H'|·p·(1−p)^{rΔ} − |V|·(|V|·Δ²/c²)`. -/
theorem exists_good_retention' {V : Type u} [Fintype V] [DecidableEq V]
    (H' : Finset (Finset V)) {p : ℝ} {r Δ : ℕ} {c : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hr1 : 1 ≤ r)
    (hr : IsUniform H' r) (hΔ : ∀ x, degree H' x ≤ Δ) (hc : 0 < c)
    (hcΔ : (Fintype.card V : ℝ) * (Δ : ℝ) ^ 2 < c ^ 2) :
    ∃ R' : Finset (Finset V), R' ⊆ H'
      ∧ (∀ v : V, (degree H' v : ℝ) * (1 - r * Δ * p) - c
          < (degree (Hypergraph.residual H' R') v : ℝ))
      ∧ (H'.card : ℝ) * (p * (1 - p) ^ (r * Δ))
          - (Fintype.card V : ℝ) * ((Fintype.card V : ℝ) * (Δ : ℝ) ^ 2 / c ^ 2)
          ≤ ((roundMatching R').card : ℝ) := by
  refine exists_good_retention (δ := (Fintype.card V : ℝ) * (Δ : ℝ) ^ 2 / c ^ 2)
    H' hp0 hp1 hr1 hr hΔ hc ?_
  intro Ω _ _ ρ
  exact ⟨variance_sum_lt_one ρ hΔ hcΔ, regularityBad_prob_toReal_le ρ hp0 hp1 hr hΔ hc⟩

end Nibble

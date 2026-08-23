/-
# Nibble — Finset-level Freedman good retention

Standalone, Mathlib-only. This is the Finset-level companion of `exists_good_round_freedman`: it hides
the probability space produced by `exists_bernoulliRetention` and exposes a retained subset `R' ⊆ H`
with the same near-regularity conclusion as the old Chebyshev bridge, but with the exponential
Freedman bad-event penalty.
-/
import Nibble.GoodRoundFreedman
import Nibble.BernoulliSpace
import Nibble.Prelude

open MeasureTheory ProbabilityTheory Finset Hypergraph
open scoped Classical

namespace Nibble

/-- **Finset-level Freedman good retention.** If the all-vertices Freedman tail is `< 1`, there is
`R' ⊆ H` preserving the lower residual-degree threshold and covering
`H.card * p(1-p)^(rΔ)` up to the exponential bad-event penalty. -/
theorem exists_good_retention_freedman' {V : Type u} [Fintype V] [DecidableEq V]
    (H : Finset (Finset V)) {p : ℝ} {r Δ : ℕ} {c : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hr1 : 1 ≤ r)
    (hr : IsUniform H r) (hΔ : ∀ x, degree H x ≤ Δ) (hΔ0 : 0 < Δ) (hc : 0 < c)
    (hVpos : ∀ v : V, 0 < degree H v →
      0 < (∑ e ∈ H.filter (fun f => v ∈ f),
          (((H.filter (fun f => v ∈ f)).filter
            (fun e' => ¬ Disjoint (depNbhd H e) (depNbhd H e'))).card : ℝ)) * ((r : ℝ) * Δ * p))
    (hsmall : (Fintype.card V : ℝ) * (2 * Real.exp (-c ^ 2 / (2 * ((Δ : ℝ) ^ 2 * ((r : ℝ) * Δ * p)
          + (Δ : ℝ) / 3 * c)))) < 1) :
    ∃ R' : Finset (Finset V), R' ⊆ H
      ∧ (∀ v : V, (degree H v : ℝ) * (1 - r * Δ * p) - c
          < (degree (Hypergraph.residual H R') v : ℝ))
      ∧ (H.card : ℝ) * (p * (1 - p) ^ (r * Δ))
          - (Fintype.card V : ℝ) * ((Fintype.card V : ℝ)
              * (2 * Real.exp (-c ^ 2 / (2 * ((Δ : ℝ) ^ 2 * ((r : ℝ) * Δ * p)
                + (Δ : ℝ) / 3 * c)))))
          ≤ ((roundMatching R').card : ℝ) := by
  obtain ⟨Ω, mΩ, hProb, ⟨ρ⟩⟩ := exists_bernoulliRetention H hp0 hp1
  letI := mΩ
  letI := hProb
  obtain ⟨ω, hreg, hcov⟩ :=
    exists_good_round_freedman ρ hp0 hp1 hr1 hr hΔ hΔ0 hc hVpos hsmall
  exact ⟨retainedSet H ρ ω, Finset.filter_subset _ _, hreg, hcov⟩

end Nibble

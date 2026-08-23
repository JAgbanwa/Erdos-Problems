/-
# Nibble — the retention strategy `R` (step-2 part a)

Standalone, Mathlib-only. Defines the fixed retention strategy `R = nibbleStrategy` that the nibble
iteration applies to each residual: on a hypergraph that is `r`-uniform with max degree `≤ Δ`, it
returns the good retained subset from `exists_good_retention'` (via `Classical.choose`); on any other
hypergraph it returns the hypergraph unchanged. The parameters `r, Δ, p, c` and their side conditions
are fixed data of the run.

* `nibbleStrategy_subset` — `R H' ⊆ H'` (the `hR` hypothesis of the discharge lemmas).
* `nibbleStrategy_spec` — on an `r`-uniform, max-degree-`≤ Δ` hypergraph, `R H'` preserves
  near-regularity and covers `≥ |H'|·p·(1−p)^{rΔ} − |V|·(|V|·Δ²/c²)`.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.GoodRetentionClean
import Nibble.Iteration

open MeasureTheory ProbabilityTheory Finset Hypergraph
open scoped Classical

namespace Nibble

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The retention strategy: the good retained subset when the input is `r`-uniform with max degree
`≤ Δ`, else the input unchanged. -/
noncomputable def nibbleStrategy (r Δ : ℕ) (p c : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hr1 : 1 ≤ r)
    (hc : 0 < c) (hcΔ : (Fintype.card V : ℝ) * (Δ : ℝ) ^ 2 < c ^ 2) :
    Finset (Finset V) → Finset (Finset V) :=
  fun H' =>
    if h : IsUniform H' r ∧ (∀ x, degree H' x ≤ Δ)
    then (exists_good_retention' H' hp0 hp1 hr1 h.1 h.2 hc hcΔ).choose
    else H'

/-- **`hR`** — the strategy keeps edges inside their input. -/
theorem nibbleStrategy_subset (r Δ : ℕ) (p c : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hr1 : 1 ≤ r)
    (hc : 0 < c) (hcΔ : (Fintype.card V : ℝ) * (Δ : ℝ) ^ 2 < c ^ 2) (H' : Finset (Finset V)) :
    nibbleStrategy r Δ p c hp0 hp1 hr1 hc hcΔ H' ⊆ H' := by
  rw [nibbleStrategy]
  by_cases h : IsUniform H' r ∧ (∀ x, degree H' x ≤ Δ)
  · rw [dif_pos h]
    exact (exists_good_retention' H' hp0 hp1 hr1 h.1 h.2 hc hcΔ).choose_spec.1
  · rw [dif_neg h]

/-- **Strategy spec** — on a valid hypergraph, the strategy's round preserves near-regularity and
covers a definite amount. -/
theorem nibbleStrategy_spec (r Δ : ℕ) (p c : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hr1 : 1 ≤ r)
    (hc : 0 < c) (hcΔ : (Fintype.card V : ℝ) * (Δ : ℝ) ^ 2 < c ^ 2) (H' : Finset (Finset V))
    (huni : IsUniform H' r) (hdeg : ∀ x, degree H' x ≤ Δ) :
    (∀ v : V, (degree H' v : ℝ) * (1 - r * Δ * p) - c
        < (degree (Hypergraph.residual H' (nibbleStrategy r Δ p c hp0 hp1 hr1 hc hcΔ H')) v : ℝ))
      ∧ (H'.card : ℝ) * (p * (1 - p) ^ (r * Δ))
          - (Fintype.card V : ℝ) * ((Fintype.card V : ℝ) * (Δ : ℝ) ^ 2 / c ^ 2)
          ≤ ((roundMatching (nibbleStrategy r Δ p c hp0 hp1 hr1 hc hcΔ H')).card : ℝ) := by
  have hkey : nibbleStrategy r Δ p c hp0 hp1 hr1 hc hcΔ H'
      = (exists_good_retention' H' hp0 hp1 hr1 huni hdeg hc hcΔ).choose := by
    rw [nibbleStrategy]; exact dif_pos ⟨huni, hdeg⟩
  rw [hkey]
  exact ⟨(exists_good_retention' H' hp0 hp1 hr1 huni hdeg hc hcΔ).choose_spec.2.1,
    (exists_good_retention' H' hp0 hp1 hr1 huni hdeg hc hcΔ).choose_spec.2.2⟩

end Nibble

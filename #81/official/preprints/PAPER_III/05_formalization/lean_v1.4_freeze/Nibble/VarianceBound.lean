/-
# Nibble — the Chebyshev variance sum is `< 1` for large `c`

Standalone, Mathlib-only. The parameter condition that unblocks the step-2 invariant: the residual
degree variance `Var[deg_residual v]` has a ρ-INDEPENDENT bound (`residualDeg_variance_le` in
`Nibble.Chebyshev`), namely by the number of interacting edge pairs through `v`, which is at most
`(deg v)² ≤ Δ²`. Summing over the `n = |V|` vertices gives `∑_v Var ≤ n·Δ²`, so choosing `c` with
`c² > n·Δ²` makes the Chebyshev sum `∑_v Var/c² < 1` — exactly the `hsmall` hypothesis that
`exists_good_round` / `regularityBadTwoSided_prob_lt_one` consume.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.Basic
import Nibble.Round
import Nibble.Covered
import Nibble.Chebyshev
import Nibble.Prelude

open MeasureTheory ProbabilityTheory Finset Hypergraph

namespace Nibble

variable {V : Type*} [DecidableEq V] [Fintype V] {Ω : Type*} [MeasureSpace Ω]
  [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- **Variance sum `< 1` for large `c`.** With `c² > |V|·Δ²`, the Chebyshev variance sum over all
vertices is `< 1`. Uses the ρ-independent bound `residualDeg_variance_le` (variance ≤ number of
interacting pairs ≤ (deg v)² ≤ Δ²) and sums over the `|V|` vertices. -/
theorem variance_sum_lt_one {H : Finset (Finset V)} {p : ℝ} {Δ : ℕ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (hΔ : ∀ x, degree H x ≤ Δ) {c : ℝ}
    (hc : (Fintype.card V : ℝ) * (Δ : ℝ) ^ 2 < c ^ 2) :
    (∑ v : V, ENNReal.ofReal
      (Var[fun ω => (degree (Hypergraph.residual H (retainedSet H ρ ω)) v : ℝ);
        (ℙ : Measure Ω)] / c ^ 2)) < 1 := by
  -- For each vertex v, variance ≤ (deg v)² ≤ Δ²
  have hvar_bound : ∀ v : V,
      Var[fun ω => (degree (Hypergraph.residual H (retainedSet H ρ ω)) v : ℝ); (ℙ : Measure Ω)]
        ≤ (Δ : ℝ) ^ 2 := by
    intro v
    have := residualDeg_variance_le ρ v
    -- The double sum is bounded by |{e ∈ H : v ∈ e}|² ≤ Δ²
    have hcard_bound : ((H.filter (fun f => v ∈ f)).card : ℝ) ≤ Δ := by
      have : (H.filter (fun f => v ∈ f)).card ≤ Δ := hΔ v
      exact_mod_cast this
    -- Each inner sum has at most |{e ∈ H : v ∈ e}| terms
    calc Var[fun ω => (degree (Hypergraph.residual H (retainedSet H ρ ω)) v : ℝ); (ℙ : Measure Ω)]
        ≤ ∑ e ∈ H.filter (fun f => v ∈ f),
            (((H.filter (fun f => v ∈ f)).filter
              (fun e' => ¬ Disjoint (depNbhd H e) (depNbhd H e'))).card : ℝ) := this
      _ ≤ ∑ _e ∈ H.filter (fun f => v ∈ f),
            (((H.filter (fun f => v ∈ f)).card : ℝ)) := by
            apply Finset.sum_le_sum
            intro e _
            exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
      _ = (((H.filter (fun f => v ∈ f)).card : ℝ)) * (((H.filter (fun f => v ∈ f)).card : ℝ)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (Δ : ℝ) ^ 2 := by
            have hcard_nonneg : (0 : ℝ) ≤ ((H.filter (fun f => v ∈ f)).card : ℝ) := Nat.cast_nonneg _
            nlinarith only [hcard_bound, sq_nonneg ((Δ : ℝ) - ((H.filter (fun f => v ∈ f)).card : ℝ))]
  -- Bound the sum by |V| * ENNReal.ofReal (Δ² / c²)
  have hterm_bound : ∀ v : V,
      ENNReal.ofReal (Var[fun ω => (degree (Hypergraph.residual H (retainedSet H ρ ω)) v : ℝ); (ℙ : Measure Ω)] / c ^ 2)
        ≤ ENNReal.ofReal ((Δ : ℝ) ^ 2 / c ^ 2) := by
    intro v
    exact ENNReal.ofReal_le_ofReal
      (by gcongr; exact hvar_bound v)
  have hsum_bound : ∑ v : V, ENNReal.ofReal
        (Var[fun ω => (degree (Hypergraph.residual H (retainedSet H ρ ω)) v : ℝ); (ℙ : Measure Ω)] / c ^ 2)
      ≤ ↑(Fintype.card V) * ENNReal.ofReal ((Δ : ℝ) ^ 2 / c ^ 2) := by
    have h1 : ∑ v : V, ENNReal.ofReal
          (Var[fun ω => (degree (Hypergraph.residual H (retainedSet H ρ ω)) v : ℝ); (ℙ : Measure Ω)] / c ^ 2)
        ≤ ∑ _v : V, ENNReal.ofReal ((Δ : ℝ) ^ 2 / c ^ 2) :=
      Finset.sum_le_sum (fun v _ => hterm_bound v)
    have h2 : ∑ _v : V, ENNReal.ofReal ((Δ : ℝ) ^ 2 / c ^ 2) =
        ↑(Fintype.card V) * ENNReal.ofReal ((Δ : ℝ) ^ 2 / c ^ 2) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have h3 : ∑ v : V, ENNReal.ofReal
          (Var[fun ω => (degree (Hypergraph.residual H (retainedSet H ρ ω)) v : ℝ); (ℙ : Measure Ω)] / c ^ 2)
        ≤ ↑(Fintype.card V) * ENNReal.ofReal ((Δ : ℝ) ^ 2 / c ^ 2) := le_trans h1 h2.le
    exact h3
  -- Now show |V| * Δ²/c² < 1 when |V| * Δ² < c²
  have hc2_pos : (0 : ℝ) < c ^ 2 := by nlinarith
  have hprod_lt_one : (Fintype.card V : ℝ) * ((Δ : ℝ) ^ 2 / c ^ 2) < 1 := by
    rw [mul_div_assoc']
    exact (div_lt_one hc2_pos).mpr hc
  have hfinal : ↑(Fintype.card V) * ENNReal.ofReal ((Δ : ℝ) ^ 2 / c ^ 2) < 1 := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (Fintype.card V : ℝ))]
    exact ENNReal.ofReal_lt_one.mpr hprod_lt_one
  exact lt_of_le_of_lt hsum_bound hfinal

end Nibble

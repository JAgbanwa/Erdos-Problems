/-
# Nibble — ρ-independent bound on the regularity-failure probability

Standalone, Mathlib-only. Discharges the `P(Bad) ≤ δ` half of the step-2 `hsmall` hypothesis with the
ρ-INDEPENDENT δ = |V|·Δ²/c². Uses `round_regularity_failure` (P(Bad) ≤ ∑Var/c²) and the per-vertex
variance bound `Var ≤ Δ²` (from `residualDeg_variance_le` in `Nibble.Chebyshev`: variance ≤ number of
interacting pairs ≤ (deg v)² ≤ Δ²).

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.Basic
import Nibble.Round
import Nibble.Covered
import Nibble.Chebyshev
import Nibble.RoundInvariant
import Nibble.Prelude

open MeasureTheory ProbabilityTheory Finset Hypergraph

namespace Nibble

variable {V : Type*} [DecidableEq V] [Fintype V] {Ω : Type*} [MeasureSpace Ω]
  [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- Per-vertex residual-degree variance is bounded by `Δ²` (ρ-independent). -/
theorem residualDeg_variance_le_sq {H : Finset (Finset V)} {p : ℝ} {Δ : ℕ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (hΔ : ∀ x, degree H x ≤ Δ) (v : V) :
    Var[fun ω => (degree (Hypergraph.residual H (retainedSet H ρ ω)) v : ℝ);
      (ℙ : Measure Ω)] ≤ (Δ : ℝ) ^ 2 := by
  have hvar := residualDeg_variance_le ρ v
  have hcard : ((H.filter (fun f => v ∈ f)).card : ℝ) ≤ Δ := by
    exact_mod_cast hΔ v
  calc
    Var[fun ω => (degree (Hypergraph.residual H (retainedSet H ρ ω)) v : ℝ);
        (ℙ : Measure Ω)]
        ≤ ∑ e ∈ H.filter (fun f => v ∈ f),
            (((H.filter (fun f => v ∈ f)).filter
              (fun e' => ¬ Disjoint (depNbhd H e) (depNbhd H e'))).card : ℝ) := hvar
    _ ≤ ∑ _e ∈ H.filter (fun f => v ∈ f),
          ((H.filter (fun f => v ∈ f)).card : ℝ) := by
        apply Finset.sum_le_sum
        intro e _
        exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
    _ = ((H.filter (fun f => v ∈ f)).card : ℝ) *
          ((H.filter (fun f => v ∈ f)).card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Δ : ℝ) ^ 2 := by
        have hnonneg : (0 : ℝ) ≤ ((H.filter (fun f => v ∈ f)).card : ℝ) :=
          Nat.cast_nonneg _
        nlinarith

/-- **Regularity-failure probability, ρ-independent bound.** `P(Bad).toReal ≤ |V|·Δ²/c²`. This is
the `δ := |V|·Δ²/c²` needed for the `hsmall` hypothesis of `exists_good_retention`. -/
theorem regularityBad_prob_toReal_le {H : Finset (Finset V)} {p : ℝ} {r Δ : ℕ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : IsUniform H r) (hΔ : ∀ x, degree H x ≤ Δ) {c : ℝ} (hc : 0 < c) :
    ((ℙ : Measure Ω) {ω | ∃ v : V,
        (degree (Hypergraph.residual H (retainedSet H ρ ω)) v : ℝ)
          ≤ (degree H v : ℝ) * (1 - r * Δ * p) - c}).toReal
      ≤ (Fintype.card V : ℝ) * (Δ : ℝ) ^ 2 / c ^ 2 := by
  have hprob := round_regularity_failure ρ hp0 hp1 hr hΔ hc
  have hc2 : 0 < c ^ 2 := sq_pos_of_pos hc
  have hterm : ∀ v : V,
      ENNReal.ofReal
          (Var[fun ω => (degree (Hypergraph.residual H (retainedSet H ρ ω)) v : ℝ);
            (ℙ : Measure Ω)] / c ^ 2)
        ≤ ENNReal.ofReal ((Δ : ℝ) ^ 2 / c ^ 2) := by
    intro v
    apply ENNReal.ofReal_le_ofReal
    exact div_le_div_of_nonneg_right (residualDeg_variance_le_sq ρ hΔ v) hc2.le
  have hsum : ∑ v : V, ENNReal.ofReal
          (Var[fun ω => (degree (Hypergraph.residual H (retainedSet H ρ ω)) v : ℝ);
            (ℙ : Measure Ω)] / c ^ 2)
      ≤ (Fintype.card V : ENNReal) * ENNReal.ofReal ((Δ : ℝ) ^ 2 / c ^ 2) := by
    calc
      _ ≤ ∑ _v : V, ENNReal.ofReal ((Δ : ℝ) ^ 2 / c ^ 2) :=
        Finset.sum_le_sum (fun v _ => hterm v)
      _ = (Fintype.card V : ENNReal) * ENNReal.ofReal ((Δ : ℝ) ^ 2 / c ^ 2) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hle : (ℙ : Measure Ω) {ω | ∃ v : V,
        (degree (Hypergraph.residual H (retainedSet H ρ ω)) v : ℝ)
          ≤ (degree H v : ℝ) * (1 - r * Δ * p) - c}
      ≤ (Fintype.card V : ENNReal) * ENNReal.ofReal ((Δ : ℝ) ^ 2 / c ^ 2) :=
    hprob.trans hsum
  have hfinite : (Fintype.card V : ENNReal) *
      ENNReal.ofReal ((Δ : ℝ) ^ 2 / c ^ 2) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top
  calc
    _ ≤ ((Fintype.card V : ENNReal) *
        ENNReal.ofReal ((Δ : ℝ) ^ 2 / c ^ 2)).toReal :=
      ENNReal.toReal_mono hfinite hle
    _ = (Fintype.card V : ℝ) * ((Δ : ℝ) ^ 2 / c ^ 2) := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_natCast,
        ENNReal.toReal_ofReal (by positivity)]
    _ = (Fintype.card V : ℝ) * (Δ : ℝ) ^ 2 / c ^ 2 := by ring

end Nibble

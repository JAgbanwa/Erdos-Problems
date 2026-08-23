/-
# Nibble — the safe-degree expectation, packaged as a BAND

`Nibble.safeDegree_expectation_ge` / `Nibble.safeDegree_expectation_le` give the sharp two-sided
expectation of the safe degree in terms of the exact covering rates `q_u`.  Under the standing
uniform hypotheses of a nibble round (`r`-uniform, degrees `≤ Δ`, codegrees `≤ κ`, covering rates in
`[qlo, qhi]`) they collapse to a genuine BAND around `deg(v)·(1 − (r−1)q)`:

  `deg(v)·(1 − (r−1)·qhi)  ≤  𝔼[safeDeg(v)]  ≤  deg(v)·(1 − (r−1)·qlo + (r−1)²·(Δ²p² + κp))`.

The width of the band is `(r−1)(qhi − qlo) + (r−1)²(Δ²p² + κp)`, which in the nibble regime
`p = γ/(rΔ)`, `κ ≤ μΔ` is `O(γ(μ + γ))` — SECOND order against the first-order drop `(r−1)q ≈ γ`.
That is precisely the tightness the loose brackets could not deliver.

Sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.Tight.SafeDegree
import Nibble.Prelude

open MeasureTheory ProbabilityTheory Finset Hypergraph
open scoped Classical

namespace Nibble

variable {V : Type*} [DecidableEq V] {Ω : Type*} [MeasureSpace Ω]
  [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- **The safe-degree expectation band, lower half.** -/
theorem safeDegree_expectation_band_lower {H : Finset (Finset V)} {p : ℝ} {r : ℕ} {qhi : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hr1 : 1 ≤ r)
    (hr : IsUniform H r) (hqhi : ∀ u : V, coverRate H p u ≤ qhi) (v : V) :
    (degree H v : ℝ) * (1 - ((r : ℝ) - 1) * qhi)
      ≤ ∫ ω, (safeDegree H (covered (retainedSet H ρ ω)) v : ℝ) ∂(ℙ : Measure Ω) := by
  refine le_trans ?_ (safeDegree_expectation_ge ρ hp0 hp1 v)
  have hterm : ∀ e ∈ H.filter (fun e => v ∈ e),
      1 - ((r : ℝ) - 1) * qhi ≤ 1 - ∑ u ∈ e.erase v, coverRate H p u := by
    intro e he
    have hveq : v ∈ e := (Finset.mem_filter.mp he).2
    have hcard : (e.erase v).card = r - 1 := by
      rw [Finset.card_erase_of_mem hveq, hr e (Finset.mem_filter.mp he).1]
    have hsum : ∑ u ∈ e.erase v, coverRate H p u ≤ ((e.erase v).card : ℝ) * qhi := by
      calc ∑ u ∈ e.erase v, coverRate H p u ≤ ∑ _u ∈ e.erase v, qhi :=
            Finset.sum_le_sum (fun u _ => hqhi u)
        _ = ((e.erase v).card : ℝ) * qhi := by rw [Finset.sum_const, nsmul_eq_mul]
    have hcast : ((e.erase v).card : ℝ) = (r : ℝ) - 1 := by
      rw [hcard]
      have : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by
        have : (1 : ℕ) ≤ r := hr1
        push_cast [Nat.cast_sub this]
        ring
      exact this
    rw [hcast] at hsum
    linarith only [hsum]
  calc (degree H v : ℝ) * (1 - ((r : ℝ) - 1) * qhi)
      = ∑ _e ∈ H.filter (fun e => v ∈ e), (1 - ((r : ℝ) - 1) * qhi) := by
        rw [Finset.sum_const, nsmul_eq_mul]; rfl
    _ ≤ ∑ e ∈ H.filter (fun e => v ∈ e), (1 - ∑ u ∈ e.erase v, coverRate H p u) :=
        Finset.sum_le_sum hterm

/-- **The safe-degree expectation band, upper half.** -/
theorem safeDegree_expectation_band_upper {H : Finset (Finset V)} {p : ℝ} {r Δ κ : ℕ} {qlo : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hr1 : 1 ≤ r)
    (hr : IsUniform H r) (hqlo : ∀ u : V, qlo ≤ coverRate H p u)
    (hΔ : ∀ x, degree H x ≤ Δ) (hκ : ∀ x y : V, x ≠ y → codegree H x y ≤ κ) (v : V) :
    ∫ ω, (safeDegree H (covered (retainedSet H ρ ω)) v : ℝ) ∂(ℙ : Measure Ω)
      ≤ (degree H v : ℝ) * (1 - ((r : ℝ) - 1) * qlo
          + ((r : ℝ) - 1) ^ 2 * ((Δ : ℝ) ^ 2 * p ^ 2 + (κ : ℝ) * p)) := by
  refine le_trans (safeDegree_expectation_le ρ hp0 hp1 v) ?_
  have hX0 : (0 : ℝ) ≤ (Δ : ℝ) ^ 2 * p ^ 2 + (κ : ℝ) * p := by positivity
  have hterm : ∀ e ∈ H.filter (fun e => v ∈ e),
      (1 - ∑ u ∈ e.erase v, coverRate H p u
        + ∑ u ∈ e.erase v, ∑ u' ∈ (e.erase v).erase u,
            ((degree H u : ℝ) * (degree H u' : ℝ) * p ^ 2 + (codegree H u u' : ℝ) * p))
      ≤ 1 - ((r : ℝ) - 1) * qlo
          + ((r : ℝ) - 1) ^ 2 * ((Δ : ℝ) ^ 2 * p ^ 2 + (κ : ℝ) * p) := by
    intro e he
    have hveq : v ∈ e := (Finset.mem_filter.mp he).2
    have hcard : (e.erase v).card = r - 1 := by
      rw [Finset.card_erase_of_mem hveq, hr e (Finset.mem_filter.mp he).1]
    have hcast : ((e.erase v).card : ℝ) = (r : ℝ) - 1 := by
      rw [hcard]
      have h1 : (1 : ℕ) ≤ r := hr1
      push_cast [Nat.cast_sub h1]
      ring
    have hr1R : (0 : ℝ) ≤ (r : ℝ) - 1 := by
      have : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
      linarith only [this]
    -- lower bound for the first-order term
    have hlow : ((r : ℝ) - 1) * qlo ≤ ∑ u ∈ e.erase v, coverRate H p u := by
      calc ((r : ℝ) - 1) * qlo = ((e.erase v).card : ℝ) * qlo := by rw [hcast]
        _ = ∑ _u ∈ e.erase v, qlo := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ u ∈ e.erase v, coverRate H p u := Finset.sum_le_sum (fun u _ => hqlo u)
    -- upper bound for the second-order term
    have hpair : ∀ u ∈ e.erase v, ∑ u' ∈ (e.erase v).erase u,
        ((degree H u : ℝ) * (degree H u' : ℝ) * p ^ 2 + (codegree H u u' : ℝ) * p)
        ≤ ((r : ℝ) - 1) * ((Δ : ℝ) ^ 2 * p ^ 2 + (κ : ℝ) * p) := by
      intro u hu
      have hstep : ∀ u' ∈ (e.erase v).erase u,
          ((degree H u : ℝ) * (degree H u' : ℝ) * p ^ 2 + (codegree H u u' : ℝ) * p)
          ≤ (Δ : ℝ) ^ 2 * p ^ 2 + (κ : ℝ) * p := by
        intro u' hu'
        have hne : u ≠ u' := fun h => (Finset.mem_erase.mp hu').1 h.symm
        have hdu : (degree H u : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast hΔ u
        have hdu' : (degree H u' : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast hΔ u'
        have hcod : (codegree H u u' : ℝ) ≤ (κ : ℝ) := by exact_mod_cast hκ u u' hne
        have h1 : (degree H u : ℝ) * (degree H u' : ℝ) ≤ (Δ : ℝ) ^ 2 := by
          nlinarith [Nat.cast_nonneg (α := ℝ) (degree H u), Nat.cast_nonneg (α := ℝ) (degree H u')]
        nlinarith [sq_nonneg p, hp0]
      calc ∑ u' ∈ (e.erase v).erase u,
            ((degree H u : ℝ) * (degree H u' : ℝ) * p ^ 2 + (codegree H u u' : ℝ) * p)
          ≤ ∑ _u' ∈ (e.erase v).erase u, ((Δ : ℝ) ^ 2 * p ^ 2 + (κ : ℝ) * p) :=
            Finset.sum_le_sum hstep
        _ = (((e.erase v).erase u).card : ℝ) * ((Δ : ℝ) ^ 2 * p ^ 2 + (κ : ℝ) * p) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ((r : ℝ) - 1) * ((Δ : ℝ) ^ 2 * p ^ 2 + (κ : ℝ) * p) := by
            refine mul_le_mul_of_nonneg_right ?_ hX0
            have : (((e.erase v).erase u).card : ℝ) ≤ ((e.erase v).card : ℝ) := by
              exact_mod_cast Finset.card_le_card (Finset.erase_subset _ _)
            rw [hcast] at this
            exact this
    have hsum2 : ∑ u ∈ e.erase v, ∑ u' ∈ (e.erase v).erase u,
        ((degree H u : ℝ) * (degree H u' : ℝ) * p ^ 2 + (codegree H u u' : ℝ) * p)
        ≤ ((r : ℝ) - 1) ^ 2 * ((Δ : ℝ) ^ 2 * p ^ 2 + (κ : ℝ) * p) := by
      calc ∑ u ∈ e.erase v, ∑ u' ∈ (e.erase v).erase u,
            ((degree H u : ℝ) * (degree H u' : ℝ) * p ^ 2 + (codegree H u u' : ℝ) * p)
          ≤ ∑ _u ∈ e.erase v, ((r : ℝ) - 1) * ((Δ : ℝ) ^ 2 * p ^ 2 + (κ : ℝ) * p) :=
            Finset.sum_le_sum hpair
        _ = ((e.erase v).card : ℝ) * (((r : ℝ) - 1) * ((Δ : ℝ) ^ 2 * p ^ 2 + (κ : ℝ) * p)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ = ((r : ℝ) - 1) ^ 2 * ((Δ : ℝ) ^ 2 * p ^ 2 + (κ : ℝ) * p) := by
            rw [hcast]; ring
    linarith only [hlow, hsum2]
  calc ∑ e ∈ H.filter (fun e => v ∈ e),
        (1 - ∑ u ∈ e.erase v, coverRate H p u
          + ∑ u ∈ e.erase v, ∑ u' ∈ (e.erase v).erase u,
              ((degree H u : ℝ) * (degree H u' : ℝ) * p ^ 2 + (codegree H u u' : ℝ) * p))
      ≤ ∑ _e ∈ H.filter (fun e => v ∈ e),
          (1 - ((r : ℝ) - 1) * qlo
            + ((r : ℝ) - 1) ^ 2 * ((Δ : ℝ) ^ 2 * p ^ 2 + (κ : ℝ) * p)) :=
        Finset.sum_le_sum hterm
    _ = (degree H v : ℝ) * (1 - ((r : ℝ) - 1) * qlo
          + ((r : ℝ) - 1) ^ 2 * ((Δ : ℝ) ^ 2 * p ^ 2 + (κ : ℝ) * p)) := by
        rw [Finset.sum_const, nsmul_eq_mul]; rfl

end Nibble

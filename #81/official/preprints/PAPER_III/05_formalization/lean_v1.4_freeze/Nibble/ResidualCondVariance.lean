/-
# Nibble — the isolated crux of the residual concentration: conditional second moment (I)

The nibble concentration engine reduces to a SINGLE abstract probability lemma. This file names that
obligation and discharges the residual-specific part against it (sorry-free).

* `BernoulliPiDoobCondVarBound` — the crux: on a finite Bernoulli product, a Doob increment's conditional
  second moment is `≤ p·C²` under a `C`-bounded coordinate difference. Purely abstract; no nibble content.
* `residualDegReindexed_condSecondMoment_le` — the residual `(I)`, proven FROM the obligation via the sharp
  coordinate oscillation `residualDegReindexed_boundedDiff`. Feeds `doob_increment_hasCondSubgammaMGF_of_secondMoment`.

Discharging `BernoulliPiDoobCondVarBound` completes the entire nibble concentration engine. Axiom-clean.
-/

import Nibble.ResidualFreedmanTail
import Nibble.McDiarmidMarginal
import Nibble.Prelude

open MeasureTheory ProbabilityTheory Finset Hypergraph

namespace Nibble

/-- **The isolated crux obligation** (the single remaining analytic step of the nibble concentration
engine): on a finite Bernoulli product `Measure.pi (bernoulliConfigMeasure p)` over `Fin n → Bool`, the
conditional second moment of a Doob increment is `≤ p·C²` whenever toggling the newly exposed coordinate
changes the observable by at most `C`. A purely abstract product-measure / Doob-martingale statement
(no nibble specifics), plausibly Mathlib-worthy. -/
def BernoulliPiDoobCondVarBound : Prop :=
  ∀ {n : ℕ} (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (f : (Fin n → Bool) → ℝ) (_hf : StronglyMeasurable f)
    (_hfi : Integrable f (Measure.pi (fun _ : Fin n => bernoulliConfigMeasure p hp0 hp1)))
    (k : ℕ) (hk : k < n) (C : ℝ)
    (_hbd : ∀ (ω ω' : Fin n → Bool),
      (∀ i, i ≠ (⟨k, hk⟩ : Fin n) → ω i = ω' i) → |f ω - f ω'| ≤ C),
    ∀ᵐ ω ∂(Measure.pi (fun _ : Fin n => bernoulliConfigMeasure p hp0 hp1)).trim (exposureσ_le k),
      ∫ x, (doob (Measure.pi (fun _ : Fin n => bernoulliConfigMeasure p hp0 hp1)) f (k + 1) x
              - doob (Measure.pi (fun _ : Fin n => bernoulliConfigMeasure p hp0 hp1)) f k x) ^ 2
          ∂condExpKernel (Measure.pi (fun _ : Fin n => bernoulliConfigMeasure p hp0 hp1))
            (exposureσ k) ω ≤ p * C ^ 2

/-- **Residual conditional second moment `(I)` — reduced to the crux obligation.** The residual-specific
part is fully discharged: given `BernoulliPiDoobCondVarBound`, the reindexed residual-degree observable's
Doob increment has conditional second moment `≤ p·neighborCoef²`, by its sharp coordinate oscillation. -/
theorem residualDegReindexed_condSecondMoment_le
    (hObl : BernoulliPiDoobCondVarBound)
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : Finset (Finset V)) (v : V)
    (e : Fin (Fintype.card (Finset V)) ≃ Finset V)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (k : ℕ) (hk : k < Fintype.card (Finset V)) :
    let μ := Measure.pi (fun _ : Fin (Fintype.card (Finset V)) =>
      bernoulliConfigMeasure p hp0 hp1)
    let f := residualDegReindexed H v e
    ∀ᵐ ω ∂μ.trim (exposureσ_le k),
      ∫ x, (doob μ f (k + 1) x - doob μ f k x) ^ 2
        ∂condExpKernel μ (exposureσ k) ω
      ≤ p * (neighborCoef H v (e ⟨k, hk⟩) : ℝ) ^ 2 := by
  apply hObl p hp0 hp1
      (residualDegReindexed H v e) (Measurable.stronglyMeasurable Measurable.of_discrete)
      Integrable.of_finite k hk (neighborCoef H v (e ⟨k, hk⟩) : ℝ)
  intro ω ω' hagree
  exact residualDegReindexed_boundedDiff H v e ⟨k, hk⟩ ω ω' hagree

end Nibble

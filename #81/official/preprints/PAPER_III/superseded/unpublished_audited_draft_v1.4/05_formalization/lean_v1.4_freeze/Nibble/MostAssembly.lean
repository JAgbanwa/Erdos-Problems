/-
# Nibble — outer assembly toward `NibbleTheoremMost` (hence `NibbleTheorem`)

Standalone, Mathlib-only. This is the OUTER LOOP that glues the (already sorry-free) per-round
bricks into the majority T3 interface `NibbleTheoremMost`. By `NibbleTheoremMost.nibbleTheorem`
(RegularMost.lean) this discharges `NibbleTheorem`, the sole open input of the Yuster → AX1 chain
and of the Haxell–Rödl bridge `approx_of_fractional` used by AX2's Part B.

## What is already proved (bricks to reuse — cite by name)
* `nibbleStrategy` (NibbleStrategy.lean): the fixed DETERMINISTIC retention strategy `R`.
* `nibbleStrategy_subset` : `R H' ⊆ H'`  (the `hR` hypothesis of the discharge lemmas).
* `nibbleStrategy_spec` : on a valid (uniform-`r`, degree ≤ `Δ`) input, ONE round both
    (a) preserves near-regularity DETERMINISTICALLY:
        `(degree H' v) * (1 - r*Δ*p) - c < degree (residual H' (R H')) v`, and
    (b) covers a definite amount:
        `H'.card * (p*(1-p)^(r*Δ)) - |V|*(|V|*Δ^2/c^2) ≤ (roundMatching (R H')).card`.
  Crucially, the probabilistic content is ALREADY discharged inside `R` (via
  `exists_good_retention'.choose`); the round-to-round invariant is now a REAL-ANALYSIS induction.
* `nibbleResidual_uniform` (Iteration.lean): the residual stays `r`-uniform.
* `degree_nibbleResidual_le` (InvariantDegree.lean): residual degrees are monotone ≤ `Δ`.
* `exists_matching_of_oracle_lt` (Discharge.lean): the bounded-`T` oracle `horacle` ⇒ a matching
    covering `≥ (1-β)*(|V|/r)`. Needs `T` with `lam^T ≤ β`.
* `NibbleTheoremMost.nibbleTheorem` (RegularMost.lean): `NibbleTheoremMost ⇒ NibbleTheorem`.
* geometric convergence `exists_uncovered_below` / `uncovered_below_lt` (Convergence.lean).

## Remaining core (the induction to fill / delegate)
The single remaining obligation is the ORACLE: for the strategy `R = nibbleStrategy` and suitable
parameters `(Δ, p, c, lam, T)`, every round `k < T` covers a `(1-lam)`-fraction of the still-
uncovered vertices:
  `(1-lam) * (|V| - support(nibbleMatching R H k).card) ≤ support(roundMatching (R (nibbleResidual R H k))).card`.
This is obtained from `nibbleStrategy_spec` by the deterministic degree-decay invariant
(chaining (a) over `k` rounds gives a lower bound on residual degrees, hence on the residual EDGE
count `H_k.card` in terms of the uncovered-vertex count via `r`-uniformity), plus the
`NearlyRegularMost` exceptional set `Exc` absorbed into the slack `β`.
## STATUS UPDATE (2026-08-05): this parameter obligation is FALSE

`NibbleParamsExistThreshold` below cannot be discharged: it is refuted in
`Nibble.ParamsCoreRefutation` (`not_nibbleParamsExistThreshold`).  The reason is structural, not a
matter of calibration — see `Nibble.FreedmanParamsObstruction` and `OUTER_LAYER_OBSTRUCTIONS.md`:
the crux asks each of the `T` rounds to cover a `(1-lam)`-fraction of the WHOLE vertex set, while
the total gain available to a fixed-parameter nibble is capped by `(1-μ)d/(rΔ) ≤ 1/r`
(`Nibble.total_gain_le`).  The statements below remain valid implications; only their hypothesis is
unsatisfiable.
-/
import Nibble.NibbleStrategy
import Nibble.Discharge
import Nibble.RegularMost
import Nibble.Convergence
import Nibble.Iteration
import Nibble.InvariantDegree
import Nibble.DegreeDecay

open Hypergraph Finset

namespace Nibble

/-- **Elementary rounds bound (LOCAL, proved).** For `0 ≤ lam < 1` and target `β > 0` there is a
round count `T` with `lam ^ T ≤ β` — the `hTβ` input of `exists_matching_of_oracle_lt`. -/
theorem exists_rounds_for_target {lam β : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam < 1) (hβ : 0 < β) :
    ∃ T : ℕ, lam ^ T ≤ β := by
  obtain ⟨T, hT⟩ := exists_pow_lt_of_lt_one hβ hlam1
  exact ⟨T, le_of_lt hT⟩

/-- Parameter existence, asymptotic threshold form.  This is the external real-analysis obligation
for the legacy Chebyshev outer assembly route. -/
abbrev NibbleParamsExistThreshold : Prop :=
  ∀ (r : ℕ), 2 ≤ r → ∀ (β : ℝ), 0 < β →
    ∃ μ : ℝ, 0 < μ ∧ ∃ η : ℝ, 0 < η ∧ ∃ d₀ : ℝ, 0 < d₀ ∧
      ∀ {V : Type} [Fintype V] [DecidableEq V] (H : Finset (Finset V)) (d : ℝ), 0 < d → d₀ ≤ d →
        IsUniform H r → NearlyRegularMost H d μ η → CodegreeBounded H (μ * d) →
        ∃ (Δ : ℕ) (p c lam : ℝ) (T : ℕ),
          0 ≤ p ∧ p ≤ 1 ∧ 0 < c ∧ (Fintype.card V : ℝ) * (Δ : ℝ) ^ 2 < c ^ 2 ∧
          0 ≤ 1 - (r : ℝ) * Δ * p ∧ lam ≤ 1 ∧ 0 ≤ lam ∧ (∀ x, degree H x ≤ Δ) ∧ lam ^ T ≤ β ∧
          (∀ k, k < T →
            0 ≤ ((1 - μ) * d * (1 - (r : ℝ) * Δ * p) ^ k
                    - c * (∑ i ∈ Finset.range k, (1 - (r : ℝ) * Δ * p) ^ i))
                  * (p * (1 - p) ^ (r * Δ))
            ∧ (1 - lam) * (Fintype.card V : ℝ)
                ≤ (1 - η) * (Fintype.card V : ℝ)
                    * (((1 - μ) * d * (1 - (r : ℝ) * Δ * p) ^ k
                          - c * (∑ i ∈ Finset.range k, (1 - (r : ℝ) * Δ * p) ^ i))
                        * (p * (1 - p) ^ (r * Δ)))
                  - (r : ℝ) * ((Fintype.card V : ℝ)
                      * ((Fintype.card V : ℝ) * (Δ : ℝ) ^ 2 / c ^ 2)))

/-- **`NibbleTheoremMost` — assembled from explicit parameters.** Combines
the isolated parameter existence with the proved `oracle_of_crux` (⇒ the covering oracle) and the
proved geometric discharge `exists_matching_of_oracle_lt`. -/
theorem nibbleTheoremMost_holds_of_params
    (hParams : NibbleParamsExistThreshold) : NibbleTheoremMost := by
  intro r hr β hβ
  obtain ⟨μ, hμ, η, hη, d₀, hd₀, hP⟩ := hParams r hr β hβ
  refine ⟨μ, hμ, η, hη, d₀, hd₀, ?_⟩
  intro V _ _ H d hd hd0 huni hreg hcodeg
  obtain ⟨Δ, p, c, lam, T, hp0, hp1, hc, hcΔ, hq, hlam1, hlam0, hdeg0, hTβ, hcrux⟩ :=
    hP H d hd hd0 huni hreg hcodeg
  have hr1 : 1 ≤ r := le_trans (by norm_num) hr
  exact exists_matching_of_oracle_lt
    (nibbleStrategy_subset r Δ p c hp0 hp1 hr1 hc hcΔ) huni hr1 hlam0 hβ T hTβ
    (oracle_of_crux r Δ p c d μ η lam T hp0 hp1 hr1 hc hcΔ hq hlam1 H huni hdeg0 hreg hcrux)

/-- **`NibbleTheorem` from explicit parameters**, via the majority form. -/
theorem nibbleTheorem_holds_of_params
    (hParams : NibbleParamsExistThreshold) : NibbleTheorem :=
  (nibbleTheoremMost_holds_of_params hParams).nibbleTheorem

end Nibble

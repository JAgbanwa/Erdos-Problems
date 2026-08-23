/-
# Nibble — one good round : cover many vertices while avoiding a bad event

Standalone, Mathlib-only. The probabilistic heart of one nibble round: combining the expected
matching-size lower bound (`matchingSize_expectation_lower`) with the abstract good-event selector
(`exists_notin_bad_ge`), there is a single outcome `ω` that simultaneously
* avoids a prescribed measurable "bad" event `Bad` of probability `< 1` (e.g. the regularity-failure
  event of `round_regularity_failure`), and
* whose round matching has at least `|H|·p·(1-p)^{rΔ} − |V|·P(Bad)` edges.

Taking `P(Bad)` small (it is `≤ ∑Var/c²`, made small by parameter choice) this keeps the coverage a
definite fraction while preserving regularity — exactly the per-round input the nibble iteration
(`nibble_matching_card_of_oracle`) consumes.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.Basic
import Nibble.Greedy
import Nibble.Round
import Nibble.Covered
import Nibble.CoveredExpectation
import Nibble.GoodEvent
import Nibble.Prelude

open MeasureTheory ProbabilityTheory Finset Hypergraph
open scoped Classical

namespace Nibble

variable {V : Type*} [DecidableEq V] [Fintype V] {Ω : Type*} [MeasureSpace Ω]
  [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- **One good round.** There is an outcome `ω ∉ Bad` whose round matching has at least
`|H|·p·(1-p)^{rΔ} − |V|·P(Bad)` edges. (`f` = round matching size, `m` = its expectation lower
bound, `M` = `|V|` bounds the matching size; apply `exists_notin_bad_ge`.) -/
theorem exists_covering_avoiding_bad {H : Finset (Finset V)} {p : ℝ} {r Δ : ℕ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hr1 : 1 ≤ r)
    (hr : IsUniform H r) (hΔ : ∀ x, degree H x ≤ Δ)
    {Bad : Set Ω} (hBadMeas : MeasurableSet Bad) (hBad1 : (ℙ Bad).toReal < 1) :
    ∃ ω, ω ∉ Bad ∧
      (H.card : ℝ) * (p * (1 - p) ^ (r * Δ)) - (Fintype.card V : ℝ) * (ℙ Bad).toReal
        ≤ ((roundMatching (retainedSet H ρ ω)).card : ℝ) := by
  have hbound : ∀ ω, ((roundMatching (retainedSet H ρ ω)).card : ℝ) ≤ (Fintype.card V : ℝ) := by
    intro ω
    have hRr : IsUniform (retainedSet H ρ ω) r := fun e he => hr e (Finset.filter_subset _ _ he)
    have hnat : (roundMatching (retainedSet H ρ ω)).card ≤ Fintype.card V := by
      calc (roundMatching (retainedSet H ρ ω)).card
            ≤ r * (roundMatching (retainedSet H ρ ω)).card :=
              Nat.le_mul_of_pos_left _ (by omega)
        _ = (support (roundMatching (retainedSet H ρ ω))).card :=
              (matching_support_card hRr (roundMatching_isMatching (Finset.Subset.refl _))).symm
        _ ≤ Fintype.card V := Finset.card_le_univ _
    exact_mod_cast hnat
  exact exists_notin_bad_ge
    (integrable_matchingSize ρ)
    (fun ω => by positivity)
    hbound hBadMeas hBad1
    (matchingSize_expectation_lower ρ hp0 hp1 hr hΔ)

end Nibble

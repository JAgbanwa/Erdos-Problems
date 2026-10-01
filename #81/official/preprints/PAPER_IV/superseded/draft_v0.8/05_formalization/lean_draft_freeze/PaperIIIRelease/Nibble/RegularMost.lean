/-
# Nibble — near-regularity for the majority of vertices, and the adapted nibble interface

Standalone, Mathlib-only. The Szemerédi+counting reconstruction of Y1c (`triangleHypergraph_degree_
lower_of_capture` + `card_capturing_lower`) delivers near-regularity for *most* vertices — the
non-capturing exceptional set is small but nonempty. The strict `NearlyRegular` (ALL vertices) cannot
absorb it. This file introduces the majority notion `NearlyRegularMost H d μ η` (regular outside an
`η`-fraction exceptional set) and the adapted nibble interface `NibbleTheoremMost` that consumes it.

* `NearlyRegularMost` — near-`d`-regular outside an exceptional set of size `≤ η|V|`.
* `NearlyRegular.nearlyRegularMost` — strict regularity is the `η`-majority notion with empty `Exc`.
* `NibbleTheoremMost` — the T3 interface consuming `NearlyRegularMost`.
* `NibbleTheoremMost.nibbleTheorem` — the majority interface is a strengthening: it implies the
  strict `NibbleTheorem` (so discharging it suffices for the whole Layer E chain).

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.Regular
import Nibble.Interface
import Mathlib.Tactic.Bound

open Finset

namespace Hypergraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Majority near-regularity.** `H` is `(1±μ)`-nearly `d`-regular outside an exceptional set of
vertices of size at most `η·|V|`. Recovers `NearlyRegular` when the exceptional set is empty. -/
def NearlyRegularMost (H : Finset (Finset V)) (d μ η : ℝ) : Prop :=
  ∃ Exc : Finset V, (Exc.card : ℝ) ≤ η * (Fintype.card V : ℝ) ∧
    ∀ v ∉ Exc, (1 - μ) * d ≤ (degree H v : ℝ) ∧ (degree H v : ℝ) ≤ (1 + μ) * d

/-- Strict near-regularity is majority near-regularity with an empty exceptional set (any `η ≥ 0`). -/
theorem NearlyRegular.nearlyRegularMost {H : Finset (Finset V)} {d μ η : ℝ} (hη : 0 ≤ η)
    (h : NearlyRegular H d μ) : NearlyRegularMost H d μ η :=
  ⟨∅, by rw [Finset.card_empty, Nat.cast_zero]; exact mul_nonneg hη (Nat.cast_nonneg _),
    fun v _ => h v⟩

end Hypergraph

namespace Nibble

open Hypergraph

/-- **T3 interface (majority form).** For `r ≥ 2` and target `β > 0`, there are tolerances `μ, η > 0`
such that every `r`-uniform hypergraph that is `(1±μ)`-nearly `d`-regular OUTSIDE an `η`-fraction
exceptional set, with codegree `≤ μd`, has a matching covering `≥ (1-β)·(|V|/r)`. The nibble absorbs
the small exceptional set into the target slack `β`. -/
def NibbleTheoremMost : Prop :=
  ∀ (r : ℕ), 2 ≤ r → ∀ (β : ℝ), 0 < β → ∃ μ : ℝ, 0 < μ ∧ ∃ η : ℝ, 0 < η ∧ ∃ d₀ : ℝ, 0 < d₀ ∧
    ∀ {V : Type} [Fintype V] [DecidableEq V] (H : Finset (Finset V)) (d : ℝ), 0 < d → d₀ ≤ d →
      IsUniform H r → NearlyRegularMost H d μ η → CodegreeBounded H (μ * d) →
      ∃ M : Finset (Finset V), IsMatching H M ∧
        (1 - β) * ((Fintype.card V : ℝ) / r) ≤ (M.card : ℝ)

/-- **T3 interface with global degree ceiling.** This is the form consumed by the corrected
Freedman assembly: in addition to majority near-regularity and codegree boundedness, every vertex has
degree at most `(1+μ)d`.  The ceiling is the ② global-degree input in the AX1 chain. -/
def NibbleTheoremMostCeil : Prop :=
  ∀ (r : ℕ), 2 ≤ r → ∀ (β : ℝ), 0 < β → ∃ μ : ℝ, 0 < μ ∧ ∃ η : ℝ, 0 < η ∧ ∃ d₀ : ℝ, 0 < d₀ ∧
    ∀ {V : Type} [Fintype V] [DecidableEq V] (H : Finset (Finset V)) (d : ℝ), 0 < d → d₀ ≤ d →
      IsUniform H r → NearlyRegularMost H d μ η → CodegreeBounded H (μ * d) →
      (∀ x : V, (degree H x : ℝ) ≤ (1 + μ) * d) →
      ∃ M : Finset (Finset V), IsMatching H M ∧
        (1 - β) * ((Fintype.card V : ℝ) / r) ≤ (M.card : ℝ)

/-- **T3 interface with global ceiling and polynomial size control.** The Freedman parameter
selection needs a uniform way to make the all-vertices bad-event probability small.  The abstract
hypergraph hypotheses do not bound `|V|` in terms of the regular degree scale `d`; the triangle
hypergraph application does.  This interface records that missing input explicitly. -/
def NibbleTheoremMostCeilSized : Prop :=
  ∀ (r : ℕ), 2 ≤ r → ∀ (β : ℝ), 0 < β → ∃ μ : ℝ, 0 < μ ∧ ∃ η : ℝ, 0 < η ∧
    ∃ d₀ : ℝ, 0 < d₀ ∧ ∃ K : ℝ, 0 < K ∧
    ∀ {V : Type} [Fintype V] [DecidableEq V] (H : Finset (Finset V)) (d : ℝ), 0 < d → d₀ ≤ d →
      IsUniform H r → NearlyRegularMost H d μ η → CodegreeBounded H (μ * d) →
      (∀ x : V, (degree H x : ℝ) ≤ (1 + μ) * d) →
      (Fintype.card V : ℝ) ≤ K * d ^ 2 →
      ∃ M : Finset (Finset V), IsMatching H M ∧
        (1 - β) * ((Fintype.card V : ℝ) / r) ≤ (M.card : ℝ)

/-- **The majority interface implies the strict one.** Since strict `NearlyRegular` is a special case
of `NearlyRegularMost` (empty exceptional set), `NibbleTheoremMost` implies `NibbleTheorem` — so
discharging the majority form suffices for the entire Layer E chain that consumes `NibbleTheorem`. -/
theorem NibbleTheoremMost.nibbleTheorem (h : NibbleTheoremMost) : NibbleTheorem := by
  intro r hr β hβ
  obtain ⟨μ, hμ, η, hη, d₀, hd₀, hmain⟩ := h r hr β hβ
  refine ⟨μ, hμ, d₀, hd₀, ?_⟩
  intro V _ _ H d hd hd0 hunif hreg hcod
  exact hmain H d hd hd0 hunif (hreg.nearlyRegularMost (le_of_lt hη)) hcod

end Nibble

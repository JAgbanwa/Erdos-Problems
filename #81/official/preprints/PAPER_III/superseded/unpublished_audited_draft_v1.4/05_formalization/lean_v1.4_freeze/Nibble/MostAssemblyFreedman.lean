/-
# Nibble — outer assembly via the Freedman strategy

Parallel to `MostAssembly.lean`, but with the Freedman one-round strategy and exponential bad-event
penalty. This isolates the remaining work to a single parameter-existence atom whose hypotheses match
the new concentration route.
-/
import Nibble.Discharge
import Nibble.RegularMost
import Nibble.DegreeDecayFreedman

open Hypergraph Finset

namespace Nibble

/-- Convert a real global degree ceiling into the integer ceiling consumed by the nibble strategy. -/
theorem degree_le_natCeil_of_real_bound {V : Type} [Fintype V] [DecidableEq V]
    (H : Finset (Finset V)) (A : ℝ) (hceil : ∀ x : V, (degree H x : ℝ) ≤ A) :
    ∀ x : V, degree H x ≤ Nat.ceil A := by
  intro x
  exact_mod_cast (hceil x).trans (Nat.le_ceil A)

/-- Positivity of the integer ceiling in the positive real regime. -/
theorem natCeil_pos_of_pos {A : ℝ} (hA : 0 < A) : 0 < Nat.ceil A :=
  Nat.ceil_pos.mpr hA

/-- The remaining pure parameter core for the sized Freedman route.  This names the only
non-mechanical residue: choosing `Δ,p,c,lam,T` so that the Bernstein/Freedman bad-event term is small
and the round-covering inequality still has enough slack. -/
def FreedmanSizedParameterCore (r : ℕ) (β μ η K : ℝ) : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (H : Finset (Finset V)) (d : ℝ),
    0 < d →
    IsUniform H r →
    NearlyRegularMost H d μ η →
    CodegreeBounded H (μ * d) →
    (∀ x : V, (degree H x : ℝ) ≤ (1 + μ) * d) →
    (Fintype.card V : ℝ) ≤ K * d ^ 2 →
    ∃ (Δ : ℕ) (p c lam : ℝ) (T : ℕ),
      0 ≤ p ∧ p ≤ 1 ∧ 0 < p ∧ 0 < Δ ∧ 0 < c ∧
      0 ≤ 1 - (r : ℝ) * Δ * p ∧ lam ≤ 1 ∧ 0 ≤ lam ∧ (∀ x, degree H x ≤ Δ) ∧
      lam ^ T ≤ β ∧
      (∀ H' : Finset (Finset V), IsUniform H' r →
        (∀ x, degree H' x ≤ Δ) →
        (Fintype.card V : ℝ) * (2 * Real.exp (-c ^ 2 / (2 * ((Δ : ℝ) ^ 2 *
          ((r : ℝ) * Δ * p) + (Δ : ℝ) / 3 * c)))) < 1) ∧
      (∀ k, k < T →
        0 ≤ ((1 - μ) * d * (1 - (r : ℝ) * Δ * p) ^ k
                - c * (∑ i ∈ Finset.range k,
                    (1 - (r : ℝ) * Δ * p) ^ i))
              * (p * (1 - p) ^ (r * Δ))
        ∧ (1 - lam) * (Fintype.card V : ℝ)
            ≤ (1 - η) * (Fintype.card V : ℝ)
                * (((1 - μ) * d * (1 - (r : ℝ) * Δ * p) ^ k
                      - c * (∑ i ∈ Finset.range k,
                          (1 - (r : ℝ) * Δ * p) ^ i))
                    * (p * (1 - p) ^ (r * Δ)))
              - (r : ℝ) * freedmanPenalty V r Δ p c)

/-- Threshold version of `FreedmanSizedParameterCore`. This is the asymptotic parameter obligation
actually consumed by the outer nibble theorem: the real-analysis parameter choice only has to work once
the density scale has crossed the selected threshold `d₀`. -/
def FreedmanSizedThresholdParameterCore (r : ℕ) (β μ η d₀ K : ℝ) : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (H : Finset (Finset V)) (d : ℝ),
    0 < d →
    d₀ ≤ d →
    IsUniform H r →
    NearlyRegularMost H d μ η →
    CodegreeBounded H (μ * d) →
    (∀ x : V, (degree H x : ℝ) ≤ (1 + μ) * d) →
    (Fintype.card V : ℝ) ≤ K * d ^ 2 →
    ∃ (Δ : ℕ) (p c lam : ℝ) (T : ℕ),
      0 ≤ p ∧ p ≤ 1 ∧ 0 < p ∧ 0 < Δ ∧ 0 < c ∧
      0 ≤ 1 - (r : ℝ) * Δ * p ∧ lam ≤ 1 ∧ 0 ≤ lam ∧ (∀ x, degree H x ≤ Δ) ∧
      lam ^ T ≤ β ∧
      (∀ H' : Finset (Finset V), IsUniform H' r →
        (∀ x, degree H' x ≤ Δ) →
        (Fintype.card V : ℝ) * (2 * Real.exp (-c ^ 2 / (2 * ((Δ : ℝ) ^ 2 *
          ((r : ℝ) * Δ * p) + (Δ : ℝ) / 3 * c)))) < 1) ∧
      (∀ k, k < T →
        0 ≤ ((1 - μ) * d * (1 - (r : ℝ) * Δ * p) ^ k
                - c * (∑ i ∈ Finset.range k,
                    (1 - (r : ℝ) * Δ * p) ^ i))
              * (p * (1 - p) ^ (r * Δ))
        ∧ (1 - lam) * (Fintype.card V : ℝ)
            ≤ (1 - η) * (Fintype.card V : ℝ)
                * (((1 - μ) * d * (1 - (r : ℝ) * Δ * p) ^ k
                      - c * (∑ i ∈ Finset.range k,
                          (1 - (r : ℝ) * Δ * p) ^ i))
                    * (p * (1 - p) ^ (r * Δ)))
              - (r : ℝ) * freedmanPenalty V r Δ p c)

/-- Parameter core after the global degree ceiling has been converted to the canonical integer
`Δ = Nat.ceil ((1 + μ) * d)`. This removes one mechanical choice from the remaining real-analysis
problem: the residual work is only to select `p,c,lam,T` for that ceiling. -/
def FreedmanCeilThresholdParameterCore (r : ℕ) (β μ η d₀ K : ℝ) : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (H : Finset (Finset V)) (d : ℝ),
    0 < d →
    d₀ ≤ d →
    IsUniform H r →
    NearlyRegularMost H d μ η →
    CodegreeBounded H (μ * d) →
    (∀ x : V, (degree H x : ℝ) ≤ (1 + μ) * d) →
    (Fintype.card V : ℝ) ≤ K * d ^ 2 →
    ∃ (p c lam : ℝ) (T : ℕ),
      0 ≤ p ∧ p ≤ 1 ∧ 0 < p ∧ 0 < c ∧
      0 ≤ 1 - (r : ℝ) * Nat.ceil ((1 + μ) * d) * p ∧
      lam ≤ 1 ∧ 0 ≤ lam ∧ lam ^ T ≤ β ∧
      (∀ H' : Finset (Finset V), IsUniform H' r →
        (∀ x, degree H' x ≤ Nat.ceil ((1 + μ) * d)) →
        (Fintype.card V : ℝ) * (2 * Real.exp (-c ^ 2 /
          (2 * ((Nat.ceil ((1 + μ) * d) : ℝ) ^ 2 *
            ((r : ℝ) * Nat.ceil ((1 + μ) * d) * p)
            + (Nat.ceil ((1 + μ) * d) : ℝ) / 3 * c)))) < 1) ∧
      (∀ k, k < T →
        0 ≤ ((1 - μ) * d *
                (1 - (r : ℝ) * Nat.ceil ((1 + μ) * d) * p) ^ k
              - c * (∑ i ∈ Finset.range k,
                  (1 - (r : ℝ) * Nat.ceil ((1 + μ) * d) * p) ^ i))
              * (p * (1 - p) ^ (r * Nat.ceil ((1 + μ) * d)))
        ∧ (1 - lam) * (Fintype.card V : ℝ)
            ≤ (1 - η) * (Fintype.card V : ℝ)
                * (((1 - μ) * d *
                      (1 - (r : ℝ) * Nat.ceil ((1 + μ) * d) * p) ^ k
                    - c * (∑ i ∈ Finset.range k,
                        (1 - (r : ℝ) * Nat.ceil ((1 + μ) * d) * p) ^ i))
                    * (p * (1 - p) ^ (r * Nat.ceil ((1 + μ) * d))))
              - (r : ℝ) * freedmanPenalty V r (Nat.ceil ((1 + μ) * d)) p c)

/-- Fully numeric ceiled Freedman parameter core. At this point the hypergraph has disappeared: the
remaining task is a real-analysis parameter choice depending only on the finite ambient size `|V|`, the
degree scale `d`, and the canonical ceiling `Nat.ceil ((1 + μ) * d)`. -/
def FreedmanCeilNumericThresholdParameterCore (r : ℕ) (β μ η d₀ K : ℝ) : Prop :=
  ∀ {V : Type} [Fintype V] (d : ℝ),
    0 < d →
    d₀ ≤ d →
    (Fintype.card V : ℝ) ≤ K * d ^ 2 →
    ∃ (p c lam : ℝ) (T : ℕ),
      0 ≤ p ∧ p ≤ 1 ∧ 0 < p ∧ 0 < c ∧
      0 ≤ 1 - (r : ℝ) * Nat.ceil ((1 + μ) * d) * p ∧
      lam ≤ 1 ∧ 0 ≤ lam ∧ lam ^ T ≤ β ∧
      (Fintype.card V : ℝ) * (2 * Real.exp (-c ^ 2 /
        (2 * ((Nat.ceil ((1 + μ) * d) : ℝ) ^ 2 *
          ((r : ℝ) * Nat.ceil ((1 + μ) * d) * p)
          + (Nat.ceil ((1 + μ) * d) : ℝ) / 3 * c)))) < 1 ∧
      (∀ k, k < T →
        0 ≤ ((1 - μ) * d *
                (1 - (r : ℝ) * Nat.ceil ((1 + μ) * d) * p) ^ k
              - c * (∑ i ∈ Finset.range k,
                  (1 - (r : ℝ) * Nat.ceil ((1 + μ) * d) * p) ^ i))
              * (p * (1 - p) ^ (r * Nat.ceil ((1 + μ) * d)))
        ∧ (1 - lam) * (Fintype.card V : ℝ)
            ≤ (1 - η) * (Fintype.card V : ℝ)
                * (((1 - μ) * d *
                      (1 - (r : ℝ) * Nat.ceil ((1 + μ) * d) * p) ^ k
                    - c * (∑ i ∈ Finset.range k,
                        (1 - (r : ℝ) * Nat.ceil ((1 + μ) * d) * p) ^ i))
                    * (p * (1 - p) ^ (r * Nat.ceil ((1 + μ) * d))))
              - (r : ℝ) * freedmanPenalty V r (Nat.ceil ((1 + μ) * d)) p c)

/-- Type-free numeric core. The ambient finite type has been replaced by its cardinality `N`; this is
the smallest current residual for the Freedman parameter selection. -/
def FreedmanCardNumericThresholdParameterCore (r : ℕ) (β μ η d₀ K : ℝ) : Prop :=
  ∀ (N : ℕ) (d : ℝ),
    0 < d →
    d₀ ≤ d →
    (N : ℝ) ≤ K * d ^ 2 →
    ∃ (p c lam : ℝ) (T : ℕ),
      0 ≤ p ∧ p ≤ 1 ∧ 0 < p ∧ 0 < c ∧
      0 ≤ 1 - (r : ℝ) * Nat.ceil ((1 + μ) * d) * p ∧
      lam ≤ 1 ∧ 0 ≤ lam ∧ lam ^ T ≤ β ∧
      (N : ℝ) * (2 * Real.exp (-c ^ 2 /
        (2 * ((Nat.ceil ((1 + μ) * d) : ℝ) ^ 2 *
          ((r : ℝ) * Nat.ceil ((1 + μ) * d) * p)
          + (Nat.ceil ((1 + μ) * d) : ℝ) / 3 * c)))) < 1 ∧
      (∀ k, k < T →
        0 ≤ ((1 - μ) * d *
                (1 - (r : ℝ) * Nat.ceil ((1 + μ) * d) * p) ^ k
              - c * (∑ i ∈ Finset.range k,
                  (1 - (r : ℝ) * Nat.ceil ((1 + μ) * d) * p) ^ i))
              * (p * (1 - p) ^ (r * Nat.ceil ((1 + μ) * d)))
        ∧ (1 - lam) * (N : ℝ)
            ≤ (1 - η) * (N : ℝ)
                * (((1 - μ) * d *
                      (1 - (r : ℝ) * Nat.ceil ((1 + μ) * d) * p) ^ k
                    - c * (∑ i ∈ Finset.range k,
                        (1 - (r : ℝ) * Nat.ceil ((1 + μ) * d) * p) ^ i))
                    * (p * (1 - p) ^ (r * Nat.ceil ((1 + μ) * d))))
              - (r : ℝ) * ((N : ℝ) * ((N : ℝ) * (2 * Real.exp (-c ^ 2 /
                  (2 * ((Nat.ceil ((1 + μ) * d) : ℝ) ^ 2 *
                    ((r : ℝ) * Nat.ceil ((1 + μ) * d) * p)
                    + (Nat.ceil ((1 + μ) * d) : ℝ) / 3 * c)))))))

/-- Explicit-parameter version of the type-free cardinal core. This is the same residual as
`FreedmanCardNumericThresholdParameterCore`, but the parameter choice is named as functions of
`r, β, N, d`. The theorem below mechanically forgets those functions and recovers the existential
core consumed by Paper III. -/
def FreedmanCardExplicitParameterCore
    (p c lam : ℕ → ℝ → ℕ → ℝ → ℝ) (T : ℕ → ℝ → ℕ → ℝ → ℕ)
    (r : ℕ) (β μ η d₀ K : ℝ) : Prop :=
  ∀ (N : ℕ) (d : ℝ),
    0 < d →
    d₀ ≤ d →
    (N : ℝ) ≤ K * d ^ 2 →
    0 ≤ p r β N d ∧ p r β N d ≤ 1 ∧ 0 < p r β N d ∧ 0 < c r β N d ∧
    0 ≤ 1 - (r : ℝ) * Nat.ceil ((1 + μ) * d) * p r β N d ∧
    lam r β N d ≤ 1 ∧ 0 ≤ lam r β N d ∧ (lam r β N d) ^ T r β N d ≤ β ∧
    (N : ℝ) * (2 * Real.exp (-(c r β N d) ^ 2 /
      (2 * ((Nat.ceil ((1 + μ) * d) : ℝ) ^ 2 *
        ((r : ℝ) * Nat.ceil ((1 + μ) * d) * p r β N d)
        + (Nat.ceil ((1 + μ) * d) : ℝ) / 3 * c r β N d)))) < 1 ∧
    (∀ k, k < T r β N d →
      0 ≤ ((1 - μ) * d *
              (1 - (r : ℝ) * Nat.ceil ((1 + μ) * d) * p r β N d) ^ k
            - c r β N d * (∑ i ∈ Finset.range k,
                (1 - (r : ℝ) * Nat.ceil ((1 + μ) * d) * p r β N d) ^ i))
            * (p r β N d * (1 - p r β N d) ^ (r * Nat.ceil ((1 + μ) * d)))
      ∧ (1 - lam r β N d) * (N : ℝ)
          ≤ (1 - η) * (N : ℝ)
              * (((1 - μ) * d *
                    (1 - (r : ℝ) * Nat.ceil ((1 + μ) * d) * p r β N d) ^ k
                  - c r β N d * (∑ i ∈ Finset.range k,
                      (1 - (r : ℝ) * Nat.ceil ((1 + μ) * d) * p r β N d) ^ i))
                  * (p r β N d * (1 - p r β N d) ^ (r * Nat.ceil ((1 + μ) * d))))
            - (r : ℝ) * ((N : ℝ) * ((N : ℝ) * (2 * Real.exp (-(c r β N d) ^ 2 /
                (2 * ((Nat.ceil ((1 + μ) * d) : ℝ) ^ 2 *
                  ((r : ℝ) * Nat.ceil ((1 + μ) * d) * p r β N d)
                  + (Nat.ceil ((1 + μ) * d) : ℝ) / 3 * c r β N d)))))))

/-- Basic sign and decay conditions for an explicit type-free Freedman parameter choice. -/
def FreedmanCardExplicitBasicCore
    (p c lam : ℕ → ℝ → ℕ → ℝ → ℝ) (T : ℕ → ℝ → ℕ → ℝ → ℕ)
    (r : ℕ) (β μ d₀ K : ℝ) : Prop :=
  ∀ (N : ℕ) (d : ℝ),
    0 < d →
    d₀ ≤ d →
    (N : ℝ) ≤ K * d ^ 2 →
    0 ≤ p r β N d ∧ p r β N d ≤ 1 ∧ 0 < p r β N d ∧ 0 < c r β N d ∧
    0 ≤ 1 - (r : ℝ) * Nat.ceil ((1 + μ) * d) * p r β N d ∧
    lam r β N d ≤ 1 ∧ 0 ≤ lam r β N d ∧ (lam r β N d) ^ T r β N d ≤ β

/-- The explicit type-free Freedman bad-event inequality. -/
def FreedmanCardExplicitBadEventCore
    (p c : ℕ → ℝ → ℕ → ℝ → ℝ) (r : ℕ) (β μ d₀ K : ℝ) : Prop :=
  ∀ (N : ℕ) (d : ℝ),
    0 < d →
    d₀ ≤ d →
    (N : ℝ) ≤ K * d ^ 2 →
    (N : ℝ) * (2 * Real.exp (-(c r β N d) ^ 2 /
      (2 * ((Nat.ceil ((1 + μ) * d) : ℝ) ^ 2 *
        ((r : ℝ) * Nat.ceil ((1 + μ) * d) * p r β N d)
        + (Nat.ceil ((1 + μ) * d) : ℝ) / 3 * c r β N d)))) < 1

/-- The explicit type-free Freedman round-by-round crux inequality. -/
def FreedmanCardExplicitRoundCore
    (p c lam : ℕ → ℝ → ℕ → ℝ → ℝ) (T : ℕ → ℝ → ℕ → ℝ → ℕ)
    (r : ℕ) (β μ η d₀ K : ℝ) : Prop :=
  ∀ (N : ℕ) (d : ℝ),
    0 < d →
    d₀ ≤ d →
    (N : ℝ) ≤ K * d ^ 2 →
    ∀ k, k < T r β N d →
      0 ≤ ((1 - μ) * d *
              (1 - (r : ℝ) * Nat.ceil ((1 + μ) * d) * p r β N d) ^ k
            - c r β N d * (∑ i ∈ Finset.range k,
                (1 - (r : ℝ) * Nat.ceil ((1 + μ) * d) * p r β N d) ^ i))
            * (p r β N d * (1 - p r β N d) ^ (r * Nat.ceil ((1 + μ) * d)))
      ∧ (1 - lam r β N d) * (N : ℝ)
          ≤ (1 - η) * (N : ℝ)
              * (((1 - μ) * d *
                    (1 - (r : ℝ) * Nat.ceil ((1 + μ) * d) * p r β N d) ^ k
                  - c r β N d * (∑ i ∈ Finset.range k,
                      (1 - (r : ℝ) * Nat.ceil ((1 + μ) * d) * p r β N d) ^ i))
                  * (p r β N d * (1 - p r β N d) ^ (r * Nat.ceil ((1 + μ) * d))))
            - (r : ℝ) * ((N : ℝ) * ((N : ℝ) * (2 * Real.exp (-(c r β N d) ^ 2 /
                (2 * ((Nat.ceil ((1 + μ) * d) : ℝ) ^ 2 *
                  ((r : ℝ) * Nat.ceil ((1 + μ) * d) * p r β N d)
                  + (Nat.ceil ((1 + μ) * d) : ℝ) / 3 * c r β N d))))))

/-- The one-round survival factor used by the explicit cardinal parameter core. -/
noncomputable def freedmanCardQ
    (p : ℕ → ℝ → ℕ → ℝ → ℝ) (r : ℕ) (β : ℝ) (N : ℕ) (d μ : ℝ) : ℝ :=
  1 - (r : ℝ) * Nat.ceil ((1 + μ) * d) * p r β N d

/-- The deterministic lower proxy for the residual degree before the retained-edge gain. -/
noncomputable def freedmanCardDegreeProxy
    (p c : ℕ → ℝ → ℕ → ℝ → ℝ) (r : ℕ) (β : ℝ) (N k : ℕ) (d μ : ℝ) : ℝ :=
  (1 - μ) * d * (freedmanCardQ p r β N d μ) ^ k
    - c r β N d * (∑ i ∈ Finset.range k, (freedmanCardQ p r β N d μ) ^ i)

/-- The per-round matching gain proxy in the explicit cardinal core. -/
noncomputable def freedmanCardGain
    (p c : ℕ → ℝ → ℕ → ℝ → ℝ) (r : ℕ) (β : ℝ) (N k : ℕ) (d μ : ℝ) : ℝ :=
  freedmanCardDegreeProxy p c r β N k d μ
    * (p r β N d * (1 - p r β N d) ^ (r * Nat.ceil ((1 + μ) * d)))

/-- The all-vertices Freedman bad-event probability proxy in the explicit cardinal core. -/
noncomputable def freedmanCardBadEventProb
    (p c : ℕ → ℝ → ℕ → ℝ → ℝ) (r : ℕ) (β : ℝ) (N : ℕ) (d μ : ℝ) : ℝ :=
  (N : ℝ) * (2 * Real.exp (-(c r β N d) ^ 2 /
    (2 * ((Nat.ceil ((1 + μ) * d) : ℝ) ^ 2 *
      ((r : ℝ) * Nat.ceil ((1 + μ) * d) * p r β N d)
      + (Nat.ceil ((1 + μ) * d) : ℝ) / 3 * c r β N d))))

/-- The Freedman bad-event penalty in the explicit cardinal core. -/
noncomputable def freedmanCardPenalty
    (p c : ℕ → ℝ → ℕ → ℝ → ℝ) (r : ℕ) (β : ℝ) (N : ℕ) (d μ : ℝ) : ℝ :=
  (N : ℝ) * freedmanCardBadEventProb p c r β N d μ

/-- Concrete one-round probability used by the residual parameter atom. -/
noncomputable def freedmanExplicitP (r : ℕ) (_β : ℝ) (_N : ℕ) (d : ℝ) : ℝ :=
  (1 : ℝ) / (100 * (r : ℝ) * Nat.ceil ((1 + (1 : ℝ) / 100) * d))

/-- Concrete Freedman deviation scale used by the residual parameter atom. -/
noncomputable def freedmanExplicitC (_r : ℕ) (_β : ℝ) (_N : ℕ) (d : ℝ) : ℝ :=
  Real.sqrt d

/-- Concrete one-step decay factor used by the residual parameter atom. -/
noncomputable def freedmanExplicitLam (_r : ℕ) (β : ℝ) (_N : ℕ) (_d : ℝ) : ℝ :=
  min (β / 2) ((1 : ℝ) / 2)

/-- Concrete number of rounds used by the residual parameter atom. -/
def freedmanExplicitT (_r : ℕ) (_β : ℝ) (_N : ℕ) (_d : ℝ) : ℕ :=
  1

/-- Shorthand version of the explicit round crux, using `q`, gain, and penalty as named terms. -/
def FreedmanCardExplicitRoundCoreFactored
    (p c lam : ℕ → ℝ → ℕ → ℝ → ℝ) (T : ℕ → ℝ → ℕ → ℝ → ℕ)
    (r : ℕ) (β μ η d₀ K : ℝ) : Prop :=
  ∀ (N : ℕ) (d : ℝ),
    0 < d →
    d₀ ≤ d →
    (N : ℝ) ≤ K * d ^ 2 →
    ∀ k, k < T r β N d →
      0 ≤ freedmanCardGain p c r β N k d μ ∧
      (1 - lam r β N d) * (N : ℝ)
        ≤ (1 - η) * (N : ℝ) * freedmanCardGain p c r β N k d μ
          - (r : ℝ) * freedmanCardPenalty p c r β N d μ

/-- The factored round core is definitionally the expanded explicit round core. -/
theorem freedmanCardExplicitRoundCore_of_factored
    {p c lam : ℕ → ℝ → ℕ → ℝ → ℝ} {T : ℕ → ℝ → ℕ → ℝ → ℕ}
    {r : ℕ} {β μ η d₀ K : ℝ}
    (h : FreedmanCardExplicitRoundCoreFactored p c lam T r β μ η d₀ K) :
    FreedmanCardExplicitRoundCore p c lam T r β μ η d₀ K := by
  intro N d hd hd0 hsize k hk
  simpa [FreedmanCardExplicitRoundCoreFactored, freedmanCardGain,
    freedmanCardDegreeProxy, freedmanCardQ, freedmanCardPenalty, freedmanCardBadEventProb]
    using h N d hd hd0 hsize k hk

/-- The bad-event core bounds the named Freedman penalty by the ambient cardinality. This isolates
the only use of the exponential smallness inequality inside the round crux. -/
theorem freedmanCardPenalty_le_card_of_badEvent
    {p c : ℕ → ℝ → ℕ → ℝ → ℝ} {r N : ℕ} {β μ d₀ K d : ℝ}
    (hbad : FreedmanCardExplicitBadEventCore p c r β μ d₀ K)
    (hd : 0 < d) (hd0 : d₀ ≤ d) (hsize : (N : ℝ) ≤ K * d ^ 2) :
    freedmanCardPenalty p c r β N d μ ≤ (N : ℝ) := by
  have hsmall := hbad N d hd hd0 hsize
  by_cases hN : N = 0
  · subst N
    norm_num [freedmanCardPenalty, freedmanCardBadEventProb]
  · have hNpos_nat : 0 < N := Nat.pos_of_ne_zero hN
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos_nat
    exact le_of_lt <| by
      calc freedmanCardPenalty p c r β N d μ
          = (N : ℝ) * freedmanCardBadEventProb p c r β N d μ := by
              rfl
        _ < (N : ℝ) * 1 := mul_lt_mul_of_pos_left hsmall hNpos
        _ = (N : ℝ) := by ring

/-- Round crux with the Freedman penalty replaced by the coarser cardinality bound. -/
def FreedmanCardExplicitRoundCoreCardPenalty
    (p c lam : ℕ → ℝ → ℕ → ℝ → ℝ) (T : ℕ → ℝ → ℕ → ℝ → ℕ)
    (r : ℕ) (β μ η d₀ K : ℝ) : Prop :=
  ∀ (N : ℕ) (d : ℝ),
    0 < d →
    d₀ ≤ d →
    (N : ℝ) ≤ K * d ^ 2 →
    ∀ k, k < T r β N d →
      0 ≤ freedmanCardGain p c r β N k d μ ∧
      (1 - lam r β N d) * (N : ℝ)
        ≤ (1 - η) * (N : ℝ) * freedmanCardGain p c r β N k d μ
          - (r : ℝ) * (N : ℝ)

/-- The scalar gain lower bound that implies the card-penalty round crux. -/
def FreedmanCardExplicitGainLowerCore
    (p c lam : ℕ → ℝ → ℕ → ℝ → ℝ) (T : ℕ → ℝ → ℕ → ℝ → ℕ)
    (r : ℕ) (β μ η d₀ K : ℝ) : Prop :=
  ∀ (N : ℕ) (d : ℝ),
    0 < d →
    d₀ ≤ d →
    (N : ℝ) ≤ K * d ^ 2 →
    ∀ k, k < T r β N d →
      0 ≤ freedmanCardGain p c r β N k d μ ∧
      (1 - lam r β N d) + (r : ℝ)
        ≤ (1 - η) * freedmanCardGain p c r β N k d μ

/-- Positivity of the deterministic residual-degree proxy. -/
def FreedmanCardExplicitDegreeProxyNonnegCore
    (p c : ℕ → ℝ → ℕ → ℝ → ℝ) (T : ℕ → ℝ → ℕ → ℝ → ℕ)
    (r : ℕ) (β μ d₀ K : ℝ) : Prop :=
  ∀ (N : ℕ) (d : ℝ),
    0 < d →
    d₀ ≤ d →
    (N : ℝ) ≤ K * d ^ 2 →
    ∀ k, k < T r β N d →
      0 ≤ freedmanCardDegreeProxy p c r β N k d μ

/-- Direct scalar lower bound on the per-round gain. -/
def FreedmanCardExplicitGainScalarLowerCore
    (p c lam : ℕ → ℝ → ℕ → ℝ → ℝ) (T : ℕ → ℝ → ℕ → ℝ → ℕ)
    (r : ℕ) (β μ η d₀ K : ℝ) : Prop :=
  ∀ (N : ℕ) (d : ℝ),
    0 < d →
    d₀ ≤ d →
    (N : ℝ) ≤ K * d ^ 2 →
    ∀ k, k < T r β N d →
      (1 - lam r β N d) + (r : ℝ)
        ≤ (1 - η) * freedmanCardGain p c r β N k d μ

/-- The inequality part of the factored round core, separated from gain nonnegativity. -/
def FreedmanCardExplicitRoundIneqCore
    (p c lam : ℕ → ℝ → ℕ → ℝ → ℝ) (T : ℕ → ℝ → ℕ → ℝ → ℕ)
    (r : ℕ) (β μ η d₀ K : ℝ) : Prop :=
  ∀ (N : ℕ) (d : ℝ),
    0 < d →
    d₀ ≤ d →
    (N : ℝ) ≤ K * d ^ 2 →
    ∀ k, k < T r β N d →
      (1 - lam r β N d) * (N : ℝ)
        ≤ (1 - η) * (N : ℝ) * freedmanCardGain p c r β N k d μ
          - (r : ℝ) * freedmanCardPenalty p c r β N d μ

/-- Proxy nonnegativity plus scalar gain lower bound imply the gain-lower core. -/
theorem freedmanCardExplicitGainLowerCore_of_proxy_and_scalar
    {p c lam : ℕ → ℝ → ℕ → ℝ → ℝ} {T : ℕ → ℝ → ℕ → ℝ → ℕ}
    {r : ℕ} {β μ η d₀ K : ℝ}
    (hbasic : FreedmanCardExplicitBasicCore p c lam T r β μ d₀ K)
    (hproxy : FreedmanCardExplicitDegreeProxyNonnegCore p c T r β μ d₀ K)
    (hscalar : FreedmanCardExplicitGainScalarLowerCore p c lam T r β μ η d₀ K) :
    FreedmanCardExplicitGainLowerCore p c lam T r β μ η d₀ K := by
  intro N d hd hd0 hsize k hk
  obtain ⟨hp0, hp1, _hppos, _hcpos, _hq, _hlam1, _hlam0, _hTβ⟩ :=
    hbasic N d hd hd0 hsize
  have hproxy0 := hproxy N d hd hd0 hsize k hk
  have hfactor0 : 0 ≤ p r β N d * (1 - p r β N d) ^ (r * Nat.ceil ((1 + μ) * d)) := by
    exact mul_nonneg hp0 (pow_nonneg (sub_nonneg.mpr hp1) _)
  refine ⟨?_, hscalar N d hd hd0 hsize k hk⟩
  simpa [freedmanCardGain] using mul_nonneg hproxy0 hfactor0

/-- Proxy nonnegativity plus the factored round inequality imply the full factored round core. -/
theorem freedmanCardExplicitRoundCoreFactored_of_proxy_and_ineq
    {p c lam : ℕ → ℝ → ℕ → ℝ → ℝ} {T : ℕ → ℝ → ℕ → ℝ → ℕ}
    {r : ℕ} {β μ η d₀ K : ℝ}
    (hbasic : FreedmanCardExplicitBasicCore p c lam T r β μ d₀ K)
    (hproxy : FreedmanCardExplicitDegreeProxyNonnegCore p c T r β μ d₀ K)
    (hineq : FreedmanCardExplicitRoundIneqCore p c lam T r β μ η d₀ K) :
    FreedmanCardExplicitRoundCoreFactored p c lam T r β μ η d₀ K := by
  intro N d hd hd0 hsize k hk
  obtain ⟨hp0, hp1, _hppos, _hcpos, _hq, _hlam1, _hlam0, _hTβ⟩ :=
    hbasic N d hd hd0 hsize
  have hproxy0 := hproxy N d hd hd0 hsize k hk
  have hfactor0 : 0 ≤ p r β N d * (1 - p r β N d) ^ (r * Nat.ceil ((1 + μ) * d)) := by
    exact mul_nonneg hp0 (pow_nonneg (sub_nonneg.mpr hp1) _)
  refine ⟨?_, hineq N d hd hd0 hsize k hk⟩
  simpa [freedmanCardGain] using mul_nonneg hproxy0 hfactor0

/-- The gain-lower form mechanically implies the card-penalty round core. -/
theorem freedmanCardExplicitRoundCoreCardPenalty_of_gainLower
    {p c lam : ℕ → ℝ → ℕ → ℝ → ℝ} {T : ℕ → ℝ → ℕ → ℝ → ℕ}
    {r : ℕ} {β μ η d₀ K : ℝ}
    (h : FreedmanCardExplicitGainLowerCore p c lam T r β μ η d₀ K) :
    FreedmanCardExplicitRoundCoreCardPenalty p c lam T r β μ η d₀ K := by
  intro N d hd hd0 hsize k hk
  obtain ⟨hgain0, hgainLower⟩ := h N d hd hd0 hsize k hk
  refine ⟨hgain0, ?_⟩
  have hNnonneg : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hmul : ((1 - lam r β N d) + (r : ℝ)) * (N : ℝ)
      ≤ ((1 - η) * freedmanCardGain p c r β N k d μ) * (N : ℝ) :=
    mul_le_mul_of_nonneg_right hgainLower hNnonneg
  linarith

/-- A card-penalty round core plus the bad-event bound implies the factored Freedman round core. -/
theorem freedmanCardExplicitRoundCoreFactored_of_cardPenalty
    {p c lam : ℕ → ℝ → ℕ → ℝ → ℝ} {T : ℕ → ℝ → ℕ → ℝ → ℕ}
    {r : ℕ} {β μ η d₀ K : ℝ}
    (hbad : FreedmanCardExplicitBadEventCore p c r β μ d₀ K)
    (hround : FreedmanCardExplicitRoundCoreCardPenalty p c lam T r β μ η d₀ K) :
    FreedmanCardExplicitRoundCoreFactored p c lam T r β μ η d₀ K := by
  intro N d hd hd0 hsize k hk
  obtain ⟨hgain, hround'⟩ := hround N d hd hd0 hsize k hk
  refine ⟨hgain, ?_⟩
  have hpen := freedmanCardPenalty_le_card_of_badEvent (p := p) (c := c) (r := r)
    (N := N) (β := β) (μ := μ) (d₀ := d₀) (K := K) (d := d) hbad hd hd0 hsize
  have hrnn : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
  have hmul : (r : ℝ) * freedmanCardPenalty p c r β N d μ ≤ (r : ℝ) * (N : ℝ) :=
    mul_le_mul_of_nonneg_left hpen hrnn
  linarith

/-- Split explicit core: basic parameter facts, bad-event smallness, and the round crux separated. -/
def FreedmanCardExplicitSplitCore
    (p c lam : ℕ → ℝ → ℕ → ℝ → ℝ) (T : ℕ → ℝ → ℕ → ℝ → ℕ)
    (r : ℕ) (β μ η d₀ K : ℝ) : Prop :=
  FreedmanCardExplicitBasicCore p c lam T r β μ d₀ K ∧
  FreedmanCardExplicitBadEventCore p c r β μ d₀ K ∧
  FreedmanCardExplicitRoundCore p c lam T r β μ η d₀ K

/-- Split explicit core with the round crux written in factored notation. -/
def FreedmanCardExplicitSplitFactoredCore
    (p c lam : ℕ → ℝ → ℕ → ℝ → ℝ) (T : ℕ → ℝ → ℕ → ℝ → ℕ)
    (r : ℕ) (β μ η d₀ K : ℝ) : Prop :=
  FreedmanCardExplicitBasicCore p c lam T r β μ d₀ K ∧
  FreedmanCardExplicitBadEventCore p c r β μ d₀ K ∧
  FreedmanCardExplicitRoundCoreFactored p c lam T r β μ η d₀ K

/-- The factored split core mechanically implies the expanded split core. -/
theorem freedmanCardExplicitSplitCore_of_factored
    {p c lam : ℕ → ℝ → ℕ → ℝ → ℝ} {T : ℕ → ℝ → ℕ → ℝ → ℕ}
    {r : ℕ} {β μ η d₀ K : ℝ}
    (h : FreedmanCardExplicitSplitFactoredCore p c lam T r β μ η d₀ K) :
    FreedmanCardExplicitSplitCore p c lam T r β μ η d₀ K := by
  exact ⟨h.1, h.2.1, freedmanCardExplicitRoundCore_of_factored h.2.2⟩

/-- Split explicit core with the round crux using the coarser cardinality penalty. -/
def FreedmanCardExplicitSplitCardPenaltyCore
    (p c lam : ℕ → ℝ → ℕ → ℝ → ℝ) (T : ℕ → ℝ → ℕ → ℝ → ℕ)
    (r : ℕ) (β μ η d₀ K : ℝ) : Prop :=
  FreedmanCardExplicitBasicCore p c lam T r β μ d₀ K ∧
  FreedmanCardExplicitBadEventCore p c r β μ d₀ K ∧
  FreedmanCardExplicitRoundCoreCardPenalty p c lam T r β μ η d₀ K

/-- Split explicit core where the round condition is only the scalar gain-lower inequality. -/
def FreedmanCardExplicitSplitGainLowerCore
    (p c lam : ℕ → ℝ → ℕ → ℝ → ℝ) (T : ℕ → ℝ → ℕ → ℝ → ℕ)
    (r : ℕ) (β μ η d₀ K : ℝ) : Prop :=
  FreedmanCardExplicitBasicCore p c lam T r β μ d₀ K ∧
  FreedmanCardExplicitBadEventCore p c r β μ d₀ K ∧
  FreedmanCardExplicitGainLowerCore p c lam T r β μ η d₀ K

/-- Split explicit core where the gain-lower condition is decomposed into proxy nonnegativity and a
scalar lower bound. -/
def FreedmanCardExplicitSplitProxyScalarCore
    (p c lam : ℕ → ℝ → ℕ → ℝ → ℝ) (T : ℕ → ℝ → ℕ → ℝ → ℕ)
    (r : ℕ) (β μ η d₀ K : ℝ) : Prop :=
  FreedmanCardExplicitBasicCore p c lam T r β μ d₀ K ∧
  FreedmanCardExplicitBadEventCore p c r β μ d₀ K ∧
  FreedmanCardExplicitDegreeProxyNonnegCore p c T r β μ d₀ K ∧
  FreedmanCardExplicitGainScalarLowerCore p c lam T r β μ η d₀ K

/-- Split explicit core where the factored round condition is decomposed into proxy nonnegativity and
the actual factored round inequality. -/
def FreedmanCardExplicitSplitProxyIneqCore
    (p c lam : ℕ → ℝ → ℕ → ℝ → ℝ) (T : ℕ → ℝ → ℕ → ℝ → ℕ)
    (r : ℕ) (β μ η d₀ K : ℝ) : Prop :=
  FreedmanCardExplicitBasicCore p c lam T r β μ d₀ K ∧
  FreedmanCardExplicitDegreeProxyNonnegCore p c T r β μ d₀ K ∧
  FreedmanCardExplicitBadEventCore p c r β μ d₀ K ∧
  FreedmanCardExplicitRoundIneqCore p c lam T r β μ η d₀ K

/-- The remaining non-mechanical pair once signs and proxy positivity have been discharged. -/
def FreedmanCardExplicitBadRoundCore
    (p c lam : ℕ → ℝ → ℕ → ℝ → ℝ) (T : ℕ → ℝ → ℕ → ℝ → ℕ)
    (r : ℕ) (β μ η d₀ K : ℝ) : Prop :=
  FreedmanCardExplicitBadEventCore p c r β μ d₀ K ∧
  FreedmanCardExplicitRoundIneqCore p c lam T r β μ η d₀ K

/-- Reassemble the named residual pair from its two independent halves. -/
theorem freedmanCardExplicitBadRoundCore_of_badEvent_roundIneq
    {p c lam : ℕ → ℝ → ℕ → ℝ → ℝ} {T : ℕ → ℝ → ℕ → ℝ → ℕ}
    {r : ℕ} {β μ η d₀ K : ℝ}
    (hbad : FreedmanCardExplicitBadEventCore p c r β μ d₀ K)
    (hround : FreedmanCardExplicitRoundIneqCore p c lam T r β μ η d₀ K) :
    FreedmanCardExplicitBadRoundCore p c lam T r β μ η d₀ K :=
  ⟨hbad, hround⟩

/-- Basic facts and proxy nonnegativity reduce the proxy/inequality split core to the bad-event plus
round-inequality pair. -/
theorem freedmanCardExplicitSplitProxyIneqCore_of_badRound
    {p c lam : ℕ → ℝ → ℕ → ℝ → ℝ} {T : ℕ → ℝ → ℕ → ℝ → ℕ}
    {r : ℕ} {β μ η d₀ K : ℝ}
    (hbasic : FreedmanCardExplicitBasicCore p c lam T r β μ d₀ K)
    (hproxy : FreedmanCardExplicitDegreeProxyNonnegCore p c T r β μ d₀ K)
    (hbadRound : FreedmanCardExplicitBadRoundCore p c lam T r β μ η d₀ K) :
    FreedmanCardExplicitSplitProxyIneqCore p c lam T r β μ η d₀ K :=
  ⟨hbasic, hproxy, hbadRound.1, hbadRound.2⟩

/-- Proxy nonnegativity plus scalar lower bound mechanically imply the gain-lower split core. -/
theorem freedmanCardExplicitSplitGainLowerCore_of_proxyScalar
    {p c lam : ℕ → ℝ → ℕ → ℝ → ℝ} {T : ℕ → ℝ → ℕ → ℝ → ℕ}
    {r : ℕ} {β μ η d₀ K : ℝ}
    (h : FreedmanCardExplicitSplitProxyScalarCore p c lam T r β μ η d₀ K) :
    FreedmanCardExplicitSplitGainLowerCore p c lam T r β μ η d₀ K := by
  exact ⟨h.1, h.2.1,
    freedmanCardExplicitGainLowerCore_of_proxy_and_scalar h.1 h.2.2.1 h.2.2.2⟩

/-- Proxy nonnegativity plus the actual factored inequality mechanically imply the factored split
core. -/
theorem freedmanCardExplicitSplitFactoredCore_of_proxyIneq
    {p c lam : ℕ → ℝ → ℕ → ℝ → ℝ} {T : ℕ → ℝ → ℕ → ℝ → ℕ}
    {r : ℕ} {β μ η d₀ K : ℝ}
    (h : FreedmanCardExplicitSplitProxyIneqCore p c lam T r β μ η d₀ K) :
    FreedmanCardExplicitSplitFactoredCore p c lam T r β μ η d₀ K := by
  exact ⟨h.1, h.2.2.1,
    freedmanCardExplicitRoundCoreFactored_of_proxy_and_ineq h.1 h.2.1 h.2.2.2⟩

/-- The sign and one-step decay conditions for the concrete explicit parameters. -/
theorem freedmanExplicitBasicCore (r : ℕ) (hr : 2 ≤ r) (β : ℝ) (hβ : 0 < β) :
    FreedmanCardExplicitBasicCore freedmanExplicitP freedmanExplicitC freedmanExplicitLam
      freedmanExplicitT r β ((1 : ℝ) / 100) 1 1 := by
  intro N d hd hd0 _hsize
  have hrpos_nat : 0 < r := lt_of_lt_of_le (by norm_num) hr
  have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hrpos_nat
  have hApos : 0 < (1 + (1 : ℝ) / 100) * d := by positivity
  have hceil_pos_nat : 0 < Nat.ceil ((1 + (1 : ℝ) / 100) * d) :=
    Nat.ceil_pos.mpr hApos
  have hceil_pos : (0 : ℝ) < (Nat.ceil ((1 + (1 : ℝ) / 100) * d) : ℕ) := by
    exact_mod_cast hceil_pos_nat
  have hden_pos :
      0 < 100 * (r : ℝ) * Nat.ceil ((1 + (1 : ℝ) / 100) * d) := by
    positivity
  have hden_ge_one :
      1 ≤ 100 * (r : ℝ) * Nat.ceil ((1 + (1 : ℝ) / 100) * d) := by
    have hr_ge_one : (1 : ℝ) ≤ r := by exact_mod_cast (by omega : 1 ≤ r)
    have hceil_ge_one : (1 : ℝ) ≤ (Nat.ceil ((1 + (1 : ℝ) / 100) * d) : ℕ) := by
      exact_mod_cast hceil_pos_nat
    nlinarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [freedmanExplicitP]
    positivity
  · dsimp [freedmanExplicitP]
    simpa [one_div] using inv_le_one_of_one_le₀ hden_ge_one
  · dsimp [freedmanExplicitP]
    positivity
  · dsimp [freedmanExplicitC]
    exact Real.sqrt_pos.2 hd
  · dsimp [freedmanExplicitP]
    field_simp [hden_pos.ne']
    norm_num
  · dsimp [freedmanExplicitLam]
    exact (min_le_right (β / 2) ((1 : ℝ) / 2)).trans (by norm_num)
  · dsimp [freedmanExplicitLam]
    exact le_min (by nlinarith) (by norm_num)
  · dsimp [freedmanExplicitLam, freedmanExplicitT]
    rw [pow_one]
    exact (min_le_left (β / 2) ((1 : ℝ) / 2)).trans (by nlinarith)

/-- The deterministic residual-degree proxy is nonnegative for the concrete one-round parameters. -/
theorem freedmanExplicitDegreeProxyNonnegCore (r : ℕ) (β : ℝ) :
    FreedmanCardExplicitDegreeProxyNonnegCore freedmanExplicitP freedmanExplicitC freedmanExplicitT
      r β ((1 : ℝ) / 100) 1 1 := by
  intro N d hd _hd0 _hsize k hk
  have hk0 : k = 0 := by
    dsimp [freedmanExplicitT] at hk
    omega
  subst k
  dsimp [FreedmanCardExplicitDegreeProxyNonnegCore, freedmanCardDegreeProxy,
    freedmanCardQ, freedmanExplicitC, freedmanExplicitT]
  simp
  linarith

/-- The scalar gain-lower split core mechanically implies the card-penalty split core. -/
theorem freedmanCardExplicitSplitCardPenaltyCore_of_gainLower
    {p c lam : ℕ → ℝ → ℕ → ℝ → ℝ} {T : ℕ → ℝ → ℕ → ℝ → ℕ}
    {r : ℕ} {β μ η d₀ K : ℝ}
    (h : FreedmanCardExplicitSplitGainLowerCore p c lam T r β μ η d₀ K) :
    FreedmanCardExplicitSplitCardPenaltyCore p c lam T r β μ η d₀ K := by
  exact ⟨h.1, h.2.1, freedmanCardExplicitRoundCoreCardPenalty_of_gainLower h.2.2⟩

/-- The card-penalty split core mechanically implies the factored split core. -/
theorem freedmanCardExplicitSplitFactoredCore_of_cardPenalty
    {p c lam : ℕ → ℝ → ℕ → ℝ → ℝ} {T : ℕ → ℝ → ℕ → ℝ → ℕ}
    {r : ℕ} {β μ η d₀ K : ℝ}
    (h : FreedmanCardExplicitSplitCardPenaltyCore p c lam T r β μ η d₀ K) :
    FreedmanCardExplicitSplitFactoredCore p c lam T r β μ η d₀ K := by
  exact ⟨h.1, h.2.1, freedmanCardExplicitRoundCoreFactored_of_cardPenalty h.2.1 h.2.2⟩

/-- The split explicit core mechanically reassembles the explicit cardinal core. -/
theorem freedmanCardExplicitParameterCore_of_split
    {p c lam : ℕ → ℝ → ℕ → ℝ → ℝ} {T : ℕ → ℝ → ℕ → ℝ → ℕ}
    {r : ℕ} {β μ η d₀ K : ℝ}
    (h : FreedmanCardExplicitSplitCore p c lam T r β μ η d₀ K) :
    FreedmanCardExplicitParameterCore p c lam T r β μ η d₀ K := by
  intro N d hd hd0 hsize
  obtain ⟨hbasic, hbad, hround⟩ := h
  obtain ⟨hp0, hp1, hppos, hcpos, hq, hlam1, hlam0, hTβ⟩ :=
    hbasic N d hd hd0 hsize
  exact ⟨hp0, hp1, hppos, hcpos, hq, hlam1, hlam0, hTβ,
    hbad N d hd hd0 hsize, hround N d hd hd0 hsize⟩

/-- The explicit-parameter core implies the existential cardinal core. -/
theorem freedmanCardNumericThresholdParameterCore_of_explicit
    {p c lam : ℕ → ℝ → ℕ → ℝ → ℝ} {T : ℕ → ℝ → ℕ → ℝ → ℕ}
    {r : ℕ} {β μ η d₀ K : ℝ}
    (h : FreedmanCardExplicitParameterCore p c lam T r β μ η d₀ K) :
    FreedmanCardNumericThresholdParameterCore r β μ η d₀ K := by
  intro N d hd hd0 hsize
  obtain ⟨hp0, hp1, hppos, hcpos, hq, hlam1, hlam0, hTβ, hsmall, hcrux⟩ :=
    h N d hd hd0 hsize
  exact ⟨p r β N d, c r β N d, lam r β N d, T r β N d,
    hp0, hp1, hppos, hcpos, hq, hlam1, hlam0, hTβ, hsmall, hcrux⟩

/-- The type-free cardinal core implies the finite-type numeric core. -/
theorem freedmanCeilNumericThresholdParameterCore_of_card {r : ℕ} {β μ η d₀ K : ℝ}
    (h : FreedmanCardNumericThresholdParameterCore r β μ η d₀ K) :
    FreedmanCeilNumericThresholdParameterCore r β μ η d₀ K := by
  classical
  intro V _ d hd hd0 hsize
  obtain ⟨p, c, lam, T, hp0, hp1, hppos, hc, hq, hlam1, hlam0, hTβ, hsmall, hcrux⟩ :=
    h (Fintype.card V) d hd hd0 hsize
  refine ⟨p, c, lam, T, hp0, hp1, hppos, hc, hq, hlam1, hlam0, hTβ, hsmall, ?_⟩
  intro k hk
  simpa [freedmanPenalty] using hcrux k hk

/-- The numeric ceiled parameter core implies the ceiled threshold core. -/
theorem freedmanCeilThresholdParameterCore_of_numeric {r : ℕ} {β μ η d₀ K : ℝ}
    (h : FreedmanCeilNumericThresholdParameterCore r β μ η d₀ K) :
    FreedmanCeilThresholdParameterCore r β μ η d₀ K := by
  classical
  intro V _ _ H d hd hd0 _huni _hreg _hcodeg _hceil hsize
  obtain ⟨p, c, lam, T, hp0, hp1, hppos, hc, hq, hlam1, hlam0, hTβ, hsmall, hcrux⟩ :=
    h (V := V) d hd hd0 hsize
  refine ⟨p, c, lam, T, hp0, hp1, hppos, hc, hq, hlam1, hlam0, hTβ, ?_, hcrux⟩
  intro H' _huni' _hdeg'
  exact hsmall

/-- The ceiled parameter core implies the threshold parameter core. This is pure bookkeeping: `Δ` is
the natural ceiling of the supplied global degree bound. -/
theorem freedmanSizedThresholdParameterCore_of_ceil {r : ℕ} {β μ η d₀ K : ℝ}
    (hμ : 0 < μ) (h : FreedmanCeilThresholdParameterCore r β μ η d₀ K) :
    FreedmanSizedThresholdParameterCore r β μ η d₀ K := by
  classical
  intro V _ _ H d hd hd0 huni hreg hcodeg hceil hsize
  obtain ⟨p, c, lam, T, hp0, hp1, hppos, hc, hq, hlam1, hlam0, hTβ, hsmall, hcrux⟩ :=
    h H d hd hd0 huni hreg hcodeg hceil hsize
  let Δ : ℕ := Nat.ceil ((1 + μ) * d)
  have hΔ0 : 0 < Δ := by
    apply natCeil_pos_of_pos
    nlinarith
  have hdeg : ∀ x, degree H x ≤ Δ := by
    simpa [Δ] using degree_le_natCeil_of_real_bound H ((1 + μ) * d) hceil
  refine ⟨Δ, p, c, lam, T, hp0, hp1, hppos, hΔ0, hc, ?_, hlam1, hlam0, hdeg, hTβ, ?_, ?_⟩
  · simpa [Δ] using hq
  · intro H' huni' hdeg'
    simpa [Δ] using hsmall H' huni' hdeg'
  · intro k hk
    simpa [Δ] using hcrux k hk

/-- Mechanical assembly of the Freedman threshold parameter statement from the named sized core. -/
theorem nibble_params_exist_threshold_freedman_sized_of_core (r : ℕ) (_hr : 2 ≤ r)
    (β : ℝ) (hβ : 0 < β)
    (hcore : FreedmanSizedParameterCore r β ((1 : ℝ) / 100)
      (min (β / 4) ((1 : ℝ) / 100)) 1) :
    ∃ μ : ℝ, 0 < μ ∧ ∃ η : ℝ, 0 < η ∧ ∃ d₀ : ℝ, 0 < d₀ ∧
      ∃ K : ℝ, 0 < K ∧
      ∀ {V : Type} [Fintype V] [DecidableEq V] (H : Finset (Finset V)) (d : ℝ), 0 < d → d₀ ≤ d →
        IsUniform H r → NearlyRegularMost H d μ η → CodegreeBounded H (μ * d) →
        (∀ x : V, (degree H x : ℝ) ≤ (1 + μ) * d) →
        (Fintype.card V : ℝ) ≤ K * d ^ 2 →
        ∃ (Δ : ℕ) (p c lam : ℝ) (T : ℕ),
          0 ≤ p ∧ p ≤ 1 ∧ 0 < p ∧ 0 < Δ ∧ 0 < c ∧
          0 ≤ 1 - (r : ℝ) * Δ * p ∧ lam ≤ 1 ∧ 0 ≤ lam ∧ (∀ x, degree H x ≤ Δ) ∧ lam ^ T ≤ β ∧
          (∀ H' : Finset (Finset V), IsUniform H' r → (∀ x, degree H' x ≤ Δ) →
            (Fintype.card V : ℝ) * (2 * Real.exp (-c ^ 2 / (2 * ((Δ : ℝ) ^ 2 * ((r : ℝ) * Δ * p)
              + (Δ : ℝ) / 3 * c)))) < 1) ∧
          (∀ k, k < T →
            0 ≤ ((1 - μ) * d * (1 - (r : ℝ) * Δ * p) ^ k
                    - c * (∑ i ∈ Finset.range k, (1 - (r : ℝ) * Δ * p) ^ i))
                  * (p * (1 - p) ^ (r * Δ))
            ∧ (1 - lam) * (Fintype.card V : ℝ)
                ≤ (1 - η) * (Fintype.card V : ℝ)
                    * (((1 - μ) * d * (1 - (r : ℝ) * Δ * p) ^ k
                          - c * (∑ i ∈ Finset.range k, (1 - (r : ℝ) * Δ * p) ^ i))
                        * (p * (1 - p) ^ (r * Δ)))
                  - (r : ℝ) * freedmanPenalty V r Δ p c) := by
  classical
  refine ⟨(1 : ℝ) / 100, by norm_num, min (β / 4) ((1 : ℝ) / 100), ?_, 1, by norm_num,
    1, by norm_num, ?_⟩
  · exact lt_min (by positivity) (by norm_num)
  intro V _ _ H d hd _hd0 huni hreg hcodeg hceil hsize
  exact hcore H d hd huni hreg hcodeg hceil hsize

/-- Mechanical assembly of the Freedman threshold parameter statement from the correctly thresholded
parameter core. -/
theorem nibble_params_exist_threshold_freedman_sized_of_threshold_core (r : ℕ) (_hr : 2 ≤ r)
    (β : ℝ) (hβ : 0 < β)
    (hcore : ∃ d₀ : ℝ, 0 < d₀ ∧
      FreedmanSizedThresholdParameterCore r β ((1 : ℝ) / 100)
        (min (β / 4) ((1 : ℝ) / 100)) d₀ 1) :
    ∃ μ : ℝ, 0 < μ ∧ ∃ η : ℝ, 0 < η ∧ ∃ d₀ : ℝ, 0 < d₀ ∧
      ∃ K : ℝ, 0 < K ∧
      ∀ {V : Type} [Fintype V] [DecidableEq V] (H : Finset (Finset V)) (d : ℝ), 0 < d → d₀ ≤ d →
        IsUniform H r → NearlyRegularMost H d μ η → CodegreeBounded H (μ * d) →
        (∀ x : V, (degree H x : ℝ) ≤ (1 + μ) * d) →
        (Fintype.card V : ℝ) ≤ K * d ^ 2 →
        ∃ (Δ : ℕ) (p c lam : ℝ) (T : ℕ),
          0 ≤ p ∧ p ≤ 1 ∧ 0 < p ∧ 0 < Δ ∧ 0 < c ∧
          0 ≤ 1 - (r : ℝ) * Δ * p ∧ lam ≤ 1 ∧ 0 ≤ lam ∧ (∀ x, degree H x ≤ Δ) ∧ lam ^ T ≤ β ∧
          (∀ H' : Finset (Finset V), IsUniform H' r → (∀ x, degree H' x ≤ Δ) →
            (Fintype.card V : ℝ) * (2 * Real.exp (-c ^ 2 / (2 * ((Δ : ℝ) ^ 2 * ((r : ℝ) * Δ * p)
              + (Δ : ℝ) / 3 * c)))) < 1) ∧
          (∀ k, k < T →
            0 ≤ ((1 - μ) * d * (1 - (r : ℝ) * Δ * p) ^ k
                    - c * (∑ i ∈ Finset.range k, (1 - (r : ℝ) * Δ * p) ^ i))
                  * (p * (1 - p) ^ (r * Δ))
            ∧ (1 - lam) * (Fintype.card V : ℝ)
                ≤ (1 - η) * (Fintype.card V : ℝ)
                    * (((1 - μ) * d * (1 - (r : ℝ) * Δ * p) ^ k
                          - c * (∑ i ∈ Finset.range k, (1 - (r : ℝ) * Δ * p) ^ i))
                        * (p * (1 - p) ^ (r * Δ)))
                  - (r : ℝ) * freedmanPenalty V r Δ p c) := by
  classical
  obtain ⟨d₀, hd₀, hP⟩ := hcore
  refine ⟨(1 : ℝ) / 100, by norm_num, min (β / 4) ((1 : ℝ) / 100), ?_, d₀, hd₀,
    1, by norm_num, ?_⟩
  · exact lt_min (by positivity) (by norm_num)
  intro V _ _ H d hd hd0 huni hreg hcodeg hceil hsize
  exact hP H d hd hd0 huni hreg hcodeg hceil hsize

/-- Mechanical assembly of the Freedman threshold parameter statement from a split explicit
cardinality core. This keeps the remaining parameter proof in the smallest type-free interface. -/
theorem nibble_params_exist_threshold_freedman_sized_of_split_explicit_core
    (p c lam : ℕ → ℝ → ℕ → ℝ → ℝ) (T : ℕ → ℝ → ℕ → ℝ → ℕ)
    (r : ℕ) (hr : 2 ≤ r) (β : ℝ) (hβ : 0 < β)
    (hcore : ∃ d₀ : ℝ, 0 < d₀ ∧
      FreedmanCardExplicitSplitCore p c lam T r β ((1 : ℝ) / 100)
        (min (β / 4) ((1 : ℝ) / 100)) d₀ 1) :
    ∃ μ : ℝ, 0 < μ ∧ ∃ η : ℝ, 0 < η ∧ ∃ d₀ : ℝ, 0 < d₀ ∧
      ∃ K : ℝ, 0 < K ∧
      ∀ {V : Type} [Fintype V] [DecidableEq V] (H : Finset (Finset V)) (d : ℝ), 0 < d → d₀ ≤ d →
        IsUniform H r → NearlyRegularMost H d μ η → CodegreeBounded H (μ * d) →
        (∀ x : V, (degree H x : ℝ) ≤ (1 + μ) * d) →
        (Fintype.card V : ℝ) ≤ K * d ^ 2 →
        ∃ (Δ : ℕ) (p c lam : ℝ) (T : ℕ),
          0 ≤ p ∧ p ≤ 1 ∧ 0 < p ∧ 0 < Δ ∧ 0 < c ∧
          0 ≤ 1 - (r : ℝ) * Δ * p ∧ lam ≤ 1 ∧ 0 ≤ lam ∧ (∀ x, degree H x ≤ Δ) ∧ lam ^ T ≤ β ∧
          (∀ H' : Finset (Finset V), IsUniform H' r → (∀ x, degree H' x ≤ Δ) →
            (Fintype.card V : ℝ) * (2 * Real.exp (-c ^ 2 / (2 * ((Δ : ℝ) ^ 2 * ((r : ℝ) * Δ * p)
              + (Δ : ℝ) / 3 * c)))) < 1) ∧
          (∀ k, k < T →
            0 ≤ ((1 - μ) * d * (1 - (r : ℝ) * Δ * p) ^ k
                    - c * (∑ i ∈ Finset.range k, (1 - (r : ℝ) * Δ * p) ^ i))
                  * (p * (1 - p) ^ (r * Δ))
            ∧ (1 - lam) * (Fintype.card V : ℝ)
                ≤ (1 - η) * (Fintype.card V : ℝ)
                    * (((1 - μ) * d * (1 - (r : ℝ) * Δ * p) ^ k
                          - c * (∑ i ∈ Finset.range k, (1 - (r : ℝ) * Δ * p) ^ i))
                        * (p * (1 - p) ^ (r * Δ)))
                  - (r : ℝ) * freedmanPenalty V r Δ p c) := by
  refine nibble_params_exist_threshold_freedman_sized_of_threshold_core r hr β hβ ?_
  exact hcore.imp fun d₀ hd =>
    ⟨hd.1, freedmanSizedThresholdParameterCore_of_ceil (by norm_num)
      (freedmanCeilThresholdParameterCore_of_numeric
        (freedmanCeilNumericThresholdParameterCore_of_card
          (freedmanCardNumericThresholdParameterCore_of_explicit
            (freedmanCardExplicitParameterCore_of_split hd.2))))⟩

/-- Mechanical conversion from the proxy/inequality split explicit cardinality core to the sized
threshold core. This keeps later assembly lemmas from repeating the fully expanded conclusion. -/
theorem freedmanSizedThresholdParameterCore_of_proxy_ineq
    (p c lam : ℕ → ℝ → ℕ → ℝ → ℝ) (T : ℕ → ℝ → ℕ → ℝ → ℕ)
    {r : ℕ} {β μ η d₀ K : ℝ}
    (hμ : 0 < μ)
    (hcore : FreedmanCardExplicitSplitProxyIneqCore p c lam T r β μ η d₀ K) :
    FreedmanSizedThresholdParameterCore r β μ η d₀ K :=
  freedmanSizedThresholdParameterCore_of_ceil hμ
    (freedmanCeilThresholdParameterCore_of_numeric
      (freedmanCeilNumericThresholdParameterCore_of_card
        (freedmanCardNumericThresholdParameterCore_of_explicit
          (freedmanCardExplicitParameterCore_of_split
            (freedmanCardExplicitSplitCore_of_factored
              (freedmanCardExplicitSplitFactoredCore_of_proxyIneq hcore))))))

/-- `NibbleTheoremMostCeilSized` assembled directly from the pure Freedman parameter core. This is
the axiom-clean interface to the probabilistic/deterministic plumbing: the remaining mathematical
work is exactly the real-analytic parameter choice named by `FreedmanSizedParameterCore`. -/
theorem nibbleTheoremMostCeilSized_of_freedman_core
    (hcore : ∀ r : ℕ, 2 ≤ r → ∀ β : ℝ, 0 < β →
      FreedmanSizedParameterCore r β ((1 : ℝ) / 100)
        (min (β / 4) ((1 : ℝ) / 100)) 1) :
    NibbleTheoremMostCeilSized := by
  intro r hr β hβ
  obtain ⟨μ, hμ, η, hη, d₀, hd₀, K, hK, hP⟩ :=
    nibble_params_exist_threshold_freedman_sized_of_core r hr β hβ (hcore r hr β hβ)
  refine ⟨μ, hμ, η, hη, d₀, hd₀, K, hK, ?_⟩
  intro V _ _ H d hd hd0 huni hreg hcodeg hceil hsize
  obtain ⟨Δ, p, c, lam, T, hp0, hp1, hppos, hΔ0, hc, hq, hlam1, hlam0, hdeg0, hTβ, hsmall, hcrux⟩ :=
    hP H d hd hd0 huni hreg hcodeg hceil hsize
  have hr1 : 1 ≤ r := le_trans (by norm_num) hr
  have hVpos : ∀ H' : Finset (Finset V), IsUniform H' r → (∀ x, degree H' x ≤ Δ) →
      ∀ v : V, 0 < degree H' v →
        0 < (∑ e ∈ H'.filter (fun f => v ∈ f),
            (((H'.filter (fun f => v ∈ f)).filter
              (fun e' => ¬ Disjoint (depNbhd H' e) (depNbhd H' e'))).card : ℝ)) * ((r : ℝ) * Δ * p) := by
    intro H' _huni' _hdeg'
    exact active_residualDeg_proxy_pos (H := H') (r := r) (Δ := Δ) (p := p) hr1 hΔ0 hppos
  exact exists_matching_of_oracle_lt
    (nibbleStrategyFreedman_subset r Δ p c hp0 hp1 hr1 hΔ0 hc hVpos hsmall)
    huni hr1 hlam0 hβ T hTβ
    (oracle_of_crux_freedman r Δ p c d μ η lam T hp0 hp1 hr1 hΔ0 hc hVpos hsmall hq hlam1
      H huni hdeg0 hreg hcrux)

/-- `NibbleTheoremMostCeilSized` assembled directly from the thresholded pure Freedman parameter core.
This is the axiom-clean interface with the right asymptotic shape: the remaining mathematical work is
only to choose Freedman parameters above a degree threshold. -/
theorem nibbleTheoremMostCeilSized_of_freedman_threshold_core
    (hcore : ∀ r : ℕ, 2 ≤ r → ∀ β : ℝ, 0 < β →
      ∃ d₀ : ℝ, 0 < d₀ ∧
        FreedmanSizedThresholdParameterCore r β ((1 : ℝ) / 100)
          (min (β / 4) ((1 : ℝ) / 100)) d₀ 1) :
    NibbleTheoremMostCeilSized := by
  intro r hr β hβ
  obtain ⟨μ, hμ, η, hη, d₀, hd₀, K, hK, hP⟩ :=
    nibble_params_exist_threshold_freedman_sized_of_threshold_core r hr β hβ (hcore r hr β hβ)
  refine ⟨μ, hμ, η, hη, d₀, hd₀, K, hK, ?_⟩
  intro V _ _ H d hd hd0 huni hreg hcodeg hceil hsize
  obtain ⟨Δ, p, c, lam, T, hp0, hp1, hppos, hΔ0, hc, hq, hlam1, hlam0, hdeg0, hTβ, hsmall, hcrux⟩ :=
    hP H d hd hd0 huni hreg hcodeg hceil hsize
  have hr1 : 1 ≤ r := le_trans (by norm_num) hr
  have hVpos : ∀ H' : Finset (Finset V), IsUniform H' r → (∀ x, degree H' x ≤ Δ) →
      ∀ v : V, 0 < degree H' v →
        0 < (∑ e ∈ H'.filter (fun f => v ∈ f),
            (((H'.filter (fun f => v ∈ f)).filter
              (fun e' => ¬ Disjoint (depNbhd H' e) (depNbhd H' e'))).card : ℝ)) * ((r : ℝ) * Δ * p) := by
    intro H' _huni' _hdeg'
    exact active_residualDeg_proxy_pos (H := H') (r := r) (Δ := Δ) (p := p) hr1 hΔ0 hppos
  exact exists_matching_of_oracle_lt
    (nibbleStrategyFreedman_subset r Δ p c hp0 hp1 hr1 hΔ0 hc hVpos hsmall)
    huni hr1 hlam0 hβ T hTβ
    (oracle_of_crux_freedman r Δ p c d μ η lam T hp0 hp1 hr1 hΔ0 hc hVpos hsmall hq hlam1
      H huni hdeg0 hreg hcrux)

/-- `NibbleTheoremMostCeilSized` from the final concrete bad-event/round-inequality residual. The
basic parameter facts and proxy nonnegativity are already discharged in this file. -/
theorem nibbleTheoremMostCeilSized_of_freedman_concrete_badRound
    (hBadRound : ∀ r : ℕ, 2 ≤ r → ∀ β : ℝ, 0 < β →
      ∃ d₀ : ℝ, 0 < d₀ ∧
        FreedmanCardExplicitBadRoundCore freedmanExplicitP freedmanExplicitC freedmanExplicitLam
          freedmanExplicitT r β ((1 : ℝ) / 100)
          (min (β / 4) ((1 : ℝ) / 100)) d₀ 1) :
    NibbleTheoremMostCeilSized := by
  refine nibbleTheoremMostCeilSized_of_freedman_threshold_core ?_
  intro r hr β hβ
  obtain ⟨dR, hdR, hR⟩ := hBadRound r hr β hβ
  refine ⟨max 1 dR, lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_left _ _), ?_⟩
  refine freedmanSizedThresholdParameterCore_of_proxy_ineq
    freedmanExplicitP freedmanExplicitC freedmanExplicitLam freedmanExplicitT (by norm_num) ?_
  refine freedmanCardExplicitSplitProxyIneqCore_of_badRound ?_ ?_ ?_
  · intro N d hd hd0 hsize
    exact freedmanExplicitBasicCore r hr β hβ N d hd (le_trans (le_max_left 1 dR) hd0) hsize
  · intro N d hd hd0 hsize
    exact freedmanExplicitDegreeProxyNonnegCore r β N d hd
      (le_trans (le_max_left 1 dR) hd0) hsize
  · refine ⟨?_, ?_⟩
    · intro N d hd hd0 hsize
      exact hR.1 N d hd (le_trans (le_max_right 1 dR) hd0) hsize
    · intro N d hd hd0 hsize
      exact hR.2 N d hd (le_trans (le_max_right 1 dR) hd0) hsize

/-- `NibbleTheoremMostCeilSized` assembled directly from a split explicit cardinal Freedman core. -/
theorem nibbleTheoremMostCeilSized_of_freedman_split_explicit_core
    (p c lam : ℕ → ℝ → ℕ → ℝ → ℝ) (T : ℕ → ℝ → ℕ → ℝ → ℕ)
    (hcore : ∀ r : ℕ, 2 ≤ r → ∀ β : ℝ, 0 < β →
      ∃ d₀ : ℝ, 0 < d₀ ∧
        FreedmanCardExplicitSplitCore p c lam T r β ((1 : ℝ) / 100)
          (min (β / 4) ((1 : ℝ) / 100)) d₀ 1) :
    NibbleTheoremMostCeilSized := by
  exact nibbleTheoremMostCeilSized_of_freedman_threshold_core
    (fun r hr β hβ =>
      (hcore r hr β hβ).imp fun d₀ hd =>
        ⟨hd.1, freedmanSizedThresholdParameterCore_of_ceil (by norm_num)
          (freedmanCeilThresholdParameterCore_of_numeric
            (freedmanCeilNumericThresholdParameterCore_of_card
              (freedmanCardNumericThresholdParameterCore_of_explicit
                (freedmanCardExplicitParameterCore_of_split hd.2))))⟩)

end Nibble

/-
# Nibble — T3 discharge (part 1) : the covered-count recurrence

Standalone, Mathlib-only. Toward discharging `NibbleTheorem`, the deterministic accounting of how
many vertices the accumulated nibble matching covers. The cross-round invariant (D3,
`nibbleResidual_disjoint_support`) makes each new round's support DISJOINT from all previously
covered vertices, so the covered count is *exactly additive* across rounds:

  `|support(nibbleMatching R H (k+1))| = |support(nibbleMatching R H k)| + |support(round k)|`.

This is the `a(k+1) = a k - b k` half of the convergence chain (`Nibble.uncovered_step`): the
uncovered count drops by exactly the amount covered in round `k`. The per-round covering *fraction*
(the probabilistic half, `hcov`) plugs in on top.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.Basic
import Nibble.Greedy
import Nibble.Round
import Nibble.Iteration
import Nibble.Assemble
import Nibble.Convergence
import Mathlib.Analysis.RCLike.Basic

open Finset

namespace Hypergraph

variable {V : Type*} [DecidableEq V]

/-- The new round's support is disjoint from the accumulated support (cross-round invariant, D3). -/
theorem support_round_disjoint_support_acc {R : Finset (Finset V) → Finset (Finset V)}
    (hR : ∀ H', R H' ⊆ H') (H : Finset (Finset V)) (k : ℕ) :
    Disjoint (support (nibbleMatching R H k))
      (support (roundMatching (R (nibbleResidual R H k)))) := by
  rw [Finset.disjoint_left]
  intro x hxacc hxround
  rw [support, Finset.mem_biUnion] at hxround
  obtain ⟨e, heround, hxe⟩ := hxround
  -- e ∈ round k ⊆ R (residual k) ⊆ residual k
  have heres : e ∈ nibbleResidual R H k := (hR _) (roundMatching_subset _ heround)
  exact (Finset.disjoint_left.mp
    (nibbleResidual_disjoint_support (R := R) H k e heres) hxe) hxacc

/-- **T3 discharge(1) — covered-count recurrence.** The accumulated nibble matching covers exactly
`|support(round k)|` *new* vertices in round `k`: covered counts add across rounds. -/
theorem nibbleMatching_support_card_succ {R : Finset (Finset V) → Finset (Finset V)}
    (hR : ∀ H', R H' ⊆ H') (H : Finset (Finset V)) (k : ℕ) :
    (support (nibbleMatching R H (k + 1))).card
      = (support (nibbleMatching R H k)).card
        + (support (roundMatching (R (nibbleResidual R H k)))).card := by
  have hunion : nibbleMatching R H (k + 1)
      = nibbleMatching R H k ∪ roundMatching (R (nibbleResidual R H k)) := rfl
  rw [hunion, support_union,
    Finset.card_union_of_disjoint (support_round_disjoint_support_acc hR H k)]

/-- **T3 discharge(2) — reduction of `NibbleTheorem` to a per-round covering oracle.** If the
retention strategy `R` keeps edges inside their input (`hR`), and each round covers at least a
`(1-λ)` fraction of the currently-uncovered vertices (the `horacle` hypothesis — precisely what the
probabilistic good-event step supplies), then for any target `β > 0` some round count `T` yields an
accumulated matching covering `≥ (1-β)·|V|`, hence of size `≥ (1-β)·(|V|/r)` — the `NibbleTheorem`
conclusion. This isolates the deterministic accounting from the probabilistic per-round input. -/
theorem nibble_matching_card_of_oracle [Fintype V]
    {R : Finset (Finset V) → Finset (Finset V)} (hR : ∀ H', R H' ⊆ H')
    {H : Finset (Finset V)} {r : ℕ} (hr : IsUniform H r) (hr1 : 1 ≤ r)
    {lam β : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam < 1) (hβ : 0 < β)
    (horacle : ∀ k,
      (1 - lam) * ((Fintype.card V : ℝ) - ((support (nibbleMatching R H k)).card : ℝ))
        ≤ ((support (roundMatching (R (nibbleResidual R H k)))).card : ℝ)) :
    ∃ T, (1 - β) * ((Fintype.card V : ℝ) / r) ≤ ((nibbleMatching R H T).card : ℝ) := by
  have hann : ∀ k, 0 ≤ (Fintype.card V : ℝ) - ((support (nibbleMatching R H k)).card : ℝ) := by
    intro k
    have : ((support (nibbleMatching R H k)).card : ℝ) ≤ (Fintype.card V : ℝ) := by
      exact_mod_cast Finset.card_le_univ _
    linarith
  have hstep : ∀ k,
      (Fintype.card V : ℝ) - ((support (nibbleMatching R H (k + 1))).card : ℝ)
        ≤ ((Fintype.card V : ℝ) - ((support (nibbleMatching R H k)).card : ℝ))
          - ((support (roundMatching (R (nibbleResidual R H k)))).card : ℝ) := by
    intro k
    have hrec : ((support (nibbleMatching R H (k + 1))).card : ℝ)
        = ((support (nibbleMatching R H k)).card : ℝ)
          + ((support (roundMatching (R (nibbleResidual R H k)))).card : ℝ) := by
      exact_mod_cast nibbleMatching_support_card_succ hR H k
    linarith
  obtain ⟨T, hT⟩ := Nibble.exists_uncovered_below hlam0 hlam1 hβ hann hstep horacle
  have h0 : (support (nibbleMatching R H 0)).card = 0 := by
    simp [show nibbleMatching R H 0 = (∅ : Finset (Finset V)) from rfl, support, Finset.biUnion_empty]
  rw [h0] at hT
  simp only [Nat.cast_zero, sub_zero] at hT
  refine ⟨T, ?_⟩
  have hM : IsMatching H (nibbleMatching R H T) := nibbleMatching_isMatching hR H T
  have hsc : ((support (nibbleMatching R H T)).card : ℝ)
      = (r : ℝ) * ((nibbleMatching R H T).card : ℝ) := by
    exact_mod_cast matching_support_card hr hM
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr1
  rw [← mul_div_assoc, div_le_iff₀ hrpos]
  nlinarith only [hT, hsc]

/-- **T3 discharge(3) — oracle ⇒ the `NibbleTheorem` per-instance conclusion.** Given the strategy
`R` (keeping edges) and the per-round covering oracle, there is a *matching* of `H` covering at least
`(1-β)·(|V|/r)` — the exact `∃ M, IsMatching H M ∧ …` conclusion of `NibbleTheorem` (before the outer
`∃ μ`). Combines the covered-count bound (`nibble_matching_card_of_oracle`) with the fact that the
accumulated matching is a matching (`nibbleMatching_isMatching`). -/
theorem exists_matching_of_oracle [Fintype V]
    {R : Finset (Finset V) → Finset (Finset V)} (hR : ∀ H', R H' ⊆ H')
    {H : Finset (Finset V)} {r : ℕ} (hr : IsUniform H r) (hr1 : 1 ≤ r)
    {lam β : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam < 1) (hβ : 0 < β)
    (horacle : ∀ k,
      (1 - lam) * ((Fintype.card V : ℝ) - ((support (nibbleMatching R H k)).card : ℝ))
        ≤ ((support (roundMatching (R (nibbleResidual R H k)))).card : ℝ)) :
    ∃ M : Finset (Finset V), IsMatching H M
      ∧ (1 - β) * ((Fintype.card V : ℝ) / r) ≤ (M.card : ℝ) := by
  obtain ⟨T, hT⟩ := nibble_matching_card_of_oracle hR hr hr1 hlam0 hlam1 hβ horacle
  exact ⟨nibbleMatching R H T, nibbleMatching_isMatching hR H T, hT⟩

/-- **T3 discharge — bounded-rounds oracle ⇒ covered count.** The fix to `_of_oracle`: the covering
oracle is required only for the rounds `k < T` (during which the residual is still near-regular), and
`T` with `λ^T ≤ β` is taken as data. Then `nibbleMatching R H T` covers `≥ (1-β)·(|V|/r)`. This is
the dischargeable form — the unbounded `∀ k` oracle is impossible since the covering fraction `→ 0`. -/
theorem nibble_matching_card_of_oracle_lt [Fintype V]
    {R : Finset (Finset V) → Finset (Finset V)} (hR : ∀ H', R H' ⊆ H')
    {H : Finset (Finset V)} {r : ℕ} (hr : IsUniform H r) (hr1 : 1 ≤ r)
    {lam β : ℝ} (hlam0 : 0 ≤ lam) (hβ : 0 < β) (T : ℕ) (hTβ : lam ^ T ≤ β)
    (horacle : ∀ k, k < T →
      (1 - lam) * ((Fintype.card V : ℝ) - ((support (nibbleMatching R H k)).card : ℝ))
        ≤ ((support (roundMatching (R (nibbleResidual R H k)))).card : ℝ)) :
    (1 - β) * ((Fintype.card V : ℝ) / r) ≤ ((nibbleMatching R H T).card : ℝ) := by
  have hann : ∀ k, 0 ≤ (Fintype.card V : ℝ) - ((support (nibbleMatching R H k)).card : ℝ) := by
    intro k
    have : ((support (nibbleMatching R H k)).card : ℝ) ≤ (Fintype.card V : ℝ) := by
      exact_mod_cast Finset.card_le_univ _
    linarith
  have hstep : ∀ k, k < T →
      (Fintype.card V : ℝ) - ((support (nibbleMatching R H (k + 1))).card : ℝ)
        ≤ ((Fintype.card V : ℝ) - ((support (nibbleMatching R H k)).card : ℝ))
          - ((support (roundMatching (R (nibbleResidual R H k)))).card : ℝ) := by
    intro k _
    have hrec : ((support (nibbleMatching R H (k + 1))).card : ℝ)
        = ((support (nibbleMatching R H k)).card : ℝ)
          + ((support (roundMatching (R (nibbleResidual R H k)))).card : ℝ) := by
      exact_mod_cast nibbleMatching_support_card_succ hR H k
    linarith
  have hconv := Nibble.uncovered_below_lt hlam0 hann T hTβ hstep horacle
  have h0 : (support (nibbleMatching R H 0)).card = 0 := by
    simp [show nibbleMatching R H 0 = (∅ : Finset (Finset V)) from rfl, support, Finset.biUnion_empty]
  rw [h0] at hconv
  simp only [Nat.cast_zero, sub_zero] at hconv
  have hM : IsMatching H (nibbleMatching R H T) := nibbleMatching_isMatching hR H T
  have hsc : ((support (nibbleMatching R H T)).card : ℝ)
      = (r : ℝ) * ((nibbleMatching R H T).card : ℝ) := by
    exact_mod_cast matching_support_card hr hM
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr1
  rw [← mul_div_assoc, div_le_iff₀ hrpos]
  nlinarith only [hconv, hsc]

/-- **Bounded-rounds oracle ⇒ `NibbleTheorem` conclusion.** As `exists_matching_of_oracle` but with
the dischargeable bounded oracle. -/
theorem exists_matching_of_oracle_lt [Fintype V]
    {R : Finset (Finset V) → Finset (Finset V)} (hR : ∀ H', R H' ⊆ H')
    {H : Finset (Finset V)} {r : ℕ} (hr : IsUniform H r) (hr1 : 1 ≤ r)
    {lam β : ℝ} (hlam0 : 0 ≤ lam) (hβ : 0 < β) (T : ℕ) (hTβ : lam ^ T ≤ β)
    (horacle : ∀ k, k < T →
      (1 - lam) * ((Fintype.card V : ℝ) - ((support (nibbleMatching R H k)).card : ℝ))
        ≤ ((support (roundMatching (R (nibbleResidual R H k)))).card : ℝ)) :
    ∃ M : Finset (Finset V), IsMatching H M
      ∧ (1 - β) * ((Fintype.card V : ℝ) / r) ≤ (M.card : ℝ) :=
  ⟨nibbleMatching R H T, nibbleMatching_isMatching hR H T,
    nibble_matching_card_of_oracle_lt hR hr hr1 hlam0 hβ T hTβ horacle⟩

end Hypergraph

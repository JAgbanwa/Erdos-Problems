/-
# Nibble — the **portion budget** of the banded block-allocation route

The bridge from the near-uniform coupled block cover
(`Nibble.AX1.blockCoverResidualCoupledNearUniform_holds`, `Nibble.CoreGapBlockCoverUniform`) to
general cluster densities is supposed to band the densities geometrically
(`Nibble.AX1.exists_density_band`, `Nibble.AX1.density_band_count_le`), run the near-uniform
construction inside every band profile, and add up the profiles.  Adding them up needs the block
families of different profiles to have **disjoint rectangles**, and the only mechanism available
for that is to give each cluster `S` one *portion* per band, cut into slots of the length that band
prescribes: the block a member puts in `S` has size `τ·(density of the opposite pair)`, so a member
of band `b` at `S` needs a slot of length `≈ τ·δ(1+ρ)^b`.

This file isolates the arithmetic of that allocation and shows that **the budget genuinely
overruns**.  Write, for a cluster pair `(S, T)` of the reduced cluster graph:

* `f b` — the fraction of `S` given to the band-`b` portion (so `∑ b, f b ≤ 1`);
* `g b` — the same fraction for `T`;
* `a b` — the fraction of the `#S × #T` rectangle that the profiles with band `b` at both `S`
  and `T` have to carry (the LP mass of those profiles, divided by the density of `(S, T)`).

A member of band `b` at `S` and band `b'` at `T` occupies a `λ_b × λ_{b'}` rectangle, and the
band-`(b, b')` members can only use slot pairs coming from the two portions, so their rectangles
live inside a `f b · #S` by `g b' · #T` sub-rectangle: the scheme can serve the demand only if

  `a b ≤ f b * g b`   for every band `b`.                                   (★)

The LP itself only bounds the *total* demand, `∑ b, a b ≤ 1`.  The two constraints do not match:
`(★)` forces `∑ b, √(a b) ≤ 1` (`Nibble.AX1.portion_budget_sqrt_le`), which for the flat demand
`a b = c/n` spread over `n` bands forces `c ≤ 1/n` (`Nibble.AX1.portion_budget_served_le`), i.e. the
portion scheme serves at most a `1/n` fraction of an LP-feasible demand, and for `n ≥ 2` it cannot
serve the perfectly LP-feasible demand `a b = 1/n` at all
(`Nibble.AX1.portion_budget_overrun`).

Since `n` is the number of density bands meeting `[δ, 1]` — `n ≈ log(1/δ)/log(1 + ρ)`, and `ρ` has
to be small for a band to be near-uniform — the profile-summed covering inequality coming out of
the route is weaker than the one `Nibble.AX1.BlockCoverResidualCoupled` asks for by the factor `n`,
which is not an `ε`-sized loss.  The obstruction is to *this route*, not to the residual itself:
the demand `(★)` is only what the *product-region* (one portion per cluster per band) allocation
can serve, and a genuinely multi-scale allocation is not subject to it.  See
`AX1_GeneralDensity_Report.md` for the full analysis, for a density configuration realising the
flat demand, and for the two special regimes in which the route does close.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Real.StarOrdered
import Mathlib.Tactic.Positivity

open Finset

namespace Nibble.AX1

/-- **The portion budget of one cluster pair.**  `PortionBudgetServes n c` says that the
band-portion allocation can serve, on a single cluster pair, the flat demand that asks each of the
`n` bands for a `c/n` fraction of the pair's rectangle — a demand of total size `c`, hence
LP-feasible as soon as `c ≤ 1`.

`f b`, `g b` are the fractions of the two clusters given to their band-`b` portions; the band-`b`
members of the pair can only use slot pairs from those two portions, so they can carry at most an
`f b * g b` fraction of the pair's rectangle. -/
def PortionBudgetServes (n : ℕ) (c : ℝ) : Prop :=
  ∃ f g : Fin n → ℝ, (∀ b, 0 ≤ f b) ∧ (∀ b, 0 ≤ g b) ∧
    (∑ b, f b) ≤ 1 ∧ (∑ b, g b) ≤ 1 ∧ ∀ b, c / (n : ℝ) ≤ f b * g b

/-- **The exact inequality the portion allocation obeys.**  If the band-`b` demand `a b` is served
inside the product of the two band-`b` portions, then the *square roots* of the demands sum to at
most `1` — while LP feasibility of the demand only says that the demands themselves sum to at
most `1`. -/
theorem portion_budget_sqrt_le {n : ℕ} (f g a : Fin n → ℝ)
    (hf : ∀ b, 0 ≤ f b) (hg : ∀ b, 0 ≤ g b)
    (hfs : (∑ b, f b) ≤ 1) (hgs : (∑ b, g b) ≤ 1)
    (ha : ∀ b, a b ≤ f b * g b) :
    (∑ b, Real.sqrt (a b)) ≤ 1 := by
  have hterm : ∀ b : Fin n, Real.sqrt (a b) ≤ (f b + g b) / 2 := by
    intro b
    have h1 : Real.sqrt (a b) ≤ Real.sqrt (f b * g b) :=
      Real.sqrt_le_sqrt (ha b)
    have h2 : Real.sqrt (f b * g b) ≤ (f b + g b) / 2 := by
      have hle : f b * g b ≤ ((f b + g b) / 2) ^ 2 := by linarith only [sq_nonneg (f b - g b)]
      calc Real.sqrt (f b * g b) ≤ Real.sqrt (((f b + g b) / 2) ^ 2) := Real.sqrt_le_sqrt hle
        _ = (f b + g b) / 2 := Real.sqrt_sq (by linarith only [hf b, hg b])
    linarith
  calc (∑ b, Real.sqrt (a b)) ≤ ∑ b, (f b + g b) / 2 := Finset.sum_le_sum fun b _ => hterm b
    _ = ((∑ b, f b) + (∑ b, g b)) / 2 := by
        rw [← Finset.sum_add_distrib, ← Finset.sum_div]
    _ ≤ 1 := by linarith

/-- **The portion budget serves at most a `1/n` fraction.**  Over `n ≥ 1` bands, the flat demand of
total size `c` — which the cluster LP admits for every `c ≤ 1` — is served by the band-portion
allocation only if `c ≤ 1/n`. -/
theorem portion_budget_served_le {n : ℕ} (hn : 0 < n) {c : ℝ} (hc : 0 ≤ c)
    (h : PortionBudgetServes n c) : c ≤ 1 / (n : ℝ) := by
  obtain ⟨f, g, hf, hg, hfs, hgs, hserve⟩ := h
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hkey := portion_budget_sqrt_le f g (fun _ => c / (n : ℝ)) hf hg hfs hgs hserve
  have hconst : (∑ _b : Fin n, Real.sqrt (c / (n : ℝ)))
      = (n : ℝ) * Real.sqrt (c / (n : ℝ)) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hconst] at hkey
  have hs0 : 0 ≤ Real.sqrt (c / (n : ℝ)) := Real.sqrt_nonneg _
  have hsq : Real.sqrt (c / (n : ℝ)) ^ 2 = c / (n : ℝ) :=
    Real.sq_sqrt (by positivity)
  -- `n · √(c/n) ≤ 1` squares to `c · n ≤ 1`
  have hsqr : ((n : ℝ) * Real.sqrt (c / (n : ℝ))) ^ 2 ≤ 1 := by
    nlinarith only [hkey, mul_nonneg hn0.le hs0]
  have hexp : ((n : ℝ) * Real.sqrt (c / (n : ℝ))) ^ 2 = (n : ℝ) * c := by
    rw [mul_pow, hsq]
    field_simp
  rw [hexp] at hsqr
  rw [le_div_iff₀ hn0]
  linarith

/-- **The portion budget overruns.**  From two bands on, the band-portion allocation cannot serve
the flat demand of total size `1` — the demand that a single cluster pair, saturated by two band
profiles in equal parts, presents.  This is the exact inequality that stops the
band-profile route to `Nibble.AX1.BlockCoverResidualCoupled`: `1 ≤ 1/n` fails for `n ≥ 2`. -/
theorem portion_budget_overrun {n : ℕ} (hn : 2 ≤ n) : ¬ PortionBudgetServes n 1 := by
  intro h
  have h1 : (1 : ℝ) ≤ 1 / (n : ℝ) := portion_budget_served_le (by omega) zero_le_one h
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  rw [le_div_iff₀ (by linarith)] at h1
  linarith

/-! ### The one-sided (oriented) variant

Two rectangles are disjoint as soon as they are disjoint in **one** coordinate, so a cluster pair
can also be served by splitting only *one* of its two clusters into portions and leaving the other
one whole: the profiles present at the pair are then separated by the split side alone, and the
demand constraint weakens from `a π ≤ f π (S) * f π (T)` to `a π ≤ f π (S)`.  This is strictly
better than the product allocation — but each pair must now name the cluster it is separated at,
and a cluster that is named by two pairs with different profile demands has to host both.  Three
profiles asking for half of a cluster each already break the budget. -/
theorem oriented_portion_budget_overrun {ι : Type} [DecidableEq ι] (f : ι → ℝ)
    (hf : ∀ p, 0 ≤ f p) (s t : Finset ι) (hts : t ⊆ s)
    (hsum : (∑ p ∈ s, f p) ≤ 1) (hcard : 3 ≤ #t) (hhalf : ∀ p ∈ t, 1 / 2 ≤ f p) :
    False := by
  have h1 : (∑ p ∈ t, f p) ≤ ∑ p ∈ s, f p :=
    Finset.sum_le_sum_of_subset_of_nonneg hts fun p _ _ => hf p
  have h2 : (#t : ℝ) * (1 / 2) ≤ ∑ p ∈ t, f p := by
    have := Finset.sum_le_sum (f := fun _ : ι => (1 : ℝ) / 2) (g := f) (s := t)
      (fun p hp => hhalf p hp)
    rwa [Finset.sum_const, nsmul_eq_mul] at this
  have h3 : (3 : ℝ) ≤ (#t : ℝ) := by exact_mod_cast hcard
  linarith

/-! ### Axiom check -/

section AxCheck

#print axioms Nibble.AX1.portion_budget_sqrt_le
#print axioms Nibble.AX1.portion_budget_served_le
#print axioms Nibble.AX1.portion_budget_overrun
#print axioms Nibble.AX1.oriented_portion_budget_overrun

end AxCheck

end Nibble.AX1

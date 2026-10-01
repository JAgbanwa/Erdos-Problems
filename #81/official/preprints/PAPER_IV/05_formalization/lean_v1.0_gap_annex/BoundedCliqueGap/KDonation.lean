import BoundedCliqueGap.JRelative

/-
`BoundedCliqueGap.KDonation` — declaration-level extract of the Route B
triangle-packing development.  Only the declarations in the constant cone of
`BoundedCliqueGap.chordal_gap_linear_cliqueFree` were kept (plus the few that
the retained sources need in order to elaborate); the module documentation
below is the original one and may advertise results that were pruned away.
-/

/-
# Rung K1/K2 — the RELATIVE list-donation: what the shell gap really needs

This file replaces the *lossy* J1 objective by the accounting that actually
closes the shell gap, and isolates the two hypotheses on which it rests.

## The accounting

For a fractional packing `F` of a shell, every triangle is either a **hub**
triangle (three hub vertices) or a **port** triangle (a hub edge plus one
port), because ports are pairwise non-adjacent.  So

    value F = hubMass F + portMass F                (`shell_value_eq_hub_add_port`)

with `portMass F = ∑ₑ ∑ₓ y e x` the donation mass of `shellDonation`.

Suppose a set `K` of hub edges has been *donated*: each `e ∈ K` has an owner
port `owner e` admitting it, and the fibres of `owner` are matchings of the
hub (`IsShellDonation`).  Then

* the `K`-donated port triangles are pairwise edge-disjoint, and they are
  edge-disjoint from every triangle of the **residual hub graph**
  `hubGraph S0 K` (the hub, minus the interior of the hole, minus the donated
  slots), whence
      `#K + ν₃(hubGraph S0 K) ≤ ν₃(shell)`      (`nu3_shell_ge_donation`);
* the hub mass splits: hub triangles avoiding `K` form a fractional packing of
  `hubGraph S0 K` (`residualHubPacking`), and the hub mass through a donated
  slot `e` is at most `1 − ∑ₓ y e x`, since the slot's capacity is shared with
  the donation (`hubMass_le_residual_add_donated`,
  `hubThrough_add_donation_le_one`).

Adding the two lines, **all `#K` and all donated mass cancel** and what
survives is exactly

    value F ≤ ν₃(shell) + (undonated port mass) + (integrality gap of the
                                                   residual hub graph)

(`shell_gap_of_donation`).  This is the corrected form of the K1 → K2 step.

## Honest note on the `2/3` rebate

The transfer form suggested for K1 (`∑ y ≤ kept + (2/3)·discarded + C(κ+t)`)
is **not** sufficient for K2, and the master inequality above shows why: what
multiplies the *discarded* mass in the final bound is `1`, not `1/3`.  A hub
edge that is taken back by the hub returns to the Bose packing at `1/3` of a
triangle (three edges per block), not `2/3`; the `2/3` is the *marginal gain*
of donating an edge, i.e. it sits on the other side of the ledger.  Since
`∑ₑ ∑ₓ y e x ≤ #E` holds for free (each hub slot has capacity one), the
suggested transfer form is in fact equivalent to `#discarded ≤ 3·slack +
3C(κ+t)`, and the derivation above turns any such discard into a *full* unit
of gap.  The corrected objective is therefore a **lossless** donation: all but
`C·(κ − |S₀| + t)` of the port mass must be donated.  See `REPORT_K.md`.
-/

namespace BoundedCliqueGap

open Finset

section KDon

variable {kappa t m : ℕ} {S0 : Finset (Fin kappa)} {terr : Fin t → Fin m}
  {S : Fin m → Finset (Fin kappa)}

/-! ## The hub mass of a fractional packing of the shell -/

/-! ## The residual hub graph and the donation -/

/-- The **residual hub graph**: the hub clique with the interior of the hole
`S₀` deleted and with the donated slots `K` deleted as well. -/
def hubGraph (S0 : Finset (Fin kappa)) (K : Finset (Finset (Fin kappa))) :
    SimpleGraph (Fin kappa) where
  Adj a b := a ≠ b ∧ ¬ (a ∈ S0 ∧ b ∈ S0) ∧ ({a, b} : Finset (Fin kappa)) ∉ K
  symm := by
    rintro a b ⟨h1, h2, h3⟩
    refine ⟨h1.symm, fun hc => h2 ⟨hc.2, hc.1⟩, ?_⟩
    rwa [Finset.pair_comm]
  loopless := by
    constructor
    intro a h
    exact h.1 rfl

@[simp] lemma hubGraph_adj {S0 : Finset (Fin kappa)} {K : Finset (Finset (Fin kappa))}
    {a b : Fin kappa} :
    (hubGraph S0 K).Adj a b ↔
      a ≠ b ∧ ¬ (a ∈ S0 ∧ b ∈ S0) ∧ ({a, b} : Finset (Fin kappa)) ∉ K := Iff.rfl

/-! ### Port triangles and hub triangles inside the shell -/

/-! ## The residual hub packing -/

/-! ## The undonated port mass and the master inequality -/

end KDon

/-! ## Axiom audit -/

end BoundedCliqueGap

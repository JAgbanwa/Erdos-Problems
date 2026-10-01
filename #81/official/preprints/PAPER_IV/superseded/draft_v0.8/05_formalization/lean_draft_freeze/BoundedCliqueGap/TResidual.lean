import BoundedCliqueGap.KShellFull
import BoundedCliqueGap.Transport

/-
`BoundedCliqueGap.TResidual` — declaration-level extract of the Route B
triangle-packing development.  Only the declarations in the constant cone of
`BoundedCliqueGap.chordal_gap_linear_cliqueFree` were kept (plus the few that
the retained sources need in order to elaborate); the module documentation
below is the original one and may advertise results that were pruned away.
-/

/-
# Rung T2 — the residual hub gap: the explicit form, and what the R1 repair
# really restricts

Rung R1 audited `ResidualHubGap` (it is the universal Tuza-type statement in
disguise) and offered `ResidualHubGapDonated`, the same Prop with `K` restricted
to the slot sets a shell donation can produce.  This module settles that
interface too.

* **The explicit form is a theorem** (`residualHubGap_donated_explicit`).  The
  residual hub graph is the hub-with-a-hole minus the donated slots; the
  hub-with-a-hole is a shell with no ports, whose gap is `10·(κ−|S₀|)`
  (`shell_gap_full_no_ports`), and deleting `|K|` slots costs at most `|K|`
  triangles of a packing (`nu3_hubGraph_empty_le`).  Hence, unconditionally,

    `F.value ≤ ν₃(hubGraph S₀ K) + |K| + 10·(κ−|S₀|)`,

  for every donation-shaped `K` (all slots of size two) and every fractional
  packing `F` of the residual.

* **The R1 repair restricts nothing** (`residualHubGapDonated_universal`).  The
  colouring `owner {a,b} = (a+b) mod κ` is a proper edge colouring of the
  complete hub, so *every* set of slots is donation-produced once `t = κ`
  ports are available — the quantitative restriction
  `card_le_of_isShellDonation` (`|K| ≤ t·⌊κ/2⌋`) is vacuous there because the
  conclusion of `ResidualHubGapDonated` does not mention `t`.  Consequently
  `ResidualHubGapDonated C` still asserts the linear integrality gap
  `ν₃* ≤ ν₃ + C·n` for **every** finite simple graph, exactly as
  `residualHubGap_universal` showed for the unrestricted form.  This is stated
  as an audit, not as a refutation.

* **The budget form is what the ladder can use**
  (`ResidualHubGapDonatedSparse`, `residualHubGapDonatedSparse`): once the
  number of donated slots fits inside the interface measure, the explicit form
  *is* the interface, at the constant `11`.
-/

namespace BoundedCliqueGap

open Finset

section Residual

variable {kappa : ℕ}

/-! ## The hub with a hole is a shell with no ports -/

/-- The residual hub graph with no donated slots is a shell with no ports, so
its gap is the `10·(κ−|S₀|)` of `shell_gap_full_no_ports`. -/
theorem hubGraph_hole_gap (S0 : Finset (Fin kappa))
    (F : FracPacking (hubGraph S0 (∅ : Finset (Finset (Fin kappa))))) :
    F.value ≤ (nu3 (hubGraph S0 (∅ : Finset (Finset (Fin kappa)))) : ℚ)
      + 10 * ((kappa - S0.card : ℕ) : ℚ) := by
  classical
  set terr : Fin 0 → Fin 1 := fun x => x.elim0 with hterr
  set S : Fin 1 → Finset (Fin kappa) := fun _ => (∅ : Finset (Fin kappa)) with hS
  refine gap_transfer (G := hubGraph S0 (∅ : Finset (Finset (Fin kappa))))
    (H := shell S0 terr S) (Equiv.sumEmpty (Fin kappa) (Fin 0)).symm ?_ _
    (fun F' => shell_gap_full_no_ports S0 terr S F') F
  intro u v
  simp [hubGraph_adj, Equiv.sumEmpty]

/-! ## Deleting the donated slots costs at most one triangle each -/

/-! ## The explicit residual gap -/

end Residual

/-! ## The budget form of the interface -/

/-! ## The R1 repair restricts nothing -/

namespace DonatedUniversal

open Finset

variable {kappa : ℕ}

end DonatedUniversal

/-! ## Axiom audit -/

end BoundedCliqueGap

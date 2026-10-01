import BoundedCliqueGap.KDonation

/-
`BoundedCliqueGap.KShellFull` — declaration-level extract of the Route B
triangle-packing development.  Only the declarations in the constant cone of
`BoundedCliqueGap.chordal_gap_linear_cliqueFree` were kept (plus the few that
the retained sources need in order to elaborate); the module documentation
below is the original one and may advertise results that were pruned away.
-/

/-
# Rung K1/K2/K3 — the packaged Props and the unconditional instances

Built on the master inequality `shell_gap_of_donation` of `BoundedCliqueGap/KDonation.lean`:

    value F ≤ ν₃(shell) + (undonated port mass) + (gap of the residual hub graph).

* **K1 (`LosslessListDonation`)** — the corrected abstract donation objective: a
  fractional admissible assignment `y` (edge loads `≤ 1`, per-port-per-hub-vertex
  loads `≤ 1`, supported on the lists and outside the hole's interior) can be
  rounded to an owner map with MATCHING fibres whose *undonated* mass is at most
  `C · ((κ − |S₀|) + t)`.  Losses are charged neither to the ports nor to the
  separators; they are charged to the hub's size, exactly as the audit asks.
  `exists_shell_donation_of_lossless` is the mechanical bridge: the donation
  `shellDonation F` of any fractional packing of a shell satisfies the two
  constraint families (`shellDonation_edge_le_one`,
  `shellDonation_vertex_le_one`), so K1 applies to it verbatim.

* **K2 (`ShellDonationHyp` → `ShellGapFull`)** — a donation that is lossless *and*
  leaves a residual hub graph of small integrality gap yields the full shell gap
  with no cross-mass residual (`shellGapFull_of_donationHyp`), and
  `shell_gap_rel_full` upgrades the relative form `shell_gap_rel` verbatim.

* **K3 (`ShellGapFull`)** — the named Prop, with exactly the signature the tree
  telescoping consumes: `κ`, `S₀`, `terr`, `S`, the constant `C`, and the
  measure `(κ − |S₀|) + Σᵢ pᵢ`.

* **Unconditional instances.**  `shell_gap_full_no_ports` (a shell with no ports)
  and `shell_gap_portRich_hole` (every hub slot admissible for more than `2κ`
  ports — now with an ARBITRARY hole `S₀`, where `shell_gap_portRich` needed
  `S₀ = ∅`).  The second is a new consequence of the master inequality: the
  whole hub is donated, so the residual hub graph is edgeless and *both* error
  terms vanish.

Honest status: `ShellGapFull` itself is **not** proved unconditionally; K1 is a
list-edge-colouring statement (see `REPORT_K.md` for the obstruction — with
arbitrary lists it is false, and the clique-shaped lists of a shell are exactly
what could save it).
-/

namespace BoundedCliqueGap

open Finset

/-! ## The per-port-per-vertex constraint of a shell donation -/

section VertexLoad

variable {kappa t m : ℕ} {S0 : Finset (Fin kappa)} {terr : Fin t → Fin m}
  {S : Fin m → Finset (Fin kappa)}

end VertexLoad

/-! ## K1 — the corrected list-donation objective -/

/-! ## K3 — the packaged Props -/

/-! ## The bridge from K1 to the shell -/

section Bridge

variable {kappa t m : ℕ} {S0 : Finset (Fin kappa)} {terr : Fin t → Fin m}
  {S : Fin m → Finset (Fin kappa)}

end Bridge

/-! ## K2 — the full shell gap from the donation hypothesis -/

/-! ## The corrected (aggregate) donation route

Since every *lossless* donation objective is refuted, the loss of a donation
must be charged against the hub rather than being forbidden.  The following
variant of the master inequality does exactly that: it never uses the slack
`1 − ∑ₓ y e x` of a donated slot, and compares the port mass with the *number*
of donated slots. -/

section Aggregate

variable {kappa t m : ℕ} {S0 : Finset (Fin kappa)} {terr : Fin t → Fin m}
  {S : Fin m → Finset (Fin kappa)}

end Aggregate

/-! ## Unconditional instances -/

section Instances

variable {kappa t m : ℕ} (S0 : Finset (Fin kappa)) (terr : Fin t → Fin m)
  (S : Fin m → Finset (Fin kappa))

/-- **A shell with no ports satisfies the full shell gap.**  The cross mass of
`shell_gap` vanishes, so the residual disappears. -/
theorem shell_gap_full_no_ports (terr : Fin 0 → Fin m) (S : Fin m → Finset (Fin kappa))
    (F : FracPacking (shell S0 terr S)) :
    F.value ≤ (nu3 (shell S0 terr S) : ℚ) + 10 * ((kappa - S0.card : ℕ) : ℚ) := by
  have h := shell_gap S0 terr S F
  have hzero : ∑ i : Fin m, ((privCard terr i : ℚ) * (sepCard S i : ℚ)) = 0 := by
    refine Finset.sum_eq_zero (fun i _ => ?_)
    have hp : privCard terr i = 0 := by
      have : (privSet terr i).card = 0 := Finset.card_eq_zero.2 (by
        ext x
        exact absurd x.2 (by omega))
      simpa [privCard] using this
    rw [hp]
    simp
  rw [hzero] at h
  linarith

end Instances

/-! ### Port-rich shells with an arbitrary hole -/

section PortRich

variable {kappa t m : ℕ} {S0 : Finset (Fin kappa)} {terr : Fin t → Fin m}
  {S : Fin m → Finset (Fin kappa)}

end PortRich

/-! ## Axiom audit -/

end BoundedCliqueGap

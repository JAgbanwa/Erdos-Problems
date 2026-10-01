import BoundedCliqueGap.FlowerLP

/-
`BoundedCliqueGap.FlowerFull` — declaration-level extract of the Route B
triangle-packing development.  Only the declarations in the constant cone of
`BoundedCliqueGap.chordal_gap_linear_cliqueFree` were kept (plus the few that
the retained sources need in order to elaborate); the module documentation
below is the original one and may advertise results that were pruned away.
-/

/-
# Rung I1 — the flower gap theorem in every regime, up to the donation mass

`BoundedCliqueGap/FlowerLP.lean` provides the ceiling; this file combines it with the
three `ν₃` lower bounds already in the project, through the edge-disjoint
decomposition of the flower into its hub and its territories:

* `nu3_clique_ge` (Bose) on the hub `flowerK`;
* `nu3_CS_ge_choose` on a **port-rich** territory (`p_i ≤ s_i`): every private
  edge gets its own port, so `ν₃(CS(p_i,s_i)) ≥ C(p_i,2)`;
* `nu3_CS_portPoor_ge` on a **port-poor** territory (`s_i < p_i`), rung H1's
  ingredient: `ν₃(CS(p_i,s_i)) ≥ (C(p_i,2) + p_i s_i)/3 − 10 p_i`.

The result, `flower_gap_dual`, holds for **every** flower — no regime
hypothesis — at the price of one residual term:

```
value ≤ ν₃(flower) + 10·(κ + t) + (h − 1/3)·Q + (1 − h)·R      (1/3 ≤ h ≤ 1)
```

with `Q = C(κ,2)` (the hub capacity) and

```
R = Σ_{i : p_i ≤ s_i} ( p_i s_i / 2 − C(p_i,2) )
```

the **donation mass**: the cross capacity of the port-rich territories that
their own private edges cannot absorb, and which therefore has to be paid for
by hub edges (type-`b` triangles: one hub edge, two cross edges).  Optimising
`h` gives the residual `(2/3)·min(Q, R)`, and:

* `R = 0` (no port-rich territory) recovers rung H1's `flower_gap_linear`
  with the same constant — but now with no hypothesis in the statement;
* `flower_gap_linear_full_of_donation_small` closes the flower completely
  whenever `min(Q,R) ≤ κ + t`.

What remains for an unconditional `flower_gap_linear_full` is exactly the
integral counterpart of the donation mass: converting `R` units of hub
capacity into type-`b` triangles at a rate matching the LP.  Edge-by-edge
donation is break-even (see `REPORT_H.md`); the block-granular donation is
discussed in `REPORT_I.md`.
-/

namespace BoundedCliqueGap

open Finset

/-- `C(k,2)` in `ℚ`. -/
lemma cast_choose_two (k : ℕ) : ((k.choose 2 : ℕ) : ℚ) = (k : ℚ) * ((k : ℚ) - 1) / 2 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · have h2 := two_mul_choose_two k
    have hk1 : ((k - 1 : ℕ) : ℚ) = (k : ℚ) - 1 := by
      have : (1 : ℕ) ≤ k := hk
      push_cast [Nat.cast_sub this]
      ring
    have : (2 : ℚ) * (k.choose 2 : ℕ) = (k : ℚ) * ((k : ℚ) - 1) := by
      rw [← hk1]
      exact_mod_cast congrArg (fun n : ℕ => (n : ℚ)) h2
    linarith

section FlowerGap

variable {kappa t m : ℕ} (terr : Fin t → Fin m) (S : Fin m → Finset (Fin kappa))

end FlowerGap

/-! ## Axiom audit -/

end BoundedCliqueGap

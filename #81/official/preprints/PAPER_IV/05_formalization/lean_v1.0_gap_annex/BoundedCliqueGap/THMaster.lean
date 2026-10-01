import BoundedCliqueGap.THForeign

/-
`BoundedCliqueGap.THMaster` — declaration-level extract of the Route B
triangle-packing development.  Only the declarations in the constant cone of
`BoundedCliqueGap.chordal_gap_linear_cliqueFree` were kept (plus the few that
the retained sources need in order to elaborate); the module documentation
below is the original one and may advertise results that were pruned away.
-/

/-
# TH3 — the chordal endpoint of the recursion, and the `G8` calibration

`BoundedCliqueGap/THPartition.lean` and `BoundedCliqueGap/THForeign.lean` run the clique-tree
recursion entirely on the packing side and close it whenever the clique-tree
holes are bounded.  This module feeds that into the universal Gavril
presentation of a chordal graph, which is exactly the route of
`chordal_gap_linear_of_treeHubGapFull` (`BoundedCliqueGap.MTLift`), only with the
interface `TreeHubGapFull` replaced by the *proved* bounded-hole hub bound.

* **`chordal_gap_linear_cliqueFree`** — for **every** chordal graph with no
  clique on `d+2` vertices, with **no presentation data beyond `IsChordal`**
  and no interface hypothesis:

      `value ≤ ν₃(H) + (10 + d/2)·|V|`.

  This is unconditional.  It extends the `+29` Moderate window of rung Q2
  (`chordal_gap_moderate`, constant `10` but only for `K₃₂`-free graphs) to an
  arbitrary clique bound, at a constant that grows with the bound; inside the
  Moderate window the Q-lane constant is the better one.

* **`hub_gap_bddHole_final`** — the same statement one level down, for the hub
  graph of an arbitrary subtree representation with bounded holes: the
  *interface* `TreeHubGapFull` restricted to that class, proved.

* **`G8_th_gap`** — the mandatory calibration.  `G8` (two `K₅`'s glued along an
  edge, `BoundedCliqueGap.LObstruction`) is `K₆`-free, so `d = 4` and the recursion
  closes it at the explicit constant `12`:

      `value ≤ ν₃(G8) + 96`.

  `G8_no_shellFamily` blocks the `ShellFamily` route of the L-ladder for this
  graph; it does **not** block this one, which goes through the Gavril tree and
  its per-node holed cliques.

* `TreeForeignMassLinear` and `treeHubGapFull_of_foreignMassLinear` — the
  honest statement of what is left of the universal case after the reduction:
  a linear bound on the foreign mass would give `TreeHubGapFull (10 + C)`.
  `BoundedCliqueGap/THObstruction.lean` proves that **no such bound exists**, so the
  universal case is *not* reachable from the per-node bookkeeping alone; the
  conditional implication is recorded to make the gap precise, not to pretend
  it is a route.

No `sorry`, no new axioms, no `native_decide`; `#print axioms` at the end.
-/

namespace BoundedCliqueGap

open Finset

/-! ## The hub interface on the bounded-hole class -/

section Hub

variable {n t : ℕ} {par : ℕ → ℕ} {rt : Fin n → ℕ} {sub : Fin n → Finset ℕ}
  {S0 : Finset (Fin n)}

/-- **The hub interface, proved on the bounded-hole class.**  Same shape as
`TreeHubGapFull C` (`BoundedCliqueGap.MTLift`), with the class hypothesis added and the
constant explicit. -/
theorem hub_gap_bddHole_final {r d : ℕ} (h : IsSubtreeRep par rt sub)
    (hS0 : ∀ x ∈ S0, rt x = 0) (hr : ∀ x, rt x < r)
    (hd : ∀ j < r, (treeHole sub rt S0 j).card ≤ d)
    (F : FracPacking (treeHubGraph sub S0 t)) :
    F.value ≤ (nu3 (treeHubGraph sub S0 t) : ℚ)
      + (10 + (d : ℚ) / 2) * (((n - S0.card : ℕ) : ℚ) + (t : ℚ)) := by
  have hbase := th_gap_bddHole h hS0 hr hd F
  have hnn : (0 : ℚ) ≤ (t : ℚ) := by positivity
  have hc : (0 : ℚ) ≤ 10 + (d : ℚ) / 2 := by positivity
  nlinarith

end Hub

/-! ## The chordal endpoint -/

section Chordal

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **The endpoint of lane TH.**  A graph carrying a reverse perfect elimination
numbering (`RevPES`, i.e. a chordal graph) and without a clique on `d+2`
vertices has integrality gap at most `(10 + d/2)·|V|` — unconditionally, with no
presentation data beyond the numbering.

The proof is the clique-tree recursion of this lane run on the Gavril
presentation: the value splits over the nodes, each node's piece is a holed
clique (gap `10·|own|`), the pieces are edge-disjoint so their packing numbers
add inside `ν₃`, and the foreign mass — the `(o,h,h)` triangles whose hole–hole
edge is owned at a strict ancestor — is paid by the gluing capacity, which is
where the clique bound enters.

The chordality hypothesis is delivered in the form `SimpleGraph.IsChordal` by
`BoundedCliqueGap.chordal_gap_linear_cliqueFree` (`BoundedCliqueGap/Gap.lean`). -/
theorem gap_linear_of_revPES {H : SimpleGraph V} {d : ℕ} {ord : V → ℕ}
    (hpes : RevPES H ord) (hk : H.CliqueFree (d + 2)) (F : FracPacking H) :
    F.value ≤ (nu3 H : ℚ) + (10 + (d : ℚ) / 2) * (Fintype.card V : ℚ) := by
  classical
  set P := chordalTreePresentation hpes with hP
  refine gap_transfer_embed P.emb P.emb_inj P.emb_adj P.emb_supp
    ((10 + (d : ℚ) / 2) * (Fintype.card V : ℚ)) (fun F' => ?_) F
  revert F'
  rw [hP, chordalTreePresentation_flower_eq_hub hpes]
  intro F'
  have hd : ∀ j < (chordalTreePresentation hpes).r,
      (treeHole (chordalTreePresentation hpes).sub (chordalTreePresentation hpes).rt
        (chordalTreePresentation hpes).S0 j).card ≤ d := by
    intro j hj
    have hj' : j < Fintype.card V := by simpa using hj
    have := chordalTree_treeHole_card_lt (k := d + 1) hpes (by simpa using hk) hj'
    omega
  have h := hub_gap_bddHole_final (d := d) (chordalTreePresentation hpes).isRep
    (chordalTreePresentation hpes).hS0 (chordalTreePresentation hpes).hr hd F'
  simpa using h

end Chordal

/-! ## The mandatory calibration: `G8`, two `K₅`'s glued along an edge -/

section G8

end G8

/-! ## What is left of the universal case -/

section Residual

end Residual

/-! ## Axiom audit -/

end BoundedCliqueGap

/-
# The two caps the counted merge runs into

This file is the quantitative part of the audit of the one-link step
`BKLO.RoutedSweepInvCellCountWide6hStep` (`BKLO/AX2CountedMerge.lean`).  The audit of
`BKLO/AX2CountedMergeAllocation.lean` isolates the allocation the merge has to carry out; what is
proved here is how much room the *two* resources a forced leftover may draw on — a slot of the
foreign plan, or a planned place together with a free routing index — actually have, and where the
room runs out.

A forced leftover of the perturbation at the new link `u` is a place `z` of a class of the region
of `u` which the class matching cannot send across (`BKLO.trace_deficit_forces_leftovers`).  Only
the places the perturbation *deletes* force one: a place it adds lies outside `resLink R W' u`,
where the cross-side rule of `BKLO.IsClassMatchedSweep` does not reach it, so the operative demand
per link is `D = t / 32` and not `t / 16`.  By `BKLO.count_partner_forced_or_foreign` the counted
invariant classifies such a `z` in exactly one of two ways:

* **foreign**: `z ∈ M u`, its partner unconstrained;
* **cross-routed**: `z ∈ L u` planned, its partner a place of the opposite part of the region, and
  the fibre `(z, routing index)` charged one more unit against the counted cap `5 K² t + 1`.

## 1. The foreign plan has the volume, but only for a *spread* demand

`BKLO.ledger_caps_foreign_ceiling`: every foreign ceiling `c · K² t` the leftover ledger admits —
`4 (t + 1) + 4 (5 K² t + 1) + c K² t ≤ 25 K² t`, the inequality
`BKLO.excLedgerSpread_of_routedSweepInvCellCountWide` pays — has `c ≤ 4`, and at `K = 2` only
`c ≤ 3` (`BKLO.uniform_line_foreign_demand_exceeds_ceiling_at_two` uses this).  The wide plan's
`c = 3` is therefore at the ledger's own ceiling: widening it is not an option.

Against that ceiling the counts come out as follows, at the worst class size the design admits
(`4 q = 3 t`, the floor of `IsGridTwoSidedReservoir.classCardGe`):

* **spread demand fits.**  `BKLO.uniform_line_foreign_demand_fits`: with the operative demand
  `32 D = t` spread uniformly over the `h` classes of the relevant part of each region, a class
  receives `2 (20 K² t + 1) D ≈ 1.25 K² t²` slots against the `q · 3 K² t ≈ 2.25 K² t²` the wide
  plan holds.  `BKLO.spread_foreign_allotment_fits` is the same count for an allotment of `m`
  slots per class per link: it fits as soon as `80 h m ≤ 3 t`.
* **concentrated demand does not.**  `BKLO.line_local_foreign_demand_exceeds_ceiling`: if every
  link of the two lines that meet a class puts its whole demand into *that* class, the class is
  asked for `2 h (20 K² t + 1) D`, a factor `≈ 0.8 h` more than even the ceiling `4 K² t` holds.
* and the demand is not spread for free: `BKLO.uniform_line_foreign_demand_exceeds_ceiling_at_two`
  shows that at `K = 2` there is not even a factor two of slack in the spread count — at the
  doubled demand `16 D = t` the uniform spread already overshoots by `10 / 9`.

So the foreign route is a *spreading* problem, and what decides whether the merge can spread is the
routing index: the class a foreign partner is taken from is the class of the routing index the
planned leftover uses.

## 2. What the counted clause does *not* reserve

How many routing indices a history can take away from a place is decided by the plan, not by the
counted clause: `BKLO.blocked_routing_indices_card_le` shows that a full fibre costs `5 K² t + 1`
of the links at which the plan claims the place, so a plan whose load at a place along a line is
`ℓ` leaves at least `h - ℓ / (5 K² t + 1)` of the `h` indices free there.  This is the positive
half, and it is the reason the merge has *many* target classes to spread over: a cell-balanced plan
sits far below the cell ceiling.  `BKLO.exists_free_routing_index_sharp` shows the other end of the
scale — at the ceiling `BKLO.planned_row_line_card_lt` allows, a history can leave exactly one
usable index — and `BKLO.exists_saturated_partner_pool` with
`BKLO.counted_clause_fails_at_saturated` show that saturating one and the same index at *every*
place of a pool is consistent with the counted clause, after which the new link may not use that
index at all.

`BKLO.pool_blocking_affordable` is the count that matters, and it is scale-invariant: emptying all
`h` fibres of every one of the `p` places the plan offers the new link costs `p h (5 K² t + 1)`
links of history, while the plan hands the whole line `h (20 K² t + 1) p` slots — four times as
many.  Whatever density the plan is built at, a history admitted by
`BKLO.RoutedSweepInvCellCount` can aim its budget at one link and take away *every* routing index
of *every* place the plan offers there.  At such a link the cross-routed route is closed, the
forced leftovers must all be foreign, and their classes are the ones the perturbation chose — the
concentrated demand of §1, which the foreign plan cannot hold and which no allocation chosen in
advance can prepare for, since `M` is fixed before the history is presented.

## 3. What this says about the step

The counted clause caps each fibre but does not **balance** the fibres, and it does not tie a
place's used fibres to the plan's slots at that place.  §2 shows that the invariant, as stated,
admits histories that spend that freedom on one link; §1 shows the foreign plan cannot pick up the
pieces there.  A closure along the prescribed route therefore needs a change of statement, and the
two cheapest are:

* a **balanced-fibre invariant**: record in `BKLO.RoutedSweepInvCellCount` that the fibres a place
  has lost along a line are a bounded fraction of the plan's slots at that place — the clause a
  sweep built by a least-loaded-index rule maintains for free.  With it,
  `BKLO.blocked_routing_indices_card_le` turns into a *matching* pair of free indices on the two
  sides of a forced pair, and the merge can spread its foreign demand into the window
  `BKLO.spread_foreign_allotment_fits` describes.  The whole chain
  `BKLO.excLedgerSpread_of_routedSweepInvCellCountWide` →
  `BKLO.twoSidedUsedClassMatchedResized6hPairing_of_cell_step_countWide` →
  `BKLO.triangle_decomposition_of_inputs_and_cell_step_countWide` then has to be re-run against the
  strengthened invariant; nothing in it uses more than the clauses it already has.
* or a **finer residual demand**, presenting only links whose perturbation is a `1 / (32 h)`
  fraction of a class rather than `1 / 32`: the per-link demand then drops by a factor `h` and even
  the concentrated count fits (`BKLO.fine_perturbation_foreign_demand_fits`).

Everything here is `sorry`-free.  Nothing here *refutes*
`BKLO.RoutedSweepInvCellCountWide6hStep`: these are statements about the ledger arithmetic and
about the counted clause in the abstract, and a refutation would have to exhibit a design instance
carrying the concentrated perturbation and the blocking history at once.  They do say exactly where
a proof along the prescribed route runs out of room, and that the missing ingredient is a clause of
the invariant, not a wider plan.
-/
import BKLO.AX2CountedMergeAllocation

open Finset

namespace BKLO

/-! ### 1. The foreign ceiling the ledger admits -/

/-- **The leftover ledger admits no foreign ceiling above `4 K² t`.**  The spread ledger the counted
invariant pays is `4 (t + 1) + 4 (5 K² t + 1) + c K² t ≤ 25 K² t`
(`BKLO.excLedgerSpread_of_routedSweepInvCellCountWide` at `c = 3`); at `c = 5` the cycle and routed
terms alone already exhaust it. -/
theorem ledger_caps_foreign_ceiling {K t c : ℕ} (hK : 2 ≤ K) (ht : 512 ≤ t)
    (hled : 4 * (t + 1) + 4 * (5 * (K * K) * t + 1) + c * ((K * K) * t) ≤ 25 * ((K * K) * t)) :
    c ≤ 4 := by
  by_contra hcon
  push_neg at hcon
  have hKK : 4 ≤ K * K := Nat.mul_le_mul hK hK
  have h4t : 4 * t ≤ (K * K) * t := Nat.mul_le_mul_right _ hKK
  have h5 : 5 * ((K * K) * t) ≤ c * ((K * K) * t) := Nat.mul_le_mul_right _ hcon
  have hpos : 0 < t := by omega
  linarith only [hled, h5, h4t, hpos]

/-- **A single class cannot hold the line-local foreign demand of a maximal perturbation.**  With
the worst class size `4 q = 3 t` and the maximal admissible per-link demand `16 D = t`, the two
lines that meet a class carry `2 h (20 K² t + 1)` links, and even the largest foreign ceiling the
ledger admits (`BKLO.ledger_caps_foreign_ceiling`) leaves the class short. -/
theorem line_local_foreign_demand_exceeds_ceiling {K t h q D : ℕ} (hK : 2 ≤ K) (ht : 512 ≤ t)
    (hh : 2 ≤ h) (hq : 4 * q = 3 * t) (hD : 16 * D = t) :
    q * (4 * (K * K) * t) < 2 * h * (20 * (K * K) * t) * D := by
  have hKK : 4 ≤ K * K := Nat.mul_le_mul hK hK
  have hpos : 0 < t := by omega
  have hDpos : 0 < D := by omega
  have hlhs : 16 * (q * (4 * (K * K) * t)) = 48 * ((K * K) * (t * t)) := by
    have h : 16 * (q * (4 * (K * K) * t)) = 16 * (4 * q) * ((K * K) * t) := by ring
    rw [h, hq]; ring
  have hrhs : 16 * (2 * h * (20 * (K * K) * t) * D) = 40 * h * ((K * K) * (t * t)) := by
    have : 16 * (2 * h * (20 * (K * K) * t) * D) = 40 * h * ((K * K) * t) * (16 * D) := by ring
    rw [this, hD]; ring
  have hkey : 48 * ((K * K) * (t * t)) < 40 * h * ((K * K) * (t * t)) := by
    have h80 : 80 * ((K * K) * (t * t)) ≤ 40 * h * ((K * K) * (t * t)) := by
      have : 80 * ((K * K) * (t * t)) = 40 * 2 * ((K * K) * (t * t)) := by ring
      rw [this]
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 40 hh)
    have hp : 0 < (K * K) * (t * t) := by positivity
    omega
  omega

/-- **A perturbation `h` times finer does fit, line by line.**  At `16 * (h * D) = t` — a
perturbation of `1 / (32 h)` of a class rather than `1 / 32` — the same count comes out the other
way: the two lines of a class demand `2 h (20 K² t) D ≈ 2.5 K² t²` foreign slots and the ceiling
`4 K² t` holds `3 K² t²`. -/
theorem fine_perturbation_foreign_demand_fits {K t h q D : ℕ}
    (hq : 4 * q = 3 * t) (hD : 16 * (h * D) = t) :
    2 * h * (20 * (K * K) * t) * D ≤ q * (4 * (K * K) * t) := by
  have hlhs : 16 * (2 * h * (20 * (K * K) * t) * D) = 40 * ((K * K) * t) * (16 * (h * D)) := by
    ring
  have hrhs : 16 * (q * (4 * (K * K) * t)) = 16 * (4 * q) * ((K * K) * t) := by ring
  rw [hD] at hlhs
  rw [hq] at hrhs
  have h1 : 16 * (2 * h * (20 * (K * K) * t) * D) = 40 * ((K * K) * (t * t)) := by
    rw [hlhs]; ring
  have h2 : 16 * (q * (4 * (K * K) * t)) = 48 * ((K * K) * (t * t)) := by
    rw [hrhs]; ring
  omega

/-- **At `K = 2` and the worst class size, no ledger-admissible foreign ceiling covers even the
perfectly spread foreign demand.**  This is the sharp form of the obstruction.  Suppose the merge
manages to spread the foreign partners of the forced leftovers of every link *uniformly* over the
`h` classes of the relevant part of its region — the best any allocation can do.  A class is then
asked for `2 (20 K² t + 1) D` slots (its two lines carry `2 h (20 K² t + 1)` links, each
contributing `D / h`), which at `K = 2` and `16 D = t` is `10 t²`, while a class of the worst size
`4 q = 3 t` holds `q · c · 4 t ≤ 9 t²` slots for every ceiling `c` the leftover ledger admits.  So
the foreign route is short by a factor `10 / 9` at the corner `K = 2`, `4 q = 3 t` of the parameter
space — for the wide plan's `c = 3` and for every other `c` the ledger allows. -/
theorem uniform_line_foreign_demand_exceeds_ceiling_at_two {t q D c : ℕ} (ht : 512 ≤ t)
    (hq : 4 * q = 3 * t) (hD : 16 * D = t)
    (hled : 4 * (t + 1) + 4 * (5 * 4 * t + 1) + c * (4 * t) ≤ 25 * (4 * t)) :
    q * (c * (4 * t)) < 2 * (20 * 4 * t) * D := by
  have ht0 : 0 < t := by omega
  have hc : c ≤ 3 := by
    by_contra hcon
    push_neg at hcon
    have h4 : 4 * (4 * t) ≤ c * (4 * t) := Nat.mul_le_mul_right _ hcon
    omega
  have hL : 64 * (q * (c * (4 * t))) = 192 * (c * (t * t)) := by
    have h : 64 * (q * (c * (4 * t))) = 64 * ((4 * q) * (c * t)) := by ring
    rw [h, hq]; ring
  have hR : 64 * (2 * (20 * 4 * t) * D) = 640 * (t * t) := by
    have h : 64 * (2 * (20 * 4 * t) * D) = 640 * (t * (16 * D)) := by ring
    rw [h, hD]
  have hcle : 192 * (c * (t * t)) ≤ 576 * (t * t) := by
    have : c * (t * t) ≤ 3 * (t * t) := Nat.mul_le_mul_right _ hc
    omega
  have hpos : 0 < t * t := Nat.mul_pos ht0 ht0
  omega

/-- **Spread over the classes, the demand of the deletions does fit.**  Only the places the
perturbation *deletes* force a leftover — a place it adds lies outside `resLink R W' u`, where the
cross-side rule does not reach it — so the operative demand is `32 D = t`, not `16 D = t`.  Spread
uniformly over the `h` classes of the relevant part of each region, a class then receives
`2 (20 K² t + 1) D ≈ 1.25 K² t²` foreign slots against the `q · 3 K² t ≈ 2.25 K² t²` the *wide*
plan already holds at the worst class size.  The foreign plan is therefore not short of volume: it
is short only against a demand the merge is forced to concentrate. -/
theorem uniform_line_foreign_demand_fits {K t q D : ℕ} (hK : 2 ≤ K) (ht : 512 ≤ t)
    (hq : 4 * q = 3 * t) (hD : 32 * D = t) :
    2 * (20 * (K * K) * t + 1) * D ≤ q * (3 * (K * K) * t) := by
  have hKK : 4 ≤ K * K := Nat.mul_le_mul hK hK
  have ht0 : 0 < t := by omega
  have hL : 32 * (2 * (20 * (K * K) * t + 1) * D)
      = 40 * ((K * K) * (t * t)) + 2 * t := by
    have h : 32 * (2 * (20 * (K * K) * t + 1) * D)
        = (40 * ((K * K) * t) + 2) * (32 * D) := by ring
    rw [h, hD]; ring
  have hR : 32 * (q * (3 * (K * K) * t)) = 72 * ((K * K) * (t * t)) := by
    have h : 32 * (q * (3 * (K * K) * t)) = 24 * ((4 * q) * ((K * K) * t)) := by ring
    rw [h, hq]; ring
  have hbig : 2 * t ≤ 32 * ((K * K) * (t * t)) := by
    have h1 : 4 * (t * t) ≤ (K * K) * (t * t) := Nat.mul_le_mul_right _ hKK
    nlinarith only [h1, ht0]
  omega

/-- **A spread foreign allotment fits.**  If the plan hands every link `m` foreign slots in each
class of the relevant part of its region, and `80 h m ≤ 3 t`, then the two lines that meet a class
demand at most the `q · 3 K² t` the wide plan holds at the worst class size.  Together with
`BKLO.blocked_routing_indices_card_le` — which leaves a fixed fraction of the `h` routing indices
free at every place, hence a fixed fraction of the classes available as targets — this is the
window a closure has to work inside. -/
theorem spread_foreign_allotment_fits {K t h q m : ℕ} (hK : 2 ≤ K) (ht : 512 ≤ t)
    (hq : 4 * q = 3 * t) (hm : 80 * (h * m) ≤ 3 * t) :
    2 * h * (20 * (K * K) * t + 1) * m ≤ q * (3 * (K * K) * t) := by
  have hKK : 4 ≤ K * K := Nat.mul_le_mul hK hK
  have ht0 : 0 < t := by omega
  have hbig : 3 * t ≤ 30 * ((K * K) * (t * t)) := by
    have h1 : 4 * (t * t) ≤ (K * K) * (t * t) := Nat.mul_le_mul_right _ hKK
    nlinarith only [h1, ht0]
  have hR : 40 * (q * (3 * (K * K) * t)) = 90 * ((K * K) * (t * t)) := by
    have h : 40 * (q * (3 * (K * K) * t)) = 30 * ((4 * q) * ((K * K) * t)) := by ring
    rw [h, hq]; ring
  have key : 40 * (2 * h * (20 * (K * K) * t + 1) * m) ≤ 40 * (q * (3 * (K * K) * t)) := by
    calc 40 * (2 * h * (20 * (K * K) * t + 1) * m)
        = (20 * ((K * K) * t) + 1) * (80 * (h * m)) := by ring
      _ ≤ (20 * ((K * K) * t) + 1) * (3 * t) := Nat.mul_le_mul_left _ hm
      _ = 60 * ((K * K) * (t * t)) + 3 * t := by ring
      _ ≤ 90 * ((K * K) * (t * t)) := by omega
      _ = 40 * (q * (3 * (K * K) * t)) := hR.symm
  omega

/-! ### 2. The routing fibre: what the counted clause does *not* reserve -/

/-- **How many routing indices a history can block.**  Every index whose fibre is full costs the
history `B + 1` of the links at which the place is claimed, so the blocked indices are at most
`1 / (B + 1)` of that claim.  `BKLO.exists_free_routing_index` is the case where the claim is
below `(B + 1) h`, which leaves one index; a plan whose *line* load at a place is `ℓ` leaves
`h - ℓ / (B + 1)` of them. -/
theorem blocked_routing_indices_card_le {V : Type*} [DecidableEq V] {h B : ℕ} {S : Finset V}
    {Pc : V → Finset V} {rt : V → V → ℕ} (a : V) (hrt : ∀ w ∈ S, rt w a < h) :
    (B + 1) * ((Finset.range h).filter
        (fun P => B < excRouteCount S Pc a (fun w => rt w a) P)).card
      ≤ (S.filter (fun w => a ∈ Pc w)).card := by
  classical
  have hsum : ∑ P ∈ Finset.range h, excRouteCount S Pc a (fun w => rt w a) P
      = (S.filter (fun w => a ∈ Pc w)).card := by
    simp only [excRouteCount, Finset.card_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro w hw
    by_cases hwa : a ∈ Pc w
    · rw [Finset.sum_eq_single (rt w a)]
      · simp [hwa]
      · intro P _ hne
        simp [Ne.symm hne]
      · intro hmem
        exact absurd (Finset.mem_range.2 (hrt w hw)) hmem
    · simp [hwa]
  rw [← hsum]
  set Bl : Finset ℕ := (Finset.range h).filter
    (fun P => B < excRouteCount S Pc a (fun w => rt w a) P) with hBl
  calc (B + 1) * Bl.card = ∑ _P ∈ Bl, (B + 1) := by
        rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
    _ ≤ ∑ P ∈ Bl, excRouteCount S Pc a (fun w => rt w a) P :=
        Finset.sum_le_sum (fun P hP => (Finset.mem_filter.1 hP).2)
    _ ≤ ∑ P ∈ Finset.range h, excRouteCount S Pc a (fun w => rt w a) P :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)


/-- **`BKLO.exists_free_routing_index` is sharp.**  For every cap `B` and every number `h` of
indices there is a history claiming the place `a` at `(B + 1) (h - 1)` links — one link short of
the ceiling `BKLO.planned_row_line_card_lt` imposes — whose fibres are full at every index below
`h - 1`.  Exactly one index of the design is left usable, and the merge does not get to choose
which. -/
theorem exists_free_routing_index_sharp (B h a : ℕ) :
    ∃ (S : Finset ℕ) (Pc : ℕ → Finset ℕ) (rt : ℕ → ℕ → ℕ),
      (∀ w ∈ S, rt w a < h) ∧
      (S.filter (fun w => a ∈ Pc w)).card = (B + 1) * (h - 1) ∧
      (∀ P, excRouteCount S Pc a (fun w => rt w a) P ≤ B ↔ h - 1 ≤ P) := by
  classical
  refine ⟨Finset.range ((B + 1) * (h - 1)), fun _ => {a}, fun w _ => w / (B + 1), ?_, ?_, ?_⟩
  · intro w hw
    have hw' : w < (B + 1) * (h - 1) := Finset.mem_range.1 hw
    have hh : 1 ≤ h := by
      rcases Nat.eq_zero_or_pos h with rfl | hh
      · simp at hw'
      · exact hh
    have hdiv : w / (B + 1) < h - 1 := by
      refine Nat.div_lt_of_lt_mul ?_
      omega
    show w / (B + 1) < h
    omega
  · have : ((Finset.range ((B + 1) * (h - 1))).filter (fun w => a ∈ ({a} : Finset ℕ)))
        = Finset.range ((B + 1) * (h - 1)) := by
      apply Finset.filter_true_of_mem
      intro w _
      simp
    rw [this, Finset.card_range]
  · intro P
    have hcount : excRouteCount (Finset.range ((B + 1) * (h - 1))) (fun _ => ({a} : Finset ℕ)) a
        (fun w => w / (B + 1)) P
        = ((Finset.range ((B + 1) * (h - 1))).filter (fun w => w / (B + 1) = P)).card := by
      simp only [excRouteCount]
      congr 1
      apply Finset.filter_congr
      intro w _
      simp
    rw [hcount]
    constructor
    · intro hle
      by_contra hcon
      push_neg at hcon
      -- `P < h - 1`: the fibre of `P` is a full block of `B + 1` links
      have hblock : ((Finset.range ((B + 1) * (h - 1))).filter (fun w => w / (B + 1) = P))
          = Finset.Ico (P * (B + 1)) ((P + 1) * (B + 1)) := by
        ext w
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
        constructor
        · rintro ⟨-, hdiv⟩
          have hdm := Nat.div_add_mod w (B + 1)
          have hmod : w % (B + 1) < B + 1 := Nat.mod_lt _ (by omega)
          rw [hdiv] at hdm
          have e1 : P * (B + 1) = (B + 1) * P := Nat.mul_comm _ _
          have e2 : (P + 1) * (B + 1) = (B + 1) * P + (B + 1) := by ring
          omega
        · rintro ⟨h1, h2⟩
          have hdiv : w / (B + 1) = P := by
            refine Nat.div_eq_of_lt_le ?_ ?_
            · omega
            · omega
          refine ⟨?_, hdiv⟩
          have : (P + 1) * (B + 1) ≤ (h - 1) * (B + 1) :=
            Nat.mul_le_mul_right _ (by omega)
          have hcomm : (h - 1) * (B + 1) = (B + 1) * (h - 1) := Nat.mul_comm _ _
          omega
      rw [hblock, Nat.card_Ico] at hle
      have : (P + 1) * (B + 1) - P * (B + 1) = B + 1 := by
        have : (P + 1) * (B + 1) = P * (B + 1) + (B + 1) := by ring
        omega
      omega
    · intro hP
      have hempty : ((Finset.range ((B + 1) * (h - 1))).filter (fun w => w / (B + 1) = P))
          = ∅ := by
        apply Finset.filter_false_of_mem
        intro w hw hdiv
        have hw' : w < (B + 1) * (h - 1) := Finset.mem_range.1 hw
        have hlt : w / (B + 1) < h - 1 := by
          refine Nat.div_lt_of_lt_mul ?_
          omega
        omega
      rw [hempty]
      simp

/-- **The counted clause does not reserve a fibre.**  A history may sit at the cap `B + 1` on one
and the same index `β` at *every* place of a pool, and still satisfy the counted clause of
`BKLO.RoutedSweepInvCellCount` everywhere. -/
theorem exists_saturated_partner_pool (B β : ℕ) (pool : Finset ℕ) (u : ℕ) :
    ∃ (S : Finset ℕ) (Pr : ℕ → Finset ℕ) (rt : ℕ → ℕ → ℕ), u ∉ S ∧
      (∀ b P, excRouteCount S Pr b (fun w => rt w b) P ≤ B + 1) ∧
      (∀ b ∈ pool, excRouteCount S Pr b (fun w => rt w b) β = B + 1) := by
  classical
  refine ⟨(Finset.range (B + 1)).image (fun i => u + 1 + i), fun _ => pool, fun _ _ => β,
    ?_, ?_, ?_⟩
  · intro hu
    obtain ⟨i, -, hi⟩ := Finset.mem_image.1 hu
    omega
  · intro b P
    refine le_trans (Finset.card_le_card (Finset.filter_subset _ _)) ?_
    exact le_trans (Finset.card_image_le) (by rw [Finset.card_range])
  · intro b hb
    have hset : ((Finset.range (B + 1)).image (fun i => u + 1 + i)).filter
        (fun w => b ∈ pool ∧ β = β)
        = (Finset.range (B + 1)).image (fun i => u + 1 + i) := by
      apply Finset.filter_true_of_mem
      intro w _
      exact ⟨hb, rfl⟩
    have hinj : Function.Injective (fun i => u + 1 + i) := fun i j hij =>
      Nat.add_left_cancel hij
    show (((Finset.range (B + 1)).image (fun i => u + 1 + i)).filter
      (fun w => b ∈ pool ∧ β = β)).card = B + 1
    rw [hset, Finset.card_image_of_injective _ hinj, Finset.card_range]

/-- **And then the new link may not use that index.**  Adding a link that routes a saturated place
at the saturated index breaks the counted clause outright: the fibre goes to `B + 2`. -/
theorem counted_clause_fails_at_saturated {S : Finset ℕ} {Pr : ℕ → Finset ℕ} {rt : ℕ → ℕ → ℕ}
    {b β B u : ℕ} (huS : u ∉ S) (hsat : excRouteCount S Pr b (fun w => rt w b) β = B + 1)
    (hu : b ∈ Pr u) (hrt : rt u b = β) :
    excRouteCount (insert u S) Pr b (fun w => rt w b) β = B + 2 := by
  classical
  have hfil : (insert u S).filter (fun w => b ∈ Pr w ∧ rt w b = β)
      = insert u (S.filter (fun w => b ∈ Pr w ∧ rt w b = β)) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨hw | hw, hp⟩
      · exact Or.inl hw
      · exact Or.inr ⟨hw, hp⟩
    · rintro (rfl | ⟨hw, hp⟩)
      · exact ⟨Or.inl rfl, hu, hrt⟩
      · exact ⟨Or.inr hw, hp⟩
  have hnot : u ∉ S.filter (fun w => b ∈ Pr w ∧ rt w b = β) := fun hcon =>
    huS (Finset.mem_filter.1 hcon).1
  simp only [excRouteCount] at hsat ⊢
  rw [hfil, Finset.card_insert_of_notMem hnot, hsat]

/-- **A blocking history is affordable.**  The cell plan's slots along a line of the design,
`h (20 K² t + 1) D` at a per-link demand of `D` places, are at least `3 h` times the cost
`D (5 K² t + 1)` of saturating one routing fibre at every place the plan offers a link.  So a
history admitted by `BKLO.RoutedSweepInvCellCount` has, several times over, the room to block the
index the merge needs at every candidate partner. -/
theorem blocking_budget_exceeds_index_demand {K t h D : ℕ} (hK : 2 ≤ K) (ht : 512 ≤ t) :
    3 * h * (D * (5 * (K * K) * t + 1)) ≤ h * (20 * (K * K) * t + 1) * D := by
  have hKK : 4 ≤ K * K := Nat.mul_le_mul hK hK
  have hpos : 2 ≤ 5 * ((K * K) * t) := by nlinarith only [ht, hKK]
  have h1 : 3 * h * (D * (5 * (K * K) * t + 1)) = h * D * (15 * ((K * K) * t) + 3) := by ring
  have h2 : h * (20 * (K * K) * t + 1) * D = h * D * (20 * ((K * K) * t) + 1) := by ring
  rw [h1, h2]
  exact Nat.mul_le_mul_left _ (by omega)

/-- **Blocking every index at every place the plan offers one link costs a quarter of the plan's
own slots along that line.**  A place is emptied of all its `h` routing indices at the price of
`h (5 K² t + 1)` links of the history at which the plan claims it, so emptying all `p` places the
plan offers the new link costs `p h (5 K² t + 1)`, while the plan hands the whole line
`h (20 K² t + 1) p` slots — four times as many.  A history admitted by
`BKLO.RoutedSweepInvCellCount` can therefore aim its whole index budget at the pool of a single
link, and no choice of the plan's density changes the ratio: both sides scale with the pool. -/
theorem pool_blocking_affordable {K t h p slots : ℕ}
    (hslots : h * (20 * (K * K) * t) * p ≤ slots) :
    4 * (p * (h * (5 * (K * K) * t + 1))) ≤ slots + 4 * (p * h) := by
  have h1 : 4 * (p * (h * (5 * (K * K) * t + 1)))
      = h * (20 * (K * K) * t) * p + 4 * (p * h) := by ring
  omega

end BKLO

/-
# The allocation balance sheet of the counted merge

`BKLO.RoutedSweepInvCellCountWide6hStep` (`BKLO/AX2CountedMerge.lean`) is the one-link step of the
counted routed invariant against the **wide** foreign plan `BKLO.ForeignSpreadLeftoverPlanWide`, at
the reservoir re-sized to `6 h ≤ t`.  Its whole chain to the main theorem is proved; the step
itself is not.

This file is the audit of the *allocation* the merge has to carry out, in the form the merge
actually needs it: how many places of a class the new link is forced to leave over, which of the
two plans has to hold them, and what that costs the wide plan globally.  Everything here is
`sorry`-free.

## 1. What the perturbation forces, class by class

`BKLO.trace_deficit_forces_leftovers` is the pigeonhole at the new link: the cross-side rule of
`BKLO.IsClassMatchedSweep` sends the non-leftovers of a column class `C (α h + y u)` of the region
*injectively* into the row class `C (x u h + σ u α)` the class matching prescribes, so

```
|C (α h + y u) ∩ X u ∩ resLink R W' u| ≤ |C (x u h + σ u α) ∩ X u| + |Exc u ∩ C (α h + y u)|.
```

A perturbation that deletes `d` places of the matched row class therefore forces `d` leftovers in
the column class — in *that* class, which the perturbation chooses, not one the prover chooses.

By `BKLO.count_partner_forced_or_foreign` each of those leftovers is either a slot of the foreign
plan (`z ∈ M u`) or a row-routed leftover — and then it is planned (`Pr u ⊆ L u`) and its routing
index is *forced* to the class digit of its partner.  `BKLO.column_leftover_planned_or_foreign`
records the resulting dichotomy in the shape the balance sheet uses:

```
Δ ≤ |L u ∩ C (α h + y u)| + |M u ∩ C (α h + y u)|
```

for the forced deficit `Δ` of the class, whenever the partners of those leftovers lie in row
classes of the region other than the sink one.

## 2. What the two plans can hold

* the cell plan is ample: over the `h` cells of a line `BKLO.cell_plan_line_total_le` gives
  `∑_{w in the line} |L w ∩ C i| ≤ |C i| · h · (5 K² t + 1)`, about `5 K² t² h`, against a demand
  of at most `(t / 32)` per link, i.e. about `0.63 K² t² h` over the
  `h (20 K² t + 1)` links of the line (`BKLO.twoSided_col_line_card_le`).  The plan is not the
  bottleneck — the *routing index* is: the index of a forced leftover of §1 is not free, and the
  counted clause caps its fibre at `5 K² t + 1`.
* the foreign plan is scarce: `BKLO.wide_plan_class_total_le` is the exact global ceiling
  `∑_{w ∈ W \ W'} |M w ∩ C i| ≤ |C i| · 3 K² t`.

## 3. The finding: the foreign plan has the room, but only globally

With the maximal admissible perturbation the merge has to place `D = t / 16` foreign partners per
link, each in a class of the *opposite* part of the region of that link — a row class if the
leftover sits in a column class, and conversely.  The prover chooses which one, the perturbation
does not.  Two counts, at the worst class size the design admits (`4 q = 3 t`, the floor of
`IsGridTwoSidedReservoir.classCardGe`), bracket the problem:

* `BKLO.uniform_line_demand_exceeds_class_capacity` — spreading each link's `D` partners
  *uniformly* over the `h` classes of the relevant line overshoots.  A class is served by two
  lines, `h (20 K² t + 1)` links each, so it receives `2 (20 K² t + 1) D ≈ 2.5 K² t²` while the
  wide plan holds `3 K² t · q = 2.25 K² t²`.  The same overshoot defeats every *line-local* rule,
  in particular the locally balanced plan of `BKLO.exists_locally_balanced_plan`, whose load bound
  `BKLO.planLoad_le_of_locallyBalanced` is exactly the line average.
* `BKLO.global_demand_fits_class_capacity` — globally there is room, with a factor `1.8` to spare:
  summed over all `h²` classes the demand is `h² (20 K² t + 1) D ≈ 1.25 K² t² h²` against a
  capacity `h² · 3 K² t · q = 2.25 K² t² h²`.

So the merge is not blocked by the ledger: it is blocked by the *allocation*.  Closing
`BKLO.RoutedSweepInvCellCountWide6hStep` along the prescribed route needs the foreign slots to be
allotted by a **global transportation argument** — a degree-constrained flow over the bipartite
system (links × classes), balancing the row-part demand of one line against the column-part demand
of another — and not by any per-link or per-line rule.  No such argument is available in the
library: `BKLO.exists_balanced_prescription` balances one class over one cell, and
`BKLO.exists_locally_balanced_plan` only ever certifies the average of a single link's pool
(`BKLO.planLoad_le_of_locallyBalanced`).

`BKLO.foreign_allocation_gap_witness` is the numeric form of the two counts at
`K = 2`, `h = 25600`, `t = 6 h = 153600`, `q = 3 t / 4 = 115200`, `D = t / 16 = 9600`.

## 4. What closing the step still needs

The audit leaves the one-link step `BKLO.RoutedSweepInvCellCountWide6hStep` open, and it says
exactly which five objects a closure along the prescribed route has to produce.  None of them is
refuted by anything in the development; none of them is available in it either.

1. **A perturbed three-class cycle pairing with prescribed leftovers.**
   `BKLO.exists_classMatched_pairing_cycle_shift` pairs an *unperturbed* link with the cycle
   discipline the invariant charges nothing for; `BKLO.exists_classMatched_pairing_perturbed`
   pairs a perturbed one but leaves the whole sink class over with no discipline at all, which
   `BKLO.RoutedSweepInvCellCount` cannot classify (a whole class exceeds both plans).  The merge
   needs the two together: the three-class cycle of `BKLO.exists_three_class_cycle_block` on the
   corner and the two sink classes — which absorbs *any* imbalance among those three — and, on the
   remaining class pairs, a pairing whose leftovers are **prescribed** inside `L u`, each with a
   **prescribed partner** inside `M u ∩ C (x u h + γ)` for an index `γ` the prover chooses.
2. **A cell plan inside the perturbed link.**  *(Delivered:
   `BKLO.exists_cell_balanced_plan_of_resized_in_link`, `BKLO/AX2CellPlanInLink.lean`.)*
   `BKLO.exists_cell_balanced_plan_of_resized` gives `L w ⊆ resLink R W' w`; the merge needs the
   plan's places inside `X w ∩ resLink R W' w`, since a place the perturbation deletes cannot be
   left over at `u`.  The plan is chosen after `X` in
   `BKLO.RoutedSweepInvCellCountWide6hStep`, so the same construction runs against the pools
   `C i ∩ X w ∩ resLink R W' w`, falling back to `C i ∩ resLink R W' w` at the links where the
   perturbed trace is short — the perturbation hypotheses of the step hold only at the presented
   link.
3. **A foreign plan allotted globally.**  §3: the per-place ceiling `3 K² t` is enough in total but
   not line by line, so the slots have to come from a degree-constrained flow over
   (links × classes), not from `BKLO.exists_balanced_prescription` (one class, one cell) nor from
   `BKLO.exists_locally_balanced_plan`, whose certificate `BKLO.planLoad_le_of_locallyBalanced` is
   the average over a single pool.
4. **A system of free routing indices, spread over the classes the foreign plan serves.**
   *(Shown to be out of reach of the invariant as stated: `BKLO/AX2CountedMergeCaps.lean`.)*
   `BKLO.exists_free_routing_index_at_link_col` and `BKLO.exists_free_routing_index_at_link_row`
   give *one* free index per planned place, and `BKLO.exists_free_routing_index_sharp` shows that
   one is all the counted clause guarantees.  Worse, `BKLO.pool_blocking_affordable` is
   scale-invariant: emptying *every* fibre of *every* place the plan offers one link costs a
   quarter of the plan's own slots along that line, whatever density the plan is built at, so a
   history admitted by `BKLO.RoutedSweepInvCellCount` can close the cross-routed route at a link of
   its choice.  The forced leftovers there have to go foreign, in the classes the perturbation
   chose, and `BKLO.line_local_foreign_demand_exceeds_ceiling` says no ledger-admissible ceiling
   holds them — whereas a *spread* demand would fit
   (`BKLO.uniform_line_foreign_demand_fits`, `BKLO.spread_foreign_allotment_fits`).  The repair is
   a clause of the invariant, not a wider plan: `BKLO.FibreBalanced`
   (`BKLO/AX2FibreBalance.lean`) balances the fibres of a place against the plan's claim on it, is
   maintained by routing at a least-loaded index
   (`BKLO.fibreBalanced_insert_of_least_loaded`), and makes *every* index of every place usable
   (`BKLO.excRouteCount_le_of_fibreBalanced`).
5. **The merge bookkeeping**: `BKLO.excRouteCount_insert_le` at the new link, the extension of
   `BKLO.IsClassMatchedSweep`, and the re-assembly of `BKLO.IsCountClassification` at
   `insert u S`.
-/
import BKLO.AX2CountedMerge
import BKLO.SpreadPlanGlobal

open Finset

namespace BKLO

/-! ### The load bound of a locally balanced plan -/

section AbstractPlan

variable {V : Type*} [DecidableEq V]

/-- **The total load of a plan on any ground set is the total demand.**  Summing the loads of the
places of `G` counts the pairs `(w, a)` with `a ∈ L w`, which is at most `∑ k w`. -/
theorem sum_planLoad_le {S : Finset V} {T : V → Finset V} {k : V → ℕ} {L : V → Finset V}
    (hplan : IsPlan S T k L) (G : Finset V) :
    ∑ a ∈ G, planLoad S L a ≤ ∑ w ∈ S, k w := by
  classical
  have h1 : ∑ a ∈ G, planLoad S L a = ∑ w ∈ S, (G.filter (fun a => a ∈ L w)).card := by
    simp only [planLoad, Finset.card_filter]
    exact Finset.sum_comm
  rw [h1]
  refine Finset.sum_le_sum fun w hw => ?_
  calc (G.filter (fun a => a ∈ L w)).card ≤ (L w).card :=
        Finset.card_le_card (fun a ha => (Finset.mem_filter.1 ha).2)
    _ = k w := hplan.2.1 w hw

/-- **What a locally balanced plan certifies.**  A place chosen at the link `w₀` is used at most one
more time than any unchosen candidate of the pool of `w₀`, so its load is the *average* demand over
that pool, up to one:

```
(load a - 1) · (|T w₀| - k w₀) ≤ ∑_{w ∈ S} k w.
```

This is the whole strength of `BKLO.exists_locally_balanced_plan`: it never sees more than one
link's pool, and therefore never balances a demand that two different pools impose on the same
place. -/
theorem planLoad_le_of_locallyBalanced {S : Finset V} {T : V → Finset V} {k : V → ℕ}
    {L : V → Finset V} (hplan : IsPlan S T k L) (hbal : IsLocallyBalanced S T L)
    {w₀ : V} (hw₀ : w₀ ∈ S) {a : V} (ha : a ∈ L w₀) :
    (planLoad S L a - 1) * ((T w₀).card - k w₀) ≤ ∑ w ∈ S, k w := by
  classical
  set G : Finset V := (T w₀) \ (L w₀) with hG
  have hcard : (T w₀).card - k w₀ ≤ G.card := by
    have h1 : (L w₀).card = k w₀ := hplan.2.1 w₀ hw₀
    have h2 : G.card + (L w₀).card = (T w₀).card :=
      Finset.card_sdiff_add_card_eq_card (hplan.1 w₀ hw₀)
    omega
  have hlow : ∀ b ∈ G, planLoad S L a - 1 ≤ planLoad S L b := by
    intro b hb
    obtain ⟨hbT, hbL⟩ := Finset.mem_sdiff.1 hb
    have := hbal w₀ hw₀ a ha b hbT hbL
    omega
  have h1 : (planLoad S L a - 1) * G.card ≤ ∑ b ∈ G, planLoad S L b := by
    calc (planLoad S L a - 1) * G.card = ∑ _b ∈ G, (planLoad S L a - 1) := by
          rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
      _ ≤ _ := Finset.sum_le_sum hlow
  have h2 := sum_planLoad_le hplan G
  have h3 : (planLoad S L a - 1) * ((T w₀).card - k w₀) ≤ (planLoad S L a - 1) * G.card :=
    Nat.mul_le_mul_left _ hcard
  omega

end AbstractPlan

/-! ### The lines of the design -/

section Design

variable {V : Type} [DecidableEq V]
variable {ε : ℝ} {K : ℕ} {W W' W'' : Finset V} {F R : Finset (Sym2 V)} {C : ℕ → Finset V}
  {x y : V → ℕ} {L M : V → Finset V}

/-- **A row line of the design holds at most `h (20 K² t + 1)` links**: it is the union of the `h`
cells of that row, and `BKLO.twoSided_cell_card_le` bounds each of them. -/
theorem twoSided_row_line_card_le (hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y)
    (p : ℕ) : (((W \ W').filter (fun u => x u = p)).card)
      ≤ gridSize ε K * (20 * (K * K) * gridClassSize ε K W'.card + 1) := by
  classical
  set h : ℕ := gridSize ε K with hhdef
  set t : ℕ := gridClassSize ε K W'.card with htdef
  have hsub : (W \ W').filter (fun u => x u = p)
      ⊆ (Finset.range h).biUnion
        (fun q' => (W \ W').filter (fun u => x u = p ∧ y u = q')) := by
    intro u hu
    obtain ⟨huD, hux⟩ := Finset.mem_filter.1 hu
    exact Finset.mem_biUnion.2 ⟨y u, Finset.mem_range.2 (hgrid.colLt u huD),
      Finset.mem_filter.2 ⟨huD, hux, rfl⟩⟩
  calc (((W \ W').filter (fun u => x u = p)).card)
      ≤ ((Finset.range h).biUnion
          (fun q' => (W \ W').filter (fun u => x u = p ∧ y u = q'))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ q' ∈ Finset.range h, (((W \ W').filter (fun u => x u = p ∧ y u = q')).card) :=
        Finset.card_biUnion_le
    _ ≤ ∑ _q' ∈ Finset.range h, (20 * (K * K) * t + 1) :=
        Finset.sum_le_sum (fun q' _ => twoSided_cell_card_le hgrid p q')
    _ = h * (20 * (K * K) * t + 1) := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

/-- **A column line of the design holds at most `h (20 K² t + 1)` links.** -/
theorem twoSided_col_line_card_le (hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y)
    (q : ℕ) : (((W \ W').filter (fun u => y u = q)).card)
      ≤ gridSize ε K * (20 * (K * K) * gridClassSize ε K W'.card + 1) := by
  classical
  set h : ℕ := gridSize ε K with hhdef
  set t : ℕ := gridClassSize ε K W'.card with htdef
  have hsub : (W \ W').filter (fun u => y u = q)
      ⊆ (Finset.range h).biUnion
        (fun p => (W \ W').filter (fun u => x u = p ∧ y u = q)) := by
    intro u hu
    obtain ⟨huD, huy⟩ := Finset.mem_filter.1 hu
    exact Finset.mem_biUnion.2 ⟨x u, Finset.mem_range.2 (hgrid.rowLt u huD),
      Finset.mem_filter.2 ⟨huD, rfl, huy⟩⟩
  calc (((W \ W').filter (fun u => y u = q)).card)
      ≤ ((Finset.range h).biUnion
          (fun p => (W \ W').filter (fun u => x u = p ∧ y u = q))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ p ∈ Finset.range h, (((W \ W').filter (fun u => x u = p ∧ y u = q)).card) :=
        Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ Finset.range h, (20 * (K * K) * t + 1) :=
        Finset.sum_le_sum (fun p _ => twoSided_cell_card_le hgrid p q)
    _ = h * (20 * (K * K) * t + 1) := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

/-! ### What the two plans can hold inside one class -/

/-- **The global ceiling of the wide foreign plan inside one class**: summed over all the links of
the design, the foreign slots taken inside a class `Ci` are at most `|Ci| · 3 K² t`. -/
theorem wide_plan_class_total_le (hM : ForeignSpreadLeftoverPlanWide ε K W W' M)
    (Ci : Finset V) :
    ∑ w ∈ W \ W', ((M w ∩ Ci).card) ≤ Ci.card * (3 * (K * K) * gridClassSize ε K W'.card) := by
  classical
  have h1 : ∑ w ∈ W \ W', ((M w ∩ Ci).card)
      = ∑ a ∈ Ci, (((W \ W').filter (fun w => a ∈ M w)).card) := by
    have e : ∀ w : V, (M w ∩ Ci).card = (Ci.filter (fun a => a ∈ M w)).card := by
      intro w
      congr 1
      refine Finset.Subset.antisymm (fun a ha => ?_) (fun a ha => ?_)
      · exact Finset.mem_filter.2 ⟨(Finset.mem_inter.1 ha).2, (Finset.mem_inter.1 ha).1⟩
      · exact Finset.mem_inter.2 ⟨(Finset.mem_filter.1 ha).2, (Finset.mem_filter.1 ha).1⟩
    simp only [e, Finset.card_filter]
    exact Finset.sum_comm
  rw [h1]
  calc ∑ a ∈ Ci, (((W \ W').filter (fun w => a ∈ M w)).card)
      ≤ ∑ _a ∈ Ci, (3 * (K * K) * gridClassSize ε K W'.card) :=
        Finset.sum_le_sum (fun a _ => hM a)
    _ = Ci.card * (3 * (K * K) * gridClassSize ε K W'.card) := by
        rw [Finset.sum_const, smul_eq_mul]

/-- **The cell plan is ample on a line**: over the `h` cells of a column line the plan charges a
class at most `|Ci| · h · (5 K² t + 1)` slots in total. -/
theorem cell_plan_line_total_le (hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y)
    (hL : CellSpreadLeftoverPlan ε K W W' x y L) (Ci : Finset V) (q₀ : ℕ) :
    ∑ w ∈ (W \ W').filter (fun w => y w = q₀), ((L w ∩ Ci).card)
      ≤ Ci.card * (gridSize ε K * (5 * (K * K) * gridClassSize ε K W'.card + 1)) := by
  classical
  set h : ℕ := gridSize ε K with hhdef
  set t : ℕ := gridClassSize ε K W'.card with htdef
  set D : Finset V := (W \ W').filter (fun w => y w = q₀) with hD
  have h1 : ∑ w ∈ D, ((L w ∩ Ci).card) = ∑ a ∈ Ci, ((D.filter (fun w => a ∈ L w)).card) := by
    have e : ∀ w : V, (L w ∩ Ci).card = (Ci.filter (fun a => a ∈ L w)).card := by
      intro w
      congr 1
      refine Finset.Subset.antisymm (fun a ha => ?_) (fun a ha => ?_)
      · exact Finset.mem_filter.2 ⟨(Finset.mem_inter.1 ha).2, (Finset.mem_inter.1 ha).1⟩
      · exact Finset.mem_inter.2 ⟨(Finset.mem_filter.1 ha).2, (Finset.mem_filter.1 ha).1⟩
    simp only [e, Finset.card_filter]
    exact Finset.sum_comm
  have hplace : ∀ a : V, (D.filter (fun w => a ∈ L w)).card ≤ h * (5 * (K * K) * t + 1) := by
    intro a
    have hsub : D.filter (fun w => a ∈ L w)
        ⊆ (Finset.range h).biUnion
          (fun p => (W \ W').filter (fun w => x w = p ∧ y w = q₀ ∧ a ∈ L w)) := by
      intro w hw
      obtain ⟨hwD, hwa⟩ := Finset.mem_filter.1 hw
      obtain ⟨hwD', hwy⟩ := Finset.mem_filter.1 hwD
      exact Finset.mem_biUnion.2 ⟨x w, Finset.mem_range.2 (hgrid.rowLt w hwD'),
        Finset.mem_filter.2 ⟨hwD', rfl, hwy, hwa⟩⟩
    calc (D.filter (fun w => a ∈ L w)).card
        ≤ ((Finset.range h).biUnion
            (fun p => (W \ W').filter (fun w => x w = p ∧ y w = q₀ ∧ a ∈ L w))).card :=
          Finset.card_le_card hsub
      _ ≤ ∑ p ∈ Finset.range h,
            (((W \ W').filter (fun w => x w = p ∧ y w = q₀ ∧ a ∈ L w)).card) :=
          Finset.card_biUnion_le
      _ ≤ ∑ _p ∈ Finset.range h, (5 * (K * K) * t + 1) :=
          Finset.sum_le_sum (fun p _ => hL a p q₀)
      _ = h * (5 * (K * K) * t + 1) := by
          rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
  rw [h1]
  calc ∑ a ∈ Ci, ((D.filter (fun w => a ∈ L w)).card)
      ≤ ∑ _a ∈ Ci, (h * (5 * (K * K) * t + 1)) := Finset.sum_le_sum (fun a _ => hplace a)
    _ = Ci.card * (h * (5 * (K * K) * t + 1)) := by rw [Finset.sum_const, smul_eq_mul]

/-! ### What the perturbation forces, class by class -/

/-- **A trace deficit forces leftovers, in the class the perturbation chooses.**

At a swept link `u` the cross-side rule of `BKLO.IsClassMatchedSweep` sends every non-leftover of
the column class `C (α h + y u)` of the region into the row class `C (x u h + σ u α)` the class
matching prescribes, and the pairing is injective there.  So the places of the column class that
the matched row class cannot absorb are leftovers of `u`. -/
theorem trace_deficit_forces_leftovers
    (hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y)
    {X : V → Finset V} {ρ σ : V → ℕ → ℕ} {S : Finset V} {g : V → V → V} {Exc : V → Finset V}
    (hsweep : IsClassMatchedSweep (gridSize ε K) C R W' X x y ρ σ S g Exc)
    {u : V} (hu : u ∈ W \ W') (huS : u ∈ S)
    (hmaps : ∀ a ∈ X u, g u a ∈ X u) (hginv : ∀ a ∈ X u, g u (g u a) = a)
    {α : ℕ} (hα : α < gridSize ε K) (hαne : α ≠ x u) :
    ((C (α * gridSize ε K + y u) ∩ X u ∩ resLink R W' u).card)
      ≤ ((C (x u * gridSize ε K + σ u α) ∩ X u).card)
        + ((Exc u ∩ C (α * gridSize ε K + y u)).card) := by
  classical
  set h : ℕ := gridSize ε K with hhdef
  have hyu : y u < h := hgrid.colLt u hu
  set A : Finset V :=
    (C (α * h + y u) ∩ X u ∩ resLink R W' u) \ (Exc u) with hAdef
  -- the non-leftovers of the class are sent into the matched row class, injectively
  have himg : ∀ a ∈ A, g u a ∈ C (x u * h + σ u α) ∩ X u := by
    intro a ha
    obtain ⟨haC, haE⟩ := Finset.mem_sdiff.1 ha
    obtain ⟨haCX, haR⟩ := Finset.mem_inter.1 haC
    obtain ⟨haCl, haX⟩ := Finset.mem_inter.1 haCX
    have hrule := hsweep a α (y u) hα hyu haCl u huS haX haR haE
    rcases hrule with hcase | hcase
    · exact absurd hcase.1.symm hαne
    · exact Finset.mem_inter.2 ⟨hcase.2, hmaps a haX⟩
  have hinj : ∀ a ∈ A, ∀ b ∈ A, g u a = g u b → a = b := by
    intro a ha b hb hab
    have haX : a ∈ X u := (Finset.mem_inter.1 (Finset.mem_inter.1
      (Finset.mem_sdiff.1 ha).1).1).2
    have hbX : b ∈ X u := (Finset.mem_inter.1 (Finset.mem_inter.1
      (Finset.mem_sdiff.1 hb).1).1).2
    calc a = g u (g u a) := (hginv a haX).symm
      _ = g u (g u b) := by rw [hab]
      _ = b := hginv b hbX
  have hcardA : A.card ≤ (C (x u * h + σ u α) ∩ X u).card :=
    Finset.card_le_card_of_injOn (fun a => g u a) himg (fun a ha b hb hab => hinj a ha b hb hab)
  have hsplit : (C (α * h + y u) ∩ X u ∩ resLink R W' u).card
      ≤ A.card + (Exc u ∩ C (α * h + y u)).card := by
    have hsub : (C (α * h + y u) ∩ X u ∩ resLink R W' u)
        ⊆ A ∪ (Exc u ∩ C (α * h + y u)) := by
      intro a ha
      by_cases hE : a ∈ Exc u
      · exact Finset.mem_union_right _ (Finset.mem_inter.2
          ⟨hE, (Finset.mem_inter.1 (Finset.mem_inter.1 ha).1).1⟩)
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.2 ⟨ha, hE⟩)
    calc (C (α * h + y u) ∩ X u ∩ resLink R W' u).card
        ≤ (A ∪ (Exc u ∩ C (α * h + y u))).card := Finset.card_le_card hsub
      _ ≤ A.card + (Exc u ∩ C (α * h + y u)).card := Finset.card_union_le _ _
  omega

/-- **A forced leftover of a column class is planned or foreign.**  This is
`BKLO.count_partner_forced_or_foreign` in the shape the balance sheet uses: a leftover `z` of the
column class `C (α h + y u)` whose partner lies in a row class of the region other than the sink
one is a slot of the foreign plan, or a slot of the cell plan whose routing index is forced. -/
theorem column_leftover_planned_or_foreign
    (hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y)
    {φ : V → ℕ} {S : Finset V} {g : V → V → V} {Exc : V → Finset V}
    {Cc Cr Pc Pr Fo Po : V → Finset V} {rt : V → V → ℕ} (hSD : S ⊆ W \ W')
    (hcls : IsCountClassification ε K W' C x y φ L M S g Exc Cc Cr Pc Pr Fo Po rt)
    {u : V} (hu : u ∈ S) {z : V} {α γ : ℕ}
    (hγ : γ < gridSize ε K) (hα : α < gridSize ε K)
    (hzC : z ∈ C (α * gridSize ε K + y u)) (hzExc : z ∈ Exc u)
    (hpartner : g u z ∈ C (x u * gridSize ε K + γ))
    (hαne : α ≠ x u) (hγne : γ ≠ crossShiftInv (gridSize ε K) φ (x u) u) :
    z ∈ M u ∨ z ∈ L u := by
  rcases count_partner_forced_or_foreign (W'' := W'') (F := F) (R := R) hgrid hSD hcls hu hγ hα
    hpartner hzC hzExc rfl hαne hγne with hfor | hrow
  · exact Or.inl hfor
  · exact Or.inr (hcls.2.2.2.2.2.2.1 u hu hrow.1)

/-- **The balance sheet of one class at one link.**  Combining the two previous results: the places
of a column class of the region that the matched row class cannot absorb have to be held by the
cell plan or by the foreign plan, in that very class. -/
theorem class_deficit_le_plans
    (hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y)
    {X : V → Finset V} {φ : V → ℕ} {S : Finset V} {g : V → V → V} {Exc : V → Finset V}
    {Cc Cr Pc Pr Fo Po : V → Finset V} {rt : V → V → ℕ} (hSD : S ⊆ W \ W')
    (hsweep : IsClassMatchedSweep (gridSize ε K) C R W' X x y
      (fun w β => crossShift (gridSize ε K) φ β w)
      (fun w a => crossShiftInv (gridSize ε K) φ a w) S g Exc)
    (hcls : IsCountClassification ε K W' C x y φ L M S g Exc Cc Cr Pc Pr Fo Po rt)
    {u : V} (huS : u ∈ S)
    (hmaps : ∀ a ∈ X u, g u a ∈ X u) (hginv : ∀ a ∈ X u, g u (g u a) = a)
    {α : ℕ} (hα : α < gridSize ε K) (hαne : α ≠ x u)
    -- the partners of the leftovers of this class lie in row classes of the region, away from the
    -- sink one: this is what the pairing of the merge produces
    (hpart : ∀ z ∈ Exc u ∩ C (α * gridSize ε K + y u), ∃ γ < gridSize ε K,
      γ ≠ crossShiftInv (gridSize ε K) φ (x u) u ∧ g u z ∈ C (x u * gridSize ε K + γ)) :
    ((C (α * gridSize ε K + y u) ∩ X u ∩ resLink R W' u).card)
      ≤ ((C (x u * gridSize ε K + crossShiftInv (gridSize ε K) φ α u) ∩ X u).card)
        + ((M u ∩ C (α * gridSize ε K + y u)).card)
        + ((L u ∩ C (α * gridSize ε K + y u)).card) := by
  classical
  have hu : u ∈ W \ W' := hSD huS
  have hdef := trace_deficit_forces_leftovers (W := W) (W'' := W'') (F := F) hgrid
    (X := X) (ρ := fun w β => crossShift (gridSize ε K) φ β w)
    (σ := fun w a => crossShiftInv (gridSize ε K) φ a w) hsweep hu huS hmaps hginv hα hαne
  simp only [] at hdef
  -- every leftover of the class is a slot of one of the two plans
  have hcover : Exc u ∩ C (α * gridSize ε K + y u)
      ⊆ (M u ∩ C (α * gridSize ε K + y u)) ∪ (L u ∩ C (α * gridSize ε K + y u)) := by
    intro z hz
    obtain ⟨hzE, hzC⟩ := Finset.mem_inter.1 hz
    obtain ⟨γ, hγ, hγne, hpz⟩ := hpart z hz
    rcases column_leftover_planned_or_foreign (W'' := W'') (F := F) (R := R) hgrid hSD hcls huS
      hγ hα hzC hzE hpz hαne hγne with hM | hL
    · exact Finset.mem_union_left _ (Finset.mem_inter.2 ⟨hM, hzC⟩)
    · exact Finset.mem_union_right _ (Finset.mem_inter.2 ⟨hL, hzC⟩)
  have hcard : (Exc u ∩ C (α * gridSize ε K + y u)).card
      ≤ (M u ∩ C (α * gridSize ε K + y u)).card + (L u ∩ C (α * gridSize ε K + y u)).card :=
    le_trans (Finset.card_le_card hcover) (Finset.card_union_le _ _)
  omega

end Design

/-! ### The two counts of the finding -/

/-- **The uniform allocation overshoots.**  Write the sizes of the design at the floor the design
admits: `t = 16 D` for the maximal perturbation `D = t / 16`, and `q = 12 D`, i.e. `4 q = 3 t`, the
floor of `IsGridTwoSidedReservoir.classCardGe`.  A class is served by two lines of
`h (20 K² t + 1)` links each (`BKLO.twoSided_row_line_card_le`,
`BKLO.twoSided_col_line_card_le`); if every one of them spreads its `D` foreign partners uniformly
over the `h` classes of the line, the class receives `2 (20 K² t + 1) D` slots, and that is more
than the `q · 3 K² t` the wide plan can hold. -/
theorem uniform_line_demand_exceeds_class_capacity {K D : ℕ} (hK : 2 ≤ K) (hD : 0 < D) :
    (12 * D) * (3 * (K * K) * (16 * D)) < 2 * (20 * (K * K) * (16 * D) + 1) * D := by
  have hKK : 4 ≤ K * K := Nat.mul_le_mul hK hK
  have e1 : (12 * D) * (3 * (K * K) * (16 * D)) = 576 * ((K * K) * (D * D)) := by ring
  have e2 : 2 * (20 * (K * K) * (16 * D) + 1) * D = 640 * ((K * K) * (D * D)) + 2 * D := by ring
  have hpos : 0 < (K * K) * (D * D) := by positivity
  omega

/-- **Globally the wide plan has the room, with a factor `1.8` to spare.**  At the same sizes, the
whole demand of the design — one foreign partner per unit of perturbation at each of its
`h² (20 K² t + 1)` links — is `h² (20 K² t + 1) D` against a capacity `h² · q · 3 K² t`. -/
theorem global_demand_fits_class_capacity {K D : ℕ} (hK : 2 ≤ K) :
    (20 * (K * K) * (16 * D) + 1) * D ≤ (12 * D) * (3 * (K * K) * (16 * D)) + D := by
  have hKK : 4 ≤ K * K := Nat.mul_le_mul hK hK
  have e1 : (20 * (K * K) * (16 * D) + 1) * D = 320 * ((K * K) * (D * D)) + D := by ring
  have e2 : (12 * D) * (3 * (K * K) * (16 * D)) = 576 * ((K * K) * (D * D)) := by ring
  omega

/-- **The numeric form of the gap.**  At `K = 2`, `h = 25600`, `t = 6 h = 153600`, the floor class
size `q = 3 t / 4 = 115200` and the maximal perturbation `D = t / 16 = 9600`: the uniform
allocation asks a class for `235 929 619 200` foreign slots where the wide plan holds
`212 336 640 000` — an overshoot of `10 / 9` — while the global count,
`117 964 809 600 ≤ 212 336 640 000`, has a factor `1.8` to spare. -/
theorem foreign_allocation_gap_witness :
    115200 * (3 * (2 * 2) * 153600) < 2 * (20 * (2 * 2) * 153600 + 1) * 9600 ∧
      (20 * (2 * 2) * 153600 + 1) * 9600 ≤ 115200 * (3 * (2 * 2) * 153600) := by
  norm_num

end BKLO

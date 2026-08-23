/-
# The routed residual of AX2 §10, against a **cell-balanced leftover plan**

Two forms of the one-link routed step of AX2 §10 are refuted in this development:

* `BKLO.not_routedSweepInvGenStep` (`BKLO/AX2GenStepObstruction.lean`) — the flat cap of
  `BKLO.RoutedSweepInvGen` cannot be stepped, because the sweep handed to the step is only assumed
  to satisfy the invariant and may already hold every counter of every place of a class at the cap;
* `BKLO.not_routedSweepInvSpreadStep` (`BKLO/AX2SpreadStepObstruction.lean`) — the repair by a
  *globally* spread plan (`BKLO.SpreadLeftoverPlan`) asks for a factor `h` more than a plan can
  give, because a whole grid line of links may attack one class.

This file carries out the repair the two obstructions leave open, and which the counters of
`BKLO.RoutedSweepInvGen` actually ask for: a plan balanced **per cell** — no place is planned at
more than `5 K² t + 1` links of any one cell, which is exactly what
`BKLO.exists_cell_balanced_leftovers` produces — together with the two structural conditions that
make each of the four counters a *count of one cell*:

* a column-routed leftover is a place of the **row** part of the region of its link (so the
  leftover's own class pins the grid row of the link), and a row-routed leftover is a place of the
  **column** part (so it pins the grid column);
* the routing fibre pins the other coordinate: two links routing the same place by the same index
  lie in the same grid column (resp. row).

Under those, all four counters of `BKLO.RoutedSweepInvGen` are bounded by the per-cell load of the
plan, and the global count that defeats `BKLO.SpreadLeftoverPlan` never arises.

* `BKLO.CellSpreadLeftoverPlan` — the per-cell spread condition on a plan;
* `BKLO.RoutedSweepInvCell` — the repaired invariant;
* `BKLO.excRouteCount_le_of_cellPlan_col`, `BKLO.excRouteCount_le_of_cellPlan_row` — a counter of a
  cell-pinned routing is a count of one cell;
* `BKLO.routedSweepInvGen_of_routedSweepInvCell` — the repaired invariant implies
  `BKLO.RoutedSweepInvGen`;
* `BKLO.routedSweepInvCell_empty`, `BKLO.excLedgerSpread_of_routedSweepInvCell` — the two easy
  halves of the demand;
* `BKLO.RoutedSweepInvCellStep` — the one-link step for the repaired invariant, and
* `BKLO.twoSidedUsedClassMatchedQuarterPairing_of_cell_step` — the residual demand of AX2 §10 from
  it.

Neither obstruction applies to `BKLO.RoutedSweepInvCellStep`: the plan is fixed in advance (so a
saturated sweep is impossible, unlike `BKLO.RoutedSweepInvGenStep`), its load is asked cell by cell
and not globally (unlike `BKLO.RoutedSweepInvSpreadStep`), and the routing index of a forced
leftover is free (unlike `BKLO.RoutedSweepInvStep`).

Everything here is `sorry`-free; the one-link step `BKLO.RoutedSweepInvCellStep` is *not* proved —
it is what remains of the AX2 §10 residual in this development.
-/
import BKLO.AX2RoutedResidualGen

open Finset

namespace BKLO

variable {V : Type} [DecidableEq V]
variable {ε : ℝ} {K : ℕ} {W W' W'' : Finset V} {F R : Finset (Sym2 V)} {C : ℕ → Finset V}
  {x y : V → ℕ} {L : V → Finset V}

/-! ### The plan and the invariant -/

/-- **A cell-balanced leftover plan.**  `L w` is the set of places of the reservoir at which the
link `w` is allowed to leave a forced leftover, and the plan is balanced when no place is planned
at more than `5 K² t + 1` links of any single cell of the grid.  This is the load
`BKLO.exists_cell_balanced_leftovers` achieves: a cell carries at most `20 K² t + 1` links
(`BKLO.twoSided_cell_card_le`) and the balanced prescription charges a place a quarter of them. -/
def CellSpreadLeftoverPlan (ε : ℝ) (K : ℕ) (W W' : Finset V) (x y : V → ℕ) (L : V → Finset V) :
    Prop :=
  ∀ (a : V) (p q : ℕ), (((W \ W').filter (fun w => x w = p ∧ y w = q ∧ a ∈ L w)).card)
    ≤ 5 * (K * K) * gridClassSize ε K W'.card + 1

/-- **The routed invariant of a class-matched sweep against a cell-balanced plan.**  As
`BKLO.RoutedSweepInvGen`, with the four counters replaced by the plan and the two conditions that
turn a counter into a count of one cell: a column-routed leftover is a place of the row part of the
region of its link and a row-routed leftover a place of the column part, and the routing fibre pins
the remaining coordinate of the cell. -/
def RoutedSweepInvCell (ε : ℝ) (K : ℕ) (W W' : Finset V) (C : ℕ → Finset V) (x y φ : V → ℕ)
    (L : V → Finset V) (S : Finset V) (g : V → V → V) (Exc : V → Finset V) : Prop :=
  S ⊆ W \ W' ∧
  ∃ (Cc Cr Pc Pr : V → Finset V) (rt : V → V → ℕ),
    -- the leftovers split into the cycle part and the forced part
    (∀ w ∈ S, Exc w ⊆ (Cc w ∪ Cr w) ∪ (Pc w ∪ Pr w)) ∧
    (∀ w ∈ S, ∀ a ∈ Cr w, a ∉ Cc w) ∧
    -- the cycle part obeys the three-class cycle discipline
    IsCycleRoutedLeftover (gridSize ε K) C x y φ S g Cc Cr ∧
    -- the forced part is cross-routed, by an index of the region
    (∀ w ∈ S, ∀ b : V, rt w b < gridSize ε K) ∧
    IsCrossRoutedLeftover (gridSize ε K) C x y rt S g Pc Pr ∧
    -- the forced leftovers are planned, and lie on the cross side of their own region
    (∀ w ∈ S, Pc w ⊆ L w) ∧ (∀ w ∈ S, Pr w ⊆ L w) ∧
    (∀ w ∈ S, ∀ a ∈ Pc w, ∃ β < gridSize ε K, a ∈ C (x w * gridSize ε K + β)) ∧
    (∀ w ∈ S, ∀ a ∈ Pr w, ∃ α < gridSize ε K, a ∈ C (α * gridSize ε K + y w)) ∧
    -- and the routing fibre pins the remaining coordinate of the cell
    (∀ w ∈ S, ∀ w' ∈ S, ∀ a : V, a ∈ Pc w → a ∈ Pc w' → rt w a = rt w' a → y w = y w') ∧
    (∀ w ∈ S, ∀ w' ∈ S, ∀ a : V, a ∈ Pr w → a ∈ Pr w' → rt w a = rt w' a → x w = x w')

/-- The empty sweep satisfies the invariant, against any plan. -/
theorem routedSweepInvCell_empty (φ : V → ℕ) (L : V → Finset V) :
    RoutedSweepInvCell ε K W W' C x y φ L (∅ : Finset V) (fun _ a => a) (fun _ => ∅) := by
  classical
  refine ⟨Finset.empty_subset _, (fun _ => ∅), (fun _ => ∅), (fun _ => ∅), (fun _ => ∅),
    (fun _ _ => 0), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    intro a ha <;> simp_all

/-! ### A cell-balanced plan gives the counters -/

/-- **A counter of a column-routed, cell-pinned leftover discipline is a count of one cell.**  The
leftover's own class pins the grid row of every link the counter counts, and the fibre of the
counter pins the grid column; so the counter is bounded by the load of the plan on that one
cell. -/
theorem excRouteCount_le_of_cellPlan_col
    (hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y)
    {S : Finset V} {Pc : V → Finset V}
    (hSD : S ⊆ W \ W') (hL : CellSpreadLeftoverPlan ε K W W' x y L)
    (hPcL : ∀ w ∈ S, Pc w ⊆ L w)
    (hPcRow : ∀ w ∈ S, ∀ a ∈ Pc w, ∃ β < gridSize ε K, a ∈ C (x w * gridSize ε K + β))
    (a : V) (pf : V → ℕ)
    (hpin : ∀ w ∈ S, ∀ w' ∈ S, a ∈ Pc w → a ∈ Pc w' → pf w = pf w' → y w = y w')
    (P : ℕ) :
    excRouteCount S Pc a pf P ≤ 5 * (K * K) * gridClassSize ε K W'.card + 1 := by
  classical
  set h : ℕ := gridSize ε K with hhdef
  rcases Finset.eq_empty_or_nonempty (S.filter (fun w => a ∈ Pc w ∧ pf w = P)) with h0 | ⟨w₀, hw₀⟩
  · simp only [excRouteCount, h0, Finset.card_empty]
    exact Nat.zero_le _
  obtain ⟨hw0S, hw0a, hw0p⟩ := Finset.mem_filter.1 hw₀
  refine le_trans (Finset.card_le_card ?_) (hL a (x w₀) (y w₀))
  intro w hw
  obtain ⟨hwS, hwa, hwp⟩ := Finset.mem_filter.1 hw
  refine Finset.mem_filter.2 ⟨hSD hwS, ?_, ?_, hPcL w hwS hwa⟩
  · obtain ⟨β, hβ, hmem⟩ := hPcRow w hwS a hwa
    obtain ⟨β₀, hβ₀, hmem₀⟩ := hPcRow w₀ hw0S a hw0a
    by_cases heq : x w * h + β = x w₀ * h + β₀
    · exact (gridDigits_inj hβ hβ₀ heq).1
    · exact ((Finset.disjoint_left.1
        (hgrid.classDisjoint _ (grid_idx_lt (hgrid.rowLt w (hSD hwS)) hβ) _
          (grid_idx_lt (hgrid.rowLt w₀ (hSD hw0S)) hβ₀) heq) hmem) hmem₀).elim
  · exact hpin w hwS w₀ hw0S hwa hw0a (by rw [hwp, hw0p])

/-- **A counter of a row-routed, cell-pinned leftover discipline is a count of one cell.** -/
theorem excRouteCount_le_of_cellPlan_row
    (hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y)
    {S : Finset V} {Pr : V → Finset V}
    (hSD : S ⊆ W \ W') (hL : CellSpreadLeftoverPlan ε K W W' x y L)
    (hPrL : ∀ w ∈ S, Pr w ⊆ L w)
    (hPrCol : ∀ w ∈ S, ∀ a ∈ Pr w, ∃ α < gridSize ε K, a ∈ C (α * gridSize ε K + y w))
    (a : V) (pf : V → ℕ)
    (hpin : ∀ w ∈ S, ∀ w' ∈ S, a ∈ Pr w → a ∈ Pr w' → pf w = pf w' → x w = x w')
    (P : ℕ) :
    excRouteCount S Pr a pf P ≤ 5 * (K * K) * gridClassSize ε K W'.card + 1 := by
  classical
  set h : ℕ := gridSize ε K with hhdef
  rcases Finset.eq_empty_or_nonempty (S.filter (fun w => a ∈ Pr w ∧ pf w = P)) with h0 | ⟨w₀, hw₀⟩
  · simp only [excRouteCount, h0, Finset.card_empty]
    exact Nat.zero_le _
  obtain ⟨hw0S, hw0a, hw0p⟩ := Finset.mem_filter.1 hw₀
  refine le_trans (Finset.card_le_card ?_) (hL a (x w₀) (y w₀))
  intro w hw
  obtain ⟨hwS, hwa, hwp⟩ := Finset.mem_filter.1 hw
  refine Finset.mem_filter.2 ⟨hSD hwS, ?_, ?_, hPrL w hwS hwa⟩
  · exact hpin w hwS w₀ hw0S hwa hw0a (by rw [hwp, hw0p])
  · obtain ⟨α, hα, hmem⟩ := hPrCol w hwS a hwa
    obtain ⟨α₀, hα₀, hmem₀⟩ := hPrCol w₀ hw0S a hw0a
    by_cases heq : α * h + y w = α₀ * h + y w₀
    · exact (gridDigits_inj (hgrid.colLt w (hSD hwS)) (hgrid.colLt w₀ (hSD hw0S)) heq).2
    · exact ((Finset.disjoint_left.1
        (hgrid.classDisjoint _ (grid_idx_lt hα (hgrid.colLt w (hSD hwS))) _
          (grid_idx_lt hα₀ (hgrid.colLt w₀ (hSD hw0S))) heq) hmem) hmem₀).elim

/-- **The planned invariant implies the general routed invariant**, when the plan is balanced on
every cell. -/
theorem routedSweepInvGen_of_routedSweepInvCell
    (hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y)
    {φ : V → ℕ} {S : Finset V} {g : V → V → V} {Exc : V → Finset V}
    (hL : CellSpreadLeftoverPlan ε K W W' x y L)
    (hInv : RoutedSweepInvCell ε K W W' C x y φ L S g Exc) :
    RoutedSweepInvGen ε K W W' C x y φ S g Exc := by
  classical
  obtain ⟨hSD, Cc, Cr, Pc, Pr, rt, hsplit, hdisjC, hcyc, hrtlt, hroute, hPcL, hPrL, hPcRow,
    hPrCol, hpinC, hpinR⟩ := hInv
  refine ⟨hSD, Cc, Cr, Pc, Pr, rt, hsplit, hdisjC, hcyc, hrtlt, hroute, ?_, ?_, ?_, ?_⟩
  · intro a P
    exact excRouteCount_le_of_cellPlan_col (W'' := W'') (F := F) (R := R) hgrid hSD hL hPcL
      hPcRow a (fun w => rt w a)
      (fun w hw w' hw' ha ha' hpf => hpinC w hw w' hw' a ha ha' hpf) P
  · intro a Q
    exact excRouteCount_le_of_cellPlan_col (W'' := W'') (F := F) (R := R) hgrid hSD hL hPcL
      hPcRow a y (fun w _ w' _ _ _ hpf => hpf) Q
  · intro a P
    exact excRouteCount_le_of_cellPlan_row (W'' := W'') (F := F) (R := R) hgrid hSD hL hPrL
      hPrCol a x (fun w _ w' _ _ _ hpf => hpf) P
  · intro a Q
    exact excRouteCount_le_of_cellPlan_row (W'' := W'') (F := F) (R := R) hgrid hSD hL hPrL
      hPrCol a (fun w => rt w a)
      (fun w hw w' hw' ha ha' hpf => hpinR w hw w' hw' a ha ha' hpf) Q

/-- **The planned invariant keeps the leftover ledger spread.** -/
theorem excLedgerSpread_of_routedSweepInvCell
    (hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y)
    (hε : 0 < ε) (hε' : ε ≤ 1 / 100) (hK : 2 ≤ K)
    (ht : 512 ≤ gridClassSize ε K W'.card)
    {φ : V → ℕ} (hφlt : ∀ w, φ w < gridSize ε K)
    (hbal : ∀ p q j : ℕ, (((W \ W').filter (fun w => x w = p ∧ y w = q ∧ φ w = j)).card)
      ≤ (((W \ W').filter (fun w => x w = p ∧ y w = q)).card) / gridSize ε K + 1)
    (hL : CellSpreadLeftoverPlan ε K W W' x y L)
    {S : Finset V} {g : V → V → V} {Exc : V → Finset V}
    (hInv : RoutedSweepInvCell ε K W W' C x y φ L S g Exc) :
    ExcLedgerSpread ε K W' C g S Exc :=
  excLedgerSpread_of_routedSweepInvGen (W'' := W'') (F := F) (R := R) hgrid hε hε' hK ht hφlt hbal
    (routedSweepInvGen_of_routedSweepInvCell (W'' := W'') (F := F) (R := R) hgrid hL hInv)

/-! ### The residual, from the planned one-link step -/

/-- **The one-link routed step against a cell-balanced plan.**  A design and a cell-balanced shift
admit a plan `L`, balanced on every cell, such that every link can be paired — by `F`-edges
avoiding the used ones — with its cycle leftovers routed by the three-class cycle and its forced
leftovers cross-routed inside `L`, on the cross side of their own region and with a routing index
whose fibres pin the cell.

This is what remains of the AX2 §10 residual.  Unlike `BKLO.RoutedSweepInvGenStep` the obligation
on the new link does not depend on the sweep already made — the plan is fixed in advance — and
unlike `BKLO.RoutedSweepInvSpreadStep` its load is asked one cell at a time, which is what
`BKLO.exists_cell_balanced_leftovers` delivers. -/
def RoutedSweepInvCellStep : Prop :=
  ∀ {V : Type} [DecidableEq V] {ε : ℝ} {K : ℕ} {W W' W'' : Finset V}
    {F R : Finset (Sym2 V)} {C : ℕ → Finset V} {x y : V → ℕ} {q c : ℕ},
    IsGridTwoSidedReservoir ε K W W' W'' F R C x y →
    (∀ e ∈ F, ¬ e.IsDiag) → W' ⊆ W →
    (∀ i < gridSize ε K * gridSize ε K, (C i).card = q) →
    (∀ v ∈ W \ W', ∀ i ∈ gridIdx (gridSize ε K) (x v) (y v),
      (resLink R W' v ∩ C i).card = c) →
    3 * q ≤ 4 * c →
    0 < ε → ε ≤ 1 / 100 → 2 ≤ K → 512 ≤ gridClassSize ε K W'.card →
    ∀ {φ : V → ℕ}, (∀ w, φ w < gridSize ε K) →
    (∀ p q j : ℕ, (((W \ W').filter (fun w => x w = p ∧ y w = q ∧ φ w = j)).card)
      ≤ (((W \ W').filter (fun w => x w = p ∧ y w = q)).card) / gridSize ε K + 1) →
    ∀ {X : V → Finset V},
    ∃ L : V → Finset V, CellSpreadLeftoverPlan ε K W W' x y L ∧
      ∀ {S : Finset V} {g₀ : V → V → V} {Exc : V → Finset V} {u : V} {n m : ℕ}
        {U : Finset (Sym2 V)},
      u ∈ W \ W' → X u ⊆ W' → Even (X u).card →
      4 * (X u \ resLink R W' u).card ≤ gridClassSize ε K W'.card →
      4 * (resLink R W' u \ X u).card ≤ gridClassSize ε K W'.card →
      (X u \ resLink R W' u).card ≤ n → (resLink R W' u \ X u).card ≤ n →
      (∀ a ∈ X u, (resLink U (X u) a).card ≤ m) →
      UsedForbidden X g₀ S W'' U →
      12 * n + 8 * m ≤ (2 * gridSize ε K - 1) * c →
      S ⊆ W \ W' → u ∉ S →
      (∀ w ∈ S, ∀ b ∈ X w, g₀ w b ∈ X w) → (∀ w ∈ S, ∀ b ∈ X w, g₀ w (g₀ w b) = b) →
      IsClassMatchedSweep (gridSize ε K) C R W' X x y
        (fun w β => crossShift (gridSize ε K) φ β w)
        (fun w α => crossShiftInv (gridSize ε K) φ α w) S g₀ Exc →
      RoutedSweepInvCell ε K W W' C x y φ L S g₀ Exc →
      ∃ (p : V → V) (e : Finset V),
        (∀ a ∈ X u, p a ∈ X u) ∧ (∀ a ∈ X u, p (p a) = a) ∧ (∀ a ∈ X u, p a ≠ a) ∧
        (∀ a ∈ X u, s(a, p a) ∈ F ∧ s(a, p a) ∉ U) ∧
        IsClassMatchedSweep (gridSize ε K) C R W' X x y
          (fun w β => crossShift (gridSize ε K) φ β w)
          (fun w α => crossShiftInv (gridSize ε K) φ α w)
          (insert u S) (Function.update g₀ u p) (Function.update Exc u e) ∧
        RoutedSweepInvCell ε K W W' C x y φ L (insert u S) (Function.update g₀ u p)
          (Function.update Exc u e)

/-- **The residual demand of AX2 §10, from the one-link routed step against a cell-balanced
plan.** -/
theorem twoSidedUsedClassMatchedQuarterPairing_of_cell_step (hstep : RoutedSweepInvCellStep) :
    TwoSidedUsedClassMatchedQuarterPairing := by
  intro V _ ε K W W' W'' F R C x y q c X hgrid hnd hW'W hq hcres hqc hε hε' hK hbig
  classical
  obtain ⟨φ, hφlt, hφcell⟩ :=
    exists_cell_balanced_shift (W \ W') x y (gridSize_pos ε K)
  obtain ⟨L, hL, hstep'⟩ :=
    hstep hgrid hnd hW'W hq hcres hqc hε hε' hK hbig hφlt hφcell (X := X)
  refine ⟨fun w β => crossShift (gridSize ε K) φ β w,
    fun w α => crossShiftInv (gridSize ε K) φ α w,
    RoutedSweepInvCell ε K W W' C x y φ L,
    fun w β => crossShift_lt (gridSize_pos ε K) φ β w,
    fun w α => crossShiftInv_lt (gridSize_pos ε K) φ α w,
    classMatchingFibres_of_cellBalanced hgrid hφlt hφcell,
    routedSweepInvCell_empty φ L, ?_, ?_⟩
  · intro S g Exc hInv
    exact excLedgerSpread_of_routedSweepInvCell (W'' := W'') (F := F) (R := R) hgrid hε hε' hK
      hbig hφlt hφcell hL hInv
  · intro S g₀ Exc u n m U hu hXu hXeven hadd4 hdel4 hadd hdel hUdeg hUused hmargin hSD huS
      hmaps hginv hsweep hInv
    exact hstep' hu hXu hXeven hadd4 hdel4 hadd hdel hUdeg hUused hmargin hSD huS hmaps hginv
      hsweep hInv

end BKLO

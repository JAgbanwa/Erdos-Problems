/-
# The counted routed residual: index supply, foreign demand, and the repaired vehicle

`BKLO.RoutedSweepInvCellCountStep` (`BKLO/AX2RoutedResidualCellCount.lean`) is the one-link step of
the **counted** routed invariant: the two fibre pins of `BKLO.RoutedSweepInvCellFree` are replaced
by the two fibre *counts* the ledger actually consumes, so nothing constrains the partner of a
forced leftover beyond its class.

This file audits the merge that the counted invariant is meant to admit, and records what it
delivers and what it still costs.

## 1. The index supply is there — unconditionally

`BKLO.exists_free_routing_index` needs the *whole* planned history of a place to be shorter than
`(5 K² t + 1) h`.  For a place planned at the new link this is a theorem, not an assumption:

* `BKLO.planned_row_line_card_lt` — a place `a` planned at the link `u ∉ S` is a cross-routed
  leftover of the history at fewer than `(5 K² t + 1) h` links, because a column-routed leftover
  lies in a row class of *its own* link, so all those links share the grid row of `u`, the cell
  balance of `BKLO.CellSpreadLeftoverPlan` gives `5 K² t + 1` per cell, and the cell of `u` itself
  already spends one of its `5 K² t + 1` tickets on `u`;
* `BKLO.exists_free_routing_index_at_link_col`, `BKLO.exists_free_routing_index_at_link_row` — hence a
  routing index with room for one more link always exists, at every place the plan offers, on both
  sides.  This is the exact sense in which the counted clause is never blocked by the history: the
  wall of `BKLO.routed_index_collision` is gone.

## 2. What the merge still has to pay: one *foreign* slot per forced leftover

The partner of a cross-routed leftover is not free of charge, and the counted invariant does not
make it free.  `BKLO.count_partner_forced_or_foreign` isolates the trilemma: if `a` is a leftover
of `u` in a row class `C (x u · h + γ)` and its partner `z` lies in the column class
`C (α h + y u)`, then in any classification carrying `BKLO.RoutedSweepInvCellCount` the partner `z`
is

* a **cycle** leftover — possible only when `γ` is the sink index `crossShiftInv h φ (x u) u`; or
* a **row-routed** leftover, and then its own routing index is *forced*: `rt u z = γ`; or
* a **foreign** leftover, `z ∈ M u`.

The first is unavailable at a general `γ`, and the second is the one place where the history can
still block, since `γ` is dictated by the perturbation and not chosen by the prover.  So a merge
that never needs a *forced* index has to book one foreign slot per forced leftover — one per unit
of perturbation, `(t/32)`-many at a link — and `BKLO.ForeignSpreadLeftoverPlan`, whose ceiling is
`K² t`, is short of that demand:

* `BKLO.foreign_demand_exceeds_capacity` — the double count, at the design's own capacity: with
  `N ≤ 20 K² t + 1` links per cell, `2 h - 1` cells meeting a class, one foreign slot per unit of
  a perturbation of size `t / 32` and a pool of `(2 h - 1) c` places per link, some place is
  planned at more than `K² t` links.  The witness
  `BKLO.foreign_demand_exceeds_capacity_witness` makes the numbers explicit at `K = 2`, `t = 512`,
  `h = 25600`, `D = 32`, `c = 448`;
* `BKLO.blocked_partners_are_foreign` — the bridge: when the forced index of those partners is
  blocked, the whole perturbation lands in the foreign plan;
* `BKLO.foreignPlan_cannot_meet_merge_demand`, `BKLO.merge_route_obstruction` — the obstruction
  itself: those data are contradictory, so the prescribed route cannot complete the one-link step
  against the `K² t` foreign capacity of `BKLO.RoutedSweepInvCellCountStep`.

All of §1 and §2 are stated for a **fixed** classification `BKLO.IsCountClassification` of the
sweep, never for a re-existentialised one: the witnesses of `BKLO.RoutedSweepInvCellCount` are
existentially bound, and a conclusion that re-binds them is satisfied by the empty classification
and says nothing.

## 3. The repaired vehicle

The ledger has room for the missing factor: the per-cell budget of
`BKLO.excLedgerSpread_of_routedSweepInvCellCount` is `4 (t + 1) + 4 (5 K² t + 1) + K² t ≤ 25 K² t`,
and tripling the foreign term keeps it inside `25 K² t` at `K ≥ 2`, `t ≥ 512`.  So the counted
invariant is re-run here against a foreign plan of capacity `3 K² t`:

* `BKLO.ForeignSpreadLeftoverPlanWide`, `BKLO.excLoad_le_of_routedSweepInvCellCountWide`,
  `BKLO.excLedgerSpread_of_routedSweepInvCellCountWide` — the ledger still pays;
* `BKLO.RoutedSweepInvCellCountWide6hStep` — the one-link step of the counted invariant against a
  wide foreign plan, at the reservoir re-sized to `6 h ≤ t` (`BKLO/AX2ResizedSixH.lean`), which is
  what the *pool width* of the merge needs: the partner of a forced leftover must be available in
  every routing index the count leaves free, i.e. in a constant fraction of the `h` classes of the
  region, and a plan that wide is inside the ledger only when the classes are wide, `q ≥ 4 h`;
* `BKLO.twoSidedUsedClassMatchedResized6hPairing_of_cell_step_countWide`,
  `BKLO.triangle_decomposition_of_inputs_and_cell_step_countWide` — and the chain to the AX2 half
  of the main theorem is intact.

Everything here is `sorry`-free.  The one-link step itself — `BKLO.RoutedSweepInvCellCountStep`
and its repaired form `BKLO.RoutedSweepInvCellCountWide6hStep` — is *not* proved here.
-/
import BKLO.AX2RoutedResidualCellCount
import BKLO.AX2ResizedSixH

open Finset

namespace BKLO

variable {V : Type} [DecidableEq V]
variable {ε : ℝ} {K : ℕ} {W W' W'' : Finset V} {F R : Finset (Sym2 V)} {C : ℕ → Finset V}
  {x y : V → ℕ} {L M : V → Finset V}

/-! ### A foreign plan of three times the capacity -/

/-- **The wide foreign plan**: `BKLO.ForeignSpreadLeftoverPlan` with its ceiling tripled.  This is
the capacity a merge needs, one foreign slot per unit of perturbation
(`BKLO.foreign_demand_exceeds_capacity`), and it is still inside the ledger. -/
def ForeignSpreadLeftoverPlanWide (ε : ℝ) (K : ℕ) (W W' : Finset V) (M : V → Finset V) : Prop :=
  ∀ a : V, (((W \ W').filter (fun w => a ∈ M w)).card) ≤ 3 * (K * K) * gridClassSize ε K W'.card

/-- A foreign plan is a wide foreign plan. -/
theorem foreignSpreadLeftoverPlanWide_of_foreign (hM : ForeignSpreadLeftoverPlan ε K W W' M) :
    ForeignSpreadLeftoverPlanWide ε K W W' M := by
  intro a
  exact le_trans (hM a) (Nat.mul_le_mul_right _ (by nlinarith only [Nat.zero_le (K * K)]))

/-! ### The counted invariant still pays the ledger against a wide foreign plan -/

/-- **The per-cell load of the counted invariant against a wide foreign plan.**  The load of
`BKLO.excLoad_le_of_routedSweepInvCellCount` with the foreign term tripled. -/
theorem excLoad_le_of_routedSweepInvCellCountWide
    (hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y)
    {φ : V → ℕ} (hφlt : ∀ w, φ w < gridSize ε K)
    (hbal : ∀ p q j : ℕ, (((W \ W').filter (fun w => x w = p ∧ y w = q ∧ φ w = j)).card)
      ≤ (((W \ W').filter (fun w => x w = p ∧ y w = q)).card) / gridSize ε K + 1)
    (hL : CellSpreadLeftoverPlan ε K W W' x y L) (hM : ForeignSpreadLeftoverPlanWide ε K W W' M)
    {S : Finset V} {g : V → V → V} {Exc : V → Finset V}
    (hInv : RoutedSweepInvCellCount ε K W W' C x y φ L M S g Exc)
    (a : V) {P Q : ℕ} (hP : P < gridSize ε K) (hQ : Q < gridSize ε K) :
    excLoad (gridSize ε K) C g S Exc a P Q
      ≤ 4 * ((20 * (K * K) * gridClassSize ε K W'.card + 1) / gridSize ε K + 1)
        + 4 * (5 * (K * K) * gridClassSize ε K W'.card + 1)
        + 3 * (K * K) * gridClassSize ε K W'.card := by
  classical
  obtain ⟨hSD, Cc, Cr, Pc, Pr, Fo, Po, rt, hsplit, hdisjC, hcyc, hrtlt, hroute, hPcL, hPrL,
    hPcRow, hPrCol, hcntC, hcntR, hFoM, hPo⟩ := hInv
  set h : ℕ := gridSize ε K with hhdef
  set t : ℕ := gridClassSize ε K W'.card with htdef
  -- the three parts the load splits into
  set A1 : Finset V := S.filter (fun w => a ∈ (Cc w ∪ Cr w) ∧ g w a ∈ gridRegion h C P Q) with hA1
  set A2 : Finset V := S.filter (fun w => a ∈ (Pc w ∪ Pr w) ∧ g w a ∈ gridRegion h C P Q) with hA2
  set A3 : Finset V := S.filter (fun w => a ∈ Fo w) with hA3
  have hsub : S.filter (fun w => a ∈ Exc w ∧ g w a ∈ gridRegion h C P Q) ⊆ (A1 ∪ A2) ∪ A3 := by
    intro w hw
    obtain ⟨hwS, hwE, hwreg⟩ := Finset.mem_filter.1 hw
    rcases Finset.mem_union.1 (hsplit w hwS hwE) with hcase | hcase
    · rcases Finset.mem_union.1 hcase with hc | hc
      · exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_filter.2 ⟨hwS, hc, hwreg⟩))
      · exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_filter.2 ⟨hwS, hc, hwreg⟩))
    · rcases Finset.mem_union.1 hcase with hc | hc
      · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hwS, hc⟩)
      · rw [gridRegion_eq_biUnion] at hwreg
        obtain ⟨k, hk, hmem⟩ := Finset.mem_biUnion.1 hwreg
        exact absurd hmem (hPo w hwS a hc k (gridIdx_lt hP hQ hk))
  have hcard : excLoad h C g S Exc a P Q ≤ A1.card + A2.card + A3.card := by
    calc excLoad h C g S Exc a P Q ≤ ((A1 ∪ A2) ∪ A3).card := Finset.card_le_card hsub
      _ ≤ (A1 ∪ A2).card + A3.card := Finset.card_union_le _ _
      _ ≤ A1.card + A2.card + A3.card :=
          Nat.add_le_add_right (Finset.card_union_le _ _) _
  -- the cycle part
  have hcyc1 : A1.card ≤ 4 * ((20 * (K * K) * t + 1) / h + 1) :=
    excLoad_le_of_cycleRouted (W'' := W'') (F := F) (R := R) hgrid hφlt hbal hSD
      hdisjC (Exc := fun w => Cc w ∪ Cr w) (fun w _ => Finset.Subset.refl _) hcyc a hP hQ
  -- the cross-routed part
  have hper : A2.card
      ≤ excRouteCount S Pc a (fun w => rt w a) P + excRouteCount S Pc a y Q
        + excRouteCount S Pr a x P + excRouteCount S Pr a (fun w => rt w a) Q :=
    excLoad_le_routed (C := C) (x := x) (y := y) (rt := rt) (S := S) (g := g)
      (Exc := fun w => Pc w ∪ Pr w) (Ecol := Pc) (Erow := Pr) (a := a) (P := P) (Q := Q)
      (fun i hi j hj hij => hgrid.classDisjoint i hi j hj hij)
      (fun w hw => hgrid.rowLt w (hSD hw)) (fun w hw => hgrid.colLt w (hSD hw))
      (fun w hw => hrtlt w hw a) hP hQ (fun w _ => Finset.Subset.refl _) hroute
  have hb1 : excRouteCount S Pc a (fun w => rt w a) P ≤ 5 * (K * K) * t + 1 := hcntC a P
  have hb2 : excRouteCount S Pc a y Q ≤ 5 * (K * K) * t + 1 :=
    excRouteCount_le_of_cellPlan_col (W'' := W'') (F := F) (R := R) hgrid hSD hL hPcL hPcRow a
      y (fun w _ w' _ _ _ hpf => hpf) Q
  have hb3 : excRouteCount S Pr a x P ≤ 5 * (K * K) * t + 1 :=
    excRouteCount_le_of_cellPlan_row (W'' := W'') (F := F) (R := R) hgrid hSD hL hPrL hPrCol a
      x (fun w _ w' _ _ _ hpf => hpf) P
  have hb4 : excRouteCount S Pr a (fun w => rt w a) Q ≤ 5 * (K * K) * t + 1 := hcntR a Q
  -- the foreign part
  have hfor : A3.card ≤ 3 * (K * K) * t := by
    refine le_trans (Finset.card_le_card ?_) (hM a)
    intro w hw
    obtain ⟨hwS, hwa⟩ := Finset.mem_filter.1 hw
    exact Finset.mem_filter.2 ⟨hSD hwS, hFoM w hwS hwa⟩
  omega


/-- **The counted invariant keeps the leftover ledger spread against a wide foreign plan**:
`4 (t + 1) + 4 (5 K² t + 1) + 3 K² t ≤ 25 K² t` at `2 ≤ K`, `512 ≤ t`. -/
theorem excLedgerSpread_of_routedSweepInvCellCountWide
    (hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y)
    (hε : 0 < ε) (hε' : ε ≤ 1 / 100) (hK : 2 ≤ K)
    (ht : 512 ≤ gridClassSize ε K W'.card)
    {φ : V → ℕ} (hφlt : ∀ w, φ w < gridSize ε K)
    (hbal : ∀ p q j : ℕ, (((W \ W').filter (fun w => x w = p ∧ y w = q ∧ φ w = j)).card)
      ≤ (((W \ W').filter (fun w => x w = p ∧ y w = q)).card) / gridSize ε K + 1)
    (hL : CellSpreadLeftoverPlan ε K W W' x y L) (hM : ForeignSpreadLeftoverPlanWide ε K W W' M)
    {S : Finset V} {g : V → V → V} {Exc : V → Finset V}
    (hInv : RoutedSweepInvCellCount ε K W W' C x y φ L M S g Exc) :
    ExcLedgerSpread ε K W' C g S Exc := by
  classical
  refine excLedgerSpread_of_load_le (C := C) (W' := W') hε hε' ?_
  intro a P hP Q hQ
  have h1 := excLoad_le_of_routedSweepInvCellCountWide (W'' := W'') (F := F) (R := R) hgrid hφlt
    hbal hL hM hInv a hP hQ
  set t : ℕ := gridClassSize ε K W'.card with htdef
  have h2 : (20 * (K * K) * t + 1) / gridSize ε K + 1 ≤ t + 1 :=
    cell_shift_fibre_le_succ_class (W' := W') hε hε' hK ht
  have h3 : 4 * ((20 * (K * K) * t + 1) / gridSize ε K + 1) ≤ 4 * (t + 1) :=
    Nat.mul_le_mul_left 4 h2
  have hKK : 4 ≤ K * K := Nat.mul_le_mul hK hK
  have e1 : 25 * (K * K) * t = 25 * ((K * K) * t) := by ring
  have e2 : 5 * (K * K) * t = 5 * ((K * K) * t) := by ring
  have e3 : 3 * (K * K) * t = 3 * ((K * K) * t) := by ring
  have h4 : 4 * t ≤ (K * K) * t := Nat.mul_le_mul_right _ hKK
  have h5 : 512 * 4 ≤ (K * K) * t := by
    calc 512 * 4 = 4 * 512 := by ring
      _ ≤ 4 * t := Nat.mul_le_mul_left 4 ht
      _ ≤ (K * K) * t := h4
  omega

/-! ### The repaired one-link step, and the chain to the main theorem -/

/-- **The one-link routed step of the counted invariant against a cell-balanced plan and a *wide*
foreign plan, at the reservoir re-sized to `6 h ≤ t`.**  This is
`BKLO.RoutedSweepInvCellCountStep` with the two changes the audit of this file calls for: the
foreign plan has the capacity `3 K² t` a merge actually needs
(`BKLO.foreign_demand_exceeds_capacity`), and the design is re-sized so that a class is wide
enough, `q ≥ 4 h`, to hold the partner pool the free routing index has to be chosen from. -/
def RoutedSweepInvCellCountWide6hStep : Prop :=
  ∀ {V : Type} [DecidableEq V] {ε : ℝ} {K : ℕ} {W W' W'' : Finset V}
    {F R : Finset (Sym2 V)} {C : ℕ → Finset V} {x y : V → ℕ} {q c : ℕ},
    IsGridTwoSidedReservoirEighth ε K W W' W'' F R C x y →
    (∀ e ∈ F, ¬ e.IsDiag) → W' ⊆ W →
    (∀ i < gridSize ε K * gridSize ε K, (C i).card = q) →
    (∀ v ∈ W \ W', ∀ i ∈ gridIdx (gridSize ε K) (x v) (y v),
      (resLink R W' v ∩ C i).card = c) →
    7 * q ≤ 8 * c →
    0 < ε → ε ≤ 1 / 100 → 2 ≤ K → 6 * gridSize ε K ≤ gridClassSize ε K W'.card →
    ∀ {φ : V → ℕ}, (∀ w, φ w < gridSize ε K) →
    (∀ p q j : ℕ, (((W \ W').filter (fun w => x w = p ∧ y w = q ∧ φ w = j)).card)
      ≤ (((W \ W').filter (fun w => x w = p ∧ y w = q)).card) / gridSize ε K + 1) →
    ∀ {X : V → Finset V},
    ∃ L M : V → Finset V, CellSpreadLeftoverPlan ε K W W' x y L ∧
      ForeignSpreadLeftoverPlanWide ε K W W' M ∧
      ∀ {S : Finset V} {g₀ : V → V → V} {Exc : V → Finset V} {u : V} {n m : ℕ}
        {U : Finset (Sym2 V)},
      u ∈ W \ W' → X u ⊆ W' → Even (X u).card →
      32 * (X u \ resLink R W' u).card ≤ gridClassSize ε K W'.card →
      32 * (resLink R W' u \ X u).card ≤ gridClassSize ε K W'.card →
      (X u \ resLink R W' u).card ≤ n → (resLink R W' u \ X u).card ≤ n →
      (∀ a ∈ X u, (resLink U (X u) a).card ≤ m) →
      UsedForbidden X g₀ S W'' U →
      12 * n + 8 * m ≤ (2 * gridSize ε K - 1) * c →
      S ⊆ W \ W' → u ∉ S →
      (∀ w ∈ S, ∀ b ∈ X w, g₀ w b ∈ X w) → (∀ w ∈ S, ∀ b ∈ X w, g₀ w (g₀ w b) = b) →
      IsClassMatchedSweep (gridSize ε K) C R W' X x y
        (fun w β => crossShift (gridSize ε K) φ β w)
        (fun w α => crossShiftInv (gridSize ε K) φ α w) S g₀ Exc →
      RoutedSweepInvCellCount ε K W W' C x y φ L M S g₀ Exc →
      ∃ (p : V → V) (e : Finset V),
        (∀ a ∈ X u, p a ∈ X u) ∧ (∀ a ∈ X u, p (p a) = a) ∧ (∀ a ∈ X u, p a ≠ a) ∧
        (∀ a ∈ X u, s(a, p a) ∈ F ∧ s(a, p a) ∉ U) ∧
        IsClassMatchedSweep (gridSize ε K) C R W' X x y
          (fun w β => crossShift (gridSize ε K) φ β w)
          (fun w α => crossShiftInv (gridSize ε K) φ α w)
          (insert u S) (Function.update g₀ u p) (Function.update Exc u e) ∧
        RoutedSweepInvCellCount ε K W W' C x y φ L M (insert u S) (Function.update g₀ u p)
          (Function.update Exc u e)

/-- **The re-sized `6 h ≤ t` residual demand of AX2 §10, from the repaired one-link step.** -/
theorem twoSidedUsedClassMatchedResized6hPairing_of_cell_step_countWide
    (hstep : RoutedSweepInvCellCountWide6hStep) : TwoSidedUsedClassMatchedResized6hPairing := by
  intro V _ ε K W W' W'' F R C x y q c X hgrid8 hnd hW'W hq hcres hqc8 hε hε' hK hbig
  classical
  set hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y :=
    hgrid8.toIsGridTwoSidedReservoir with hgriddef
  have hwide : 6400 * (K * K) ≤ gridSize ε K := gridSize_ge_of_eps_small hε hε' K
  have hKK : 4 ≤ K * K := Nat.mul_le_mul hK hK
  have ht512 : 512 ≤ gridClassSize ε K W'.card := by
    have h1 : 6400 * 4 ≤ 6400 * (K * K) := Nat.mul_le_mul_left _ hKK
    omega
  obtain ⟨φ, hφlt, hφcell⟩ :=
    exists_cell_balanced_shift (W \ W') x y (gridSize_pos ε K)
  obtain ⟨L, M, hL, hM, hstep'⟩ :=
    hstep hgrid8 hnd hW'W hq hcres hqc8 hε hε' hK hbig hφlt hφcell (X := X)
  refine ⟨fun w β => crossShift (gridSize ε K) φ β w,
    fun w α => crossShiftInv (gridSize ε K) φ α w,
    RoutedSweepInvCellCount ε K W W' C x y φ L M,
    fun w β => crossShift_lt (gridSize_pos ε K) φ β w,
    fun w α => crossShiftInv_lt (gridSize_pos ε K) φ α w,
    classMatchingFibres_of_cellBalanced hgrid hφlt hφcell,
    routedSweepInvCellCount_empty φ L M, ?_, ?_⟩
  · intro S g Exc hInv
    exact excLedgerSpread_of_routedSweepInvCellCountWide (W'' := W'') (F := F) (R := R) hgrid hε
      hε' hK ht512 hφlt hφcell hL hM hInv
  · intro S g₀ Exc u n m U hu hXu hXeven hadd32 hdel32 hadd hdel hUdeg hUused hmargin hSD huS
      hmaps hginv hsweep hInv
    exact hstep' hu hXu hXeven hadd32 hdel32 hadd hdel hUdeg hUused hmargin hSD huS hmaps hginv
      hsweep hInv

/-- **Main theorem (AX2 half of Erdős #81), from the three classical inputs and the repaired
one-link counted step.** -/
theorem triangle_decomposition_of_inputs_and_cell_step_countWide
    (hDross : FracTriangleThreshold) (hNib : FracToApproxMaxDeg) (hDirac : PerfectMatchingDirac)
    (hstep : RoutedSweepInvCellCountWide6hStep) :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        n₀ ≤ Fintype.card V →
        (3 ∣ G.edgeFinset.card ∧ ∀ v, Even (G.degree v)) →
        (9 / 10 + ε) * (Fintype.card V : ℝ) ≤ (G.minDegree : ℝ) →
        TriangleDecomposable G :=
  triangle_decomposition_of_inputs_and_twoSidedUsedClassMatchedResized6h hDross hNib hDirac
    (twoSidedUsedClassMatchedResized6hPairing_of_cell_step_countWide hstep)


/-! ### The index supply at the new link -/

/-- **A place planned at the new link is planned at fewer than `(5 K² t + 1) h` links of the
history of its grid row.**  The cell balance of `BKLO.CellSpreadLeftoverPlan` gives `5 K² t + 1`
planned links per cell, the grid row of `u` has `h` cells, and the cell of `u` itself already
spends one of its tickets on `u`, which is not in the history. -/
theorem planned_row_line_card_lt
    (hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y)
    (hL : CellSpreadLeftoverPlan ε K W W' x y L)
    {S : Finset V} (hSD : S ⊆ W \ W') {u : V} (hu : u ∈ W \ W') (huS : u ∉ S)
    {a : V} (hau : a ∈ L u) :
    (S.filter (fun w => x w = x u ∧ a ∈ L w)).card
      < (5 * (K * K) * gridClassSize ε K W'.card + 1) * gridSize ε K := by
  classical
  set h : ℕ := gridSize ε K with hhdef
  set t : ℕ := gridClassSize ε K W'.card with htdef
  set B : ℕ := 5 * (K * K) * t with hBdef
  set f : ℕ → ℕ := fun j => (S.filter (fun w => x w = x u ∧ y w = j ∧ a ∈ L w)).card with hfdef
  have hyu : y u < h := hgrid.colLt u hu
  -- every cell of the grid row carries at most `B + 1` planned links
  have hcell : ∀ j : ℕ, f j ≤ B + 1 := by
    intro j
    refine le_trans (Finset.card_le_card ?_) (hL a (x u) j)
    intro w hw
    obtain ⟨hwS, hwx, hwy, hwa⟩ := Finset.mem_filter.1 hw
    exact Finset.mem_filter.2 ⟨hSD hwS, hwx, hwy, hwa⟩
  -- the cell of `u` carries at most `B`, since `u` itself is planned there and is not in `S`
  have hcellu : f (y u) ≤ B := by
    have hins : insert u (S.filter (fun w => x w = x u ∧ y w = y u ∧ a ∈ L w))
        ⊆ (W \ W').filter (fun w => x w = x u ∧ y w = y u ∧ a ∈ L w) := by
      intro w hw
      rcases Finset.mem_insert.1 hw with rfl | hw
      · exact Finset.mem_filter.2 ⟨hu, rfl, rfl, hau⟩
      · obtain ⟨hwS, hwx, hwy, hwa⟩ := Finset.mem_filter.1 hw
        exact Finset.mem_filter.2 ⟨hSD hwS, hwx, hwy, hwa⟩
    have hnot : u ∉ S.filter (fun w => x w = x u ∧ y w = y u ∧ a ∈ L w) := fun hcon =>
      huS (Finset.mem_filter.1 hcon).1
    have h1 : f (y u) + 1 ≤ B + 1 := by
      have := le_trans (Finset.card_le_card hins) (hL a (x u) (y u))
      rwa [Finset.card_insert_of_notMem hnot] at this
    omega
  -- the planned links of the grid row split over its `h` cells
  have hsub : S.filter (fun w => x w = x u ∧ a ∈ L w)
      ⊆ (Finset.range h).biUnion (fun j => S.filter (fun w => x w = x u ∧ y w = j ∧ a ∈ L w)) := by
    intro w hw
    obtain ⟨hwS, hwx, hwa⟩ := Finset.mem_filter.1 hw
    exact Finset.mem_biUnion.2 ⟨y w, Finset.mem_range.2 (hgrid.colLt w (hSD hwS)),
      Finset.mem_filter.2 ⟨hwS, hwx, rfl, hwa⟩⟩
  have hcard : (S.filter (fun w => x w = x u ∧ a ∈ L w)).card ≤ ∑ j ∈ Finset.range h, f j :=
    le_trans (Finset.card_le_card hsub) (Finset.card_biUnion_le)
  -- and the sum over the cells is below `(B + 1) h`
  have hsum : ∑ j ∈ Finset.range h, f j ≤ B + (h - 1) * (B + 1) := by
    have hkey : ∑ j ∈ (Finset.range h).erase (y u), f j + f (y u) = ∑ j ∈ Finset.range h, f j :=
      Finset.sum_erase_add _ _ (Finset.mem_range.2 hyu)
    have h2 : ∑ j ∈ (Finset.range h).erase (y u), f j
        ≤ ((Finset.range h).erase (y u)).card • (B + 1) :=
      Finset.sum_le_card_nsmul _ _ _ (fun j _ => hcell j)
    simp only [smul_eq_mul] at h2
    rw [Finset.card_erase_of_mem (Finset.mem_range.2 hyu), Finset.card_range] at h2
    omega
  have hhpos : 0 < h := gridSize_pos ε K
  have hfin : B + (h - 1) * (B + 1) < (B + 1) * h := by
    have : (h - 1) * (B + 1) + (B + 1) = (B + 1) * h := by
      have : h - 1 + 1 = h := by omega
      calc (h - 1) * (B + 1) + (B + 1) = (h - 1 + 1) * (B + 1) := by ring
        _ = h * (B + 1) := by rw [this]
        _ = (B + 1) * h := by ring
    omega
  omega

/-- **A place planned at the new link is planned at fewer than `(5 K² t + 1) h` links of the
history of its grid column.**  The column analogue of `BKLO.planned_row_line_card_lt`. -/
theorem planned_col_line_card_lt
    (hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y)
    (hL : CellSpreadLeftoverPlan ε K W W' x y L)
    {S : Finset V} (hSD : S ⊆ W \ W') {u : V} (hu : u ∈ W \ W') (huS : u ∉ S)
    {a : V} (hau : a ∈ L u) :
    (S.filter (fun w => y w = y u ∧ a ∈ L w)).card
      < (5 * (K * K) * gridClassSize ε K W'.card + 1) * gridSize ε K := by
  classical
  set h : ℕ := gridSize ε K with hhdef
  set t : ℕ := gridClassSize ε K W'.card with htdef
  set B : ℕ := 5 * (K * K) * t with hBdef
  set f : ℕ → ℕ := fun i => (S.filter (fun w => x w = i ∧ y w = y u ∧ a ∈ L w)).card with hfdef
  have hxu : x u < h := hgrid.rowLt u hu
  have hcell : ∀ i : ℕ, f i ≤ B + 1 := by
    intro i
    refine le_trans (Finset.card_le_card ?_) (hL a i (y u))
    intro w hw
    obtain ⟨hwS, hwx, hwy, hwa⟩ := Finset.mem_filter.1 hw
    exact Finset.mem_filter.2 ⟨hSD hwS, hwx, hwy, hwa⟩
  have hcellu : f (x u) ≤ B := by
    have hins : insert u (S.filter (fun w => x w = x u ∧ y w = y u ∧ a ∈ L w))
        ⊆ (W \ W').filter (fun w => x w = x u ∧ y w = y u ∧ a ∈ L w) := by
      intro w hw
      rcases Finset.mem_insert.1 hw with rfl | hw
      · exact Finset.mem_filter.2 ⟨hu, rfl, rfl, hau⟩
      · obtain ⟨hwS, hwx, hwy, hwa⟩ := Finset.mem_filter.1 hw
        exact Finset.mem_filter.2 ⟨hSD hwS, hwx, hwy, hwa⟩
    have hnot : u ∉ S.filter (fun w => x w = x u ∧ y w = y u ∧ a ∈ L w) := fun hcon =>
      huS (Finset.mem_filter.1 hcon).1
    have h1 : f (x u) + 1 ≤ B + 1 := by
      have := le_trans (Finset.card_le_card hins) (hL a (x u) (y u))
      rwa [Finset.card_insert_of_notMem hnot] at this
    omega
  have hsub : S.filter (fun w => y w = y u ∧ a ∈ L w)
      ⊆ (Finset.range h).biUnion (fun i => S.filter (fun w => x w = i ∧ y w = y u ∧ a ∈ L w)) := by
    intro w hw
    obtain ⟨hwS, hwy, hwa⟩ := Finset.mem_filter.1 hw
    exact Finset.mem_biUnion.2 ⟨x w, Finset.mem_range.2 (hgrid.rowLt w (hSD hwS)),
      Finset.mem_filter.2 ⟨hwS, rfl, hwy, hwa⟩⟩
  have hcard : (S.filter (fun w => y w = y u ∧ a ∈ L w)).card ≤ ∑ i ∈ Finset.range h, f i :=
    le_trans (Finset.card_le_card hsub) (Finset.card_biUnion_le)
  have hsum : ∑ i ∈ Finset.range h, f i ≤ B + (h - 1) * (B + 1) := by
    have hkey : ∑ i ∈ (Finset.range h).erase (x u), f i + f (x u) = ∑ i ∈ Finset.range h, f i :=
      Finset.sum_erase_add _ _ (Finset.mem_range.2 hxu)
    have h2 : ∑ i ∈ (Finset.range h).erase (x u), f i
        ≤ ((Finset.range h).erase (x u)).card • (B + 1) :=
      Finset.sum_le_card_nsmul _ _ _ (fun i _ => hcell i)
    simp only [smul_eq_mul] at h2
    rw [Finset.card_erase_of_mem (Finset.mem_range.2 hxu), Finset.card_range] at h2
    omega
  have hhpos : 0 < h := gridSize_pos ε K
  have hfin : B + (h - 1) * (B + 1) < (B + 1) * h := by
    have : (h - 1) * (B + 1) + (B + 1) = (B + 1) * h := by
      have hh1 : h - 1 + 1 = h := by omega
      calc (h - 1) * (B + 1) + (B + 1) = (h - 1 + 1) * (B + 1) := by ring
        _ = h * (B + 1) := by rw [hh1]
        _ = (B + 1) * h := by ring
    omega
  omega

/-- **A column-routed leftover of the history lies in the grid row of its own link.**  The clause
`a ∈ Pc w → ∃ β < h, a ∈ C (x w · h + β)` of `BKLO.RoutedSweepInvCellCount` and the disjointness of
the classes pin the grid row of `w` to the row digit of the class of `a`. -/
theorem row_of_crossRouted_col
    (hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y)
    {S : Finset V} (hSD : S ⊆ W \ W') {Pc : V → Finset V}
    (hPcRow : ∀ w ∈ S, ∀ b ∈ Pc w, ∃ β < gridSize ε K, b ∈ C (x w * gridSize ε K + β))
    {a : V} {α : ℕ} (hα : α < gridSize ε K) {β₀ : ℕ} (hβ₀ : β₀ < gridSize ε K)
    (haC : a ∈ C (α * gridSize ε K + β₀)) {w : V} (hw : w ∈ S) (haw : a ∈ Pc w) :
    x w = α := by
  classical
  set h : ℕ := gridSize ε K with hhdef
  obtain ⟨β, hβ, haβ⟩ := hPcRow w hw a haw
  have hxw : x w < h := hgrid.rowLt w (hSD hw)
  by_cases hij : x w * h + β = α * h + β₀
  · exact (gridDigits_inj hβ hβ₀ hij).1
  · exact absurd haC (Finset.disjoint_left.1
      (hgrid.classDisjoint _ (gridIdx_lt hxw hβ (mem_gridIdx.2 (Or.inl ⟨β, hβ, rfl⟩)))
        _ (gridIdx_lt hα hβ₀ (mem_gridIdx.2 (Or.inl ⟨β₀, hβ₀, rfl⟩))) hij) haβ)

/-- **A row-routed leftover of the history lies in the grid column of its own link.** -/
theorem col_of_crossRouted_row
    (hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y)
    {S : Finset V} (hSD : S ⊆ W \ W') {Pr : V → Finset V}
    (hPrCol : ∀ w ∈ S, ∀ b ∈ Pr w, ∃ α < gridSize ε K, b ∈ C (α * gridSize ε K + y w))
    {a : V} {α₀ : ℕ} (hα₀ : α₀ < gridSize ε K) {β : ℕ} (hβ : β < gridSize ε K)
    (haC : a ∈ C (α₀ * gridSize ε K + β)) {w : V} (hw : w ∈ S) (haw : a ∈ Pr w) :
    y w = β := by
  classical
  set h : ℕ := gridSize ε K with hhdef
  obtain ⟨α, hα, haα⟩ := hPrCol w hw a haw
  have hyw : y w < h := hgrid.colLt w (hSD hw)
  by_cases hij : α * h + y w = α₀ * h + β
  · exact (gridDigits_inj hyw hβ hij).2
  · exact absurd haC (Finset.disjoint_left.1
      (hgrid.classDisjoint _ (gridIdx_lt hα hyw (mem_gridIdx.2 (Or.inl ⟨y w, hyw, rfl⟩)))
        _ (gridIdx_lt hα₀ hβ (mem_gridIdx.2 (Or.inl ⟨β, hβ, rfl⟩))) hij) haα)

/-- **A routing index with room is available at every place the plan offers the new link, on the
column-routed side.**  This is `BKLO.exists_free_routing_index` discharged from the design and the
plan alone: the history claims the place `a` at fewer than `(5 K² t + 1) h` links
(`BKLO.planned_row_line_card_lt`), so one of the `h` indices carries at most `5 K² t` of them and
the new link may use it without breaking the counted clause. -/
theorem exists_free_routing_index_at_link_col
    (hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y)
    (hL : CellSpreadLeftoverPlan ε K W W' x y L)
    {S : Finset V} (hSD : S ⊆ W \ W') {Pc : V → Finset V} {rt : V → V → ℕ}
    (hPcL : ∀ w ∈ S, Pc w ⊆ L w)
    (hPcRow : ∀ w ∈ S, ∀ b ∈ Pc w, ∃ β < gridSize ε K, b ∈ C (x w * gridSize ε K + β))
    (hrtlt : ∀ w ∈ S, ∀ b : V, rt w b < gridSize ε K)
    {u : V} (hu : u ∈ W \ W') (huS : u ∉ S)
    {a : V} (hau : a ∈ L u) {γ : ℕ} (hγ : γ < gridSize ε K)
    (haC : a ∈ C (x u * gridSize ε K + γ)) :
    ∃ P < gridSize ε K, excRouteCount S Pc a (fun w => rt w a) P
      ≤ 5 * (K * K) * gridClassSize ε K W'.card := by
  classical
  refine exists_free_routing_index (h := gridSize ε K)
    (B := 5 * (K * K) * gridClassSize ε K W'.card) a (fun w hw => hrtlt w hw a) ?_
  refine lt_of_le_of_lt (Finset.card_le_card ?_)
    (planned_row_line_card_lt (W'' := W'') (F := F) (R := R) hgrid hL hSD hu huS hau)
  intro w hw
  obtain ⟨hwS, hwa⟩ := Finset.mem_filter.1 hw
  exact Finset.mem_filter.2 ⟨hwS,
    row_of_crossRouted_col (W'' := W'') (F := F) (R := R) hgrid hSD hPcRow
      (hgrid.rowLt u hu) hγ haC hwS hwa, hPcL w hwS hwa⟩

/-- **A routing index with room is available at every place the plan offers the new link, on the
row-routed side.**  The column analogue of `BKLO.exists_free_routing_index_at_link_col`. -/
theorem exists_free_routing_index_at_link_row
    (hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y)
    (hL : CellSpreadLeftoverPlan ε K W W' x y L)
    {S : Finset V} (hSD : S ⊆ W \ W') {Pr : V → Finset V} {rt : V → V → ℕ}
    (hPrL : ∀ w ∈ S, Pr w ⊆ L w)
    (hPrCol : ∀ w ∈ S, ∀ b ∈ Pr w, ∃ α < gridSize ε K, b ∈ C (α * gridSize ε K + y w))
    (hrtlt : ∀ w ∈ S, ∀ b : V, rt w b < gridSize ε K)
    {u : V} (hu : u ∈ W \ W') (huS : u ∉ S)
    {a : V} (hau : a ∈ L u) {α : ℕ} (hα : α < gridSize ε K)
    (haC : a ∈ C (α * gridSize ε K + y u)) :
    ∃ Q < gridSize ε K, excRouteCount S Pr a (fun w => rt w a) Q
      ≤ 5 * (K * K) * gridClassSize ε K W'.card := by
  classical
  refine exists_free_routing_index (h := gridSize ε K)
    (B := 5 * (K * K) * gridClassSize ε K W'.card) a (fun w hw => hrtlt w hw a) ?_
  refine lt_of_le_of_lt (Finset.card_le_card ?_)
    (planned_col_line_card_lt (W'' := W'') (F := F) (R := R) hgrid hL hSD hu huS hau)
  intro w hw
  obtain ⟨hwS, hwa⟩ := Finset.mem_filter.1 hw
  exact Finset.mem_filter.2 ⟨hwS,
    col_of_crossRouted_row (W'' := W'') (F := F) (R := R) hgrid hSD hPrCol hα
      (hgrid.colLt u hu) haC hwS hwa, hPrL w hwS hwa⟩

/-! ### The classification a counted sweep is carried by

The witnesses `Cc, Cr, Pc, Pr, Fo, Po, rt` of `BKLO.RoutedSweepInvCellCount` are existentially
bound, so a statement that re-existentialises them says nothing: `Pc := Pr := fun _ => ∅` and any
`rt` satisfy the cross-routing clauses and both fibre counts vacuously.  Everything below is
therefore stated for a **fixed** classification, and `BKLO.isCountClassification_of_inv` /
`BKLO.routedSweepInvCellCount_of_classification` move between the two forms. -/

/-- The body of `BKLO.RoutedSweepInvCellCount` with its witnesses named: the classification of the
leftovers of a swept link into cycle, cross-routed, foreign and off-class parts, together with the
routing index `rt`. -/
def IsCountClassification (ε : ℝ) (K : ℕ) (W' : Finset V) (C : ℕ → Finset V) (x y φ : V → ℕ)
    (L M : V → Finset V) (S : Finset V) (g : V → V → V) (Exc : V → Finset V)
    (Cc Cr Pc Pr Fo Po : V → Finset V) (rt : V → V → ℕ) : Prop :=
  (∀ w ∈ S, Exc w ⊆ ((Cc w ∪ Cr w) ∪ (Pc w ∪ Pr w)) ∪ (Fo w ∪ Po w)) ∧
  (∀ w ∈ S, ∀ a ∈ Cr w, a ∉ Cc w) ∧
  IsCycleRoutedLeftover (gridSize ε K) C x y φ S g Cc Cr ∧
  (∀ w ∈ S, ∀ b : V, rt w b < gridSize ε K) ∧
  IsCrossRoutedLeftover (gridSize ε K) C x y rt S g Pc Pr ∧
  (∀ w ∈ S, Pc w ⊆ L w) ∧ (∀ w ∈ S, Pr w ⊆ L w) ∧
  (∀ w ∈ S, ∀ a ∈ Pc w, ∃ β < gridSize ε K, a ∈ C (x w * gridSize ε K + β)) ∧
  (∀ w ∈ S, ∀ a ∈ Pr w, ∃ α < gridSize ε K, a ∈ C (α * gridSize ε K + y w)) ∧
  (∀ (a : V) (P : ℕ), excRouteCount S Pc a (fun w => rt w a) P
    ≤ 5 * (K * K) * gridClassSize ε K W'.card + 1) ∧
  (∀ (a : V) (Q : ℕ), excRouteCount S Pr a (fun w => rt w a) Q
    ≤ 5 * (K * K) * gridClassSize ε K W'.card + 1) ∧
  (∀ w ∈ S, Fo w ⊆ M w) ∧
  (∀ w ∈ S, ∀ a ∈ Po w, ∀ i < gridSize ε K * gridSize ε K, g w a ∉ C i)

/-- A counted sweep is a sweep carried by some classification. -/
theorem isCountClassification_of_inv {φ : V → ℕ} {S : Finset V} {g : V → V → V}
    {Exc : V → Finset V} (hInv : RoutedSweepInvCellCount ε K W W' C x y φ L M S g Exc) :
    S ⊆ W \ W' ∧ ∃ Cc Cr Pc Pr Fo Po rt,
      IsCountClassification ε K W' C x y φ L M S g Exc Cc Cr Pc Pr Fo Po rt := hInv

/-- Conversely, a classification witnesses the counted invariant. -/
theorem routedSweepInvCellCount_of_classification {φ : V → ℕ} {S : Finset V} {g : V → V → V}
    {Exc : V → Finset V} {Cc Cr Pc Pr Fo Po : V → Finset V} {rt : V → V → ℕ}
    (hSD : S ⊆ W \ W')
    (hcls : IsCountClassification ε K W' C x y φ L M S g Exc Cc Cr Pc Pr Fo Po rt) :
    RoutedSweepInvCellCount ε K W W' C x y φ L M S g Exc :=
  ⟨hSD, Cc, Cr, Pc, Pr, Fo, Po, rt, hcls⟩

/-- **The counted invariant never blocks the new link's routing index.**  At a sweep carried by a
classification and a link `u` outside it, every place the plan offers at `u` has, on each of the
two sides, a routing index whose fibre — *of that very classification* — still has room for one
more link, so `BKLO.excRouteCount_insert_le` keeps the two counted clauses at their cap
`5 K² t + 1`.  This is the exact statement that the wall of `BKLO.routed_index_collision` — an
index owned by the history — does not exist for the counted invariant. -/
theorem free_routing_index_available_of_countInv
    (hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y)
    (hL : CellSpreadLeftoverPlan ε K W W' x y L)
    {φ : V → ℕ} {S : Finset V} {g : V → V → V} {Exc : V → Finset V}
    {Cc Cr Pc Pr Fo Po : V → Finset V} {rt : V → V → ℕ} (hSD : S ⊆ W \ W')
    (hcls : IsCountClassification ε K W' C x y φ L M S g Exc Cc Cr Pc Pr Fo Po rt)
    {u : V} (hu : u ∈ W \ W') (huS : u ∉ S) :
      (∀ a ∈ L u, ∀ γ < gridSize ε K, a ∈ C (x u * gridSize ε K + γ) →
        ∃ P < gridSize ε K, excRouteCount S Pc a (fun w => rt w a) P
          ≤ 5 * (K * K) * gridClassSize ε K W'.card) ∧
      (∀ a ∈ L u, ∀ α < gridSize ε K, a ∈ C (α * gridSize ε K + y u) →
        ∃ Q < gridSize ε K, excRouteCount S Pr a (fun w => rt w a) Q
          ≤ 5 * (K * K) * gridClassSize ε K W'.card) := by
  classical
  obtain ⟨hsplit, hdisjC, hcyc, hrtlt, hroute, hPcL, hPrL, hPcRow, hPrCol, hcntC, hcntR, hFoM,
    hPo⟩ := hcls
  refine ⟨?_, ?_⟩
  · intro a hau γ hγ haC
    exact exists_free_routing_index_at_link_col (W'' := W'') (F := F) (R := R) hgrid hL hSD hPcL
      hPcRow hrtlt hu huS hau hγ haC
  · intro a hau α hα haC
    exact exists_free_routing_index_at_link_row (W'' := W'') (F := F) (R := R) hgrid hL hSD hPrL
      hPrCol hrtlt hu huS hau hα haC


/-! ### What the merge still has to pay: the partner of a forced leftover -/

/-- **The partner of a forced leftover is booked with a *forced* index, or in the foreign plan.**

Let `a` be a leftover of the link `u` lying in a row class `C (x u · h + γ)` of its region, whose
partner `z = g u a` lies in a column class `C (α · h + y u)`, with `α ≠ x u` (the partner is not in
the corner class) and `γ` not the sink index `crossShiftInv h φ (x u) u` (the leftover is not in the
sink row class of the three-class cycle).  Then, in *any* classification witnessing
`BKLO.RoutedSweepInvCellCount`, the partner `z` is either

* a **foreign** leftover, `z ∈ M u` — a slot of the globally spread plan; or
* a **row-routed** leftover whose routing index is *forced* to `γ`, the class digit of `a`, which
  the perturbation dictates and the prover does not choose.

This is what a merge has to pay for each leftover the perturbation forces: the free routing index
of `BKLO.exists_free_routing_index_at_link_col` covers the leftover itself, never its partner. -/
theorem count_partner_forced_or_foreign
    (hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y)
    {φ : V → ℕ}
    {S : Finset V} {g : V → V → V} {Exc : V → Finset V}
    {Cc Cr Pc Pr Fo Po : V → Finset V} {rt : V → V → ℕ} (hSD : S ⊆ W \ W')
    (hcls : IsCountClassification ε K W' C x y φ L M S g Exc Cc Cr Pc Pr Fo Po rt)
    {u : V} (hu : u ∈ S) {a z : V} {γ α : ℕ}
    (hγ : γ < gridSize ε K) (hα : α < gridSize ε K)
    (haC : a ∈ C (x u * gridSize ε K + γ)) (hzC : z ∈ C (α * gridSize ε K + y u))
    (hzExc : z ∈ Exc u) (hgz : g u z = a)
    (hαne : α ≠ x u) (hγne : γ ≠ crossShiftInv (gridSize ε K) φ (x u) u) :
    z ∈ M u ∨ (z ∈ Pr u ∧ rt u z = γ) := by
  classical
  obtain ⟨hsplit, hdisjC, hcyc, hrtlt, hroute, hPcL, hPrL, hPcRow, hPrCol, hcntC, hcntR, hFoM,
    hPo⟩ := hcls
  set h : ℕ := gridSize ε K with hhdef
  have hxu : x u < h := hgrid.rowLt u (hSD hu)
  have hyu : y u < h := hgrid.colLt u (hSD hu)
  have hσ : crossShiftInv h φ (x u) u < h := crossShiftInv_lt (gridSize_pos ε K) φ (x u) u
  have hA : crossShift h φ (y u) u < h := crossShift_lt (gridSize_pos ε K) φ (y u) u
  -- the class of `z` is a column class of the region, and it is not a row class of it
  have hzclass : ∀ (β : ℕ), β < h → z ∉ C (x u * h + β) := by
    intro β hβ hmem
    have hne : α * h + y u ≠ x u * h + β := by
      intro hcon
      exact hαne (gridDigits_inj hyu hβ hcon).1
    exact absurd hmem (Finset.disjoint_left.1
      (hgrid.classDisjoint _ (gridIdx_lt hα hyu (mem_gridIdx.2 (Or.inr ⟨α, hα, rfl⟩)))
        _ (gridIdx_lt hxu hβ (mem_gridIdx.2 (Or.inl ⟨β, hβ, rfl⟩))) hne) hzC)
  -- the partner `a` of `z` lies in the row class `γ`, not in the sink row class
  have haclass : ∀ (β : ℕ), β < h → β ≠ γ → a ∉ C (x u * h + β) := by
    intro β hβ hβγ hmem
    have hne : x u * h + β ≠ x u * h + γ := by
      intro hcon
      exact hβγ (gridDigits_inj hβ hγ hcon).2
    exact absurd haC (Finset.disjoint_left.1
      (hgrid.classDisjoint _ (gridIdx_lt hxu hβ (mem_gridIdx.2 (Or.inl ⟨β, hβ, rfl⟩)))
        _ (gridIdx_lt hxu hγ (mem_gridIdx.2 (Or.inl ⟨γ, hγ, rfl⟩))) hne) hmem)
  rcases Finset.mem_union.1 (hsplit u hu hzExc) with hcase | hcase
  · rcases Finset.mem_union.1 hcase with hc | hc
    · rcases Finset.mem_union.1 hc with hc' | hc'
      · -- `z` cannot be a cycle leftover of the sink row class: its class is a column class
        exact absurd ((hcyc u hu).1 z hc').1 (hzclass _ hσ)
      · -- `z` cannot be a cycle leftover of the orphan column class: its partner would be in the
        -- sink row class
        have hp := ((hcyc u hu).2 z hc').2
        rw [hgz] at hp
        exact absurd hp (haclass _ hσ (fun hcon => hγne hcon.symm))
    · rcases Finset.mem_union.1 hc with hc' | hc'
      · -- `z` is not column-routed: it would lie in a row class of the region
        obtain ⟨β, hβ, hmem⟩ := hPcRow u hu z hc'
        exact absurd hmem (hzclass β hβ)
      · -- `z` is row-routed, and its index is forced to `γ`
        refine Or.inr ⟨hc', ?_⟩
        have hpart := (hroute u hu).2 z hc'
        rw [hgz] at hpart
        by_contra hcon
        exact absurd hpart (haclass _ (hrtlt u hu z) hcon)
  · rcases Finset.mem_union.1 hcase with hc' | hc'
    · -- `z` is foreign
      exact Or.inl (hFoM u hu hc')
    · -- `z` is not off-class: its partner `a` lies in a class of the grid
      have hoff := hPo u hu z hc' (x u * h + γ)
        (gridIdx_lt hxu hγ (mem_gridIdx.2 (Or.inl ⟨γ, hγ, rfl⟩)))
      rw [hgz] at hoff
      exact absurd haC hoff

/-! ### The foreign demand of the merge, against the capacity of the foreign plan -/

/-- **Double counting a plan.**  If every link of `T` plans at least `D` places, all of them inside
a common pool `Ground`, and `cap * |Ground| < |T| * D`, then some place of the pool is planned at
more than `cap` links. -/
theorem exists_plan_load_gt {T Ground : Finset V} {M : V → Finset V} {D cap : ℕ}
    (hsub : ∀ w ∈ T, M w ⊆ Ground) (hD : ∀ w ∈ T, D ≤ (M w).card)
    (hcap : cap * Ground.card < T.card * D) :
    ∃ a ∈ Ground, cap < (T.filter (fun w => a ∈ M w)).card := by
  classical
  by_contra hcon
  push_neg at hcon
  have hsum : ∑ a ∈ Ground, (T.filter (fun w => a ∈ M w)).card
      = ∑ w ∈ T, (Ground.filter (fun a => a ∈ M w)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have hone : ∀ w ∈ T, (Ground.filter (fun a => a ∈ M w)).card = (M w).card := by
    intro w hw
    congr 1
    refine Finset.Subset.antisymm (fun b hb => (Finset.mem_filter.1 hb).2) (fun b hb => ?_)
    exact Finset.mem_filter.2 ⟨hsub w hw hb, hb⟩
  have hlow : T.card * D ≤ ∑ w ∈ T, (Ground.filter (fun a => a ∈ M w)).card := by
    calc T.card * D = ∑ _w ∈ T, D := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum (fun w hw => by rw [hone w hw]; exact hD w hw)
  have hhigh : ∑ a ∈ Ground, (T.filter (fun w => a ∈ M w)).card ≤ Ground.card * cap := by
    calc ∑ a ∈ Ground, (T.filter (fun w => a ∈ M w)).card ≤ ∑ _a ∈ Ground, cap :=
          Finset.sum_le_sum (fun a ha => hcon a ha)
      _ = Ground.card * cap := by rw [Finset.sum_const, smul_eq_mul]
  rw [hsum] at hhigh
  have : cap * Ground.card = Ground.card * cap := Nat.mul_comm _ _
  omega

/-- **The foreign plan is too narrow for the merge.**  At the design's own capacity — `2 h - 1`
cells meeting a class and `20 K² t + 1` links per cell — one foreign slot per unit of a
perturbation of size `t / 32` on each side, i.e. `D = t / 16` slots per link chosen from a pool of
`(2 h - 1) c` places, forces some place of the pool into `M` at more than `K² t` links: the ceiling
`BKLO.ForeignSpreadLeftoverPlan` imposes is exceeded.  (The ceiling `3 K² t` of
`BKLO.ForeignSpreadLeftoverPlanWide` is not: `K² t c < (20 K² t + 1) D ≤ 3 K² t c` at these
sizes.) -/
theorem foreign_demand_exceeds_capacity {T Ground : Finset V} {M : V → Finset V}
    {K t h c D : ℕ}
    (hsub : ∀ w ∈ T, M w ⊆ Ground) (hD : ∀ w ∈ T, D ≤ (M w).card)
    (hT : (2 * h - 1) * (20 * (K * K) * t + 1) ≤ T.card)
    (hZ : Ground.card ≤ (2 * h - 1) * c)
    (ht : t = 16 * D) (hc : 8 * c ≤ 7 * t + 8) (hK : 2 ≤ K) (hh : 2 ≤ h) (hD0 : 0 < D) :
    ∃ a ∈ Ground, K * K * t < (T.filter (fun w => a ∈ M w)).card := by
  classical
  refine exists_plan_load_gt hsub hD ?_
  have hKK : 4 ≤ K * K := Nat.mul_le_mul hK hK
  have hcell : K * K * t * c < (20 * (K * K) * t + 1) * D := by
    subst ht
    have hc' : c ≤ 14 * D + 1 := by omega
    have h1 : K * K * (16 * D) * c ≤ K * K * (16 * D) * (14 * D + 1) :=
      Nat.mul_le_mul_left _ hc'
    have e3 : (K * K) * D ≤ (K * K) * (D * D) :=
      Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left D hD0)
    have e4 : 0 < (K * K) * (D * D) := by positivity
    calc K * K * (16 * D) * c ≤ K * K * (16 * D) * (14 * D + 1) := h1
      _ = 224 * ((K * K) * (D * D)) + 16 * ((K * K) * D) := by ring
      _ ≤ 224 * ((K * K) * (D * D)) + 16 * ((K * K) * (D * D)) := by omega
      _ = 240 * ((K * K) * (D * D)) := by ring
      _ < 320 * ((K * K) * (D * D)) + D := by omega
      _ = (20 * (K * K) * (16 * D) + 1) * D := by ring
  have h1 : K * K * t * Ground.card ≤ K * K * t * ((2 * h - 1) * c) :=
    Nat.mul_le_mul_left _ hZ
  have h2 : (2 * h - 1) * (20 * (K * K) * t + 1) * D ≤ T.card * D := Nat.mul_le_mul_right _ hT
  have h3 : K * K * t * ((2 * h - 1) * c) < (2 * h - 1) * (20 * (K * K) * t + 1) * D := by
    have hpos : 0 < 2 * h - 1 := by omega
    calc K * K * t * ((2 * h - 1) * c) = (2 * h - 1) * (K * K * t * c) := by ring
      _ < (2 * h - 1) * ((20 * (K * K) * t + 1) * D) :=
          Nat.mul_lt_mul_of_pos_left hcell hpos
      _ = (2 * h - 1) * (20 * (K * K) * t + 1) * D := by ring
  omega

/-- **The numeric witness of the obstruction.**  At the smallest sizes the vehicle allows --
`K = 2`, `h = 25600` classes, `t = 512` places per class, a perturbation of `D = 32` forced
leftovers per link and a pool of `c = 448` places per class -- a merge that books one foreign slot
per unit of perturbation overloads some place of the pool at more than `K^2 t = 2048` links, which
`BKLO.ForeignSpreadLeftoverPlan` forbids. -/
theorem foreign_demand_exceeds_capacity_witness {T Ground : Finset V} {M : V → Finset V}
    (hsub : ∀ w ∈ T, M w ⊆ Ground) (hD : ∀ w ∈ T, 32 ≤ (M w).card)
    (hT : 51199 * 40961 ≤ T.card) (hZ : Ground.card ≤ 51199 * 448) :
    ∃ a ∈ Ground, 2048 < (T.filter (fun w => a ∈ M w)).card := by
  have h := foreign_demand_exceeds_capacity (K := 2) (t := 512) (h := 25600) (c := 448) (D := 32)
    hsub hD (by norm_num; exact hT) (by norm_num; exact hZ) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  norm_num at h
  exact h

/-- **A blocked forced index sends the whole perturbation into the foreign plan.**  Fix a sweep
satisfying the counted invariant and, at each link `w` of a family `T`, a set `Z w` of partners of
perturbed leftovers: `z ∈ Z w` lies in the column class `alp w z` of the region, its partner
`g w z` lies in the row class `gam w z`, and neither the corner class nor the sink class of the
three-class cycle is involved.  If none of them can be booked row-routed at its *forced* index
`gam w z` -- the hypothesis `hblock`, which an adversarial history is free to impose, since the
counted invariant bounds the fibres from above only -- then, by
`BKLO.count_partner_forced_or_foreign`, every one of them is a foreign slot: `Z w ⊆ M w`. -/
theorem blocked_partners_are_foreign
    (hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y)
    {φ : V → ℕ} {S : Finset V} {g : V → V → V} {Exc : V → Finset V}
    {Cc Cr Pc Pr Fo Po : V → Finset V} {rt : V → V → ℕ} (hSD : S ⊆ W \ W')
    (hcls : IsCountClassification ε K W' C x y φ L M S g Exc Cc Cr Pc Pr Fo Po rt)
    {T : Finset V} {Z : V → Finset V} {gam alp : V → V → ℕ}
    (hTS : T ⊆ S)
    (hZ : ∀ w ∈ T, ∀ z ∈ Z w,
      gam w z < gridSize ε K ∧ alp w z < gridSize ε K ∧
        g w z ∈ C (x w * gridSize ε K + gam w z) ∧
        z ∈ C (alp w z * gridSize ε K + y w) ∧ z ∈ Exc w ∧
        alp w z ≠ x w ∧ gam w z ≠ crossShiftInv (gridSize ε K) φ (x w) w)
    (hblock : ∀ w ∈ T, ∀ z ∈ Z w, ¬ (z ∈ Pr w ∧ rt w z = gam w z)) :
    ∀ w ∈ T, Z w ⊆ M w := by
  intro w hw z hz
  obtain ⟨hg, ha, hpart, hzC, hzExc, hane, hgne⟩ := hZ w hw z hz
  rcases count_partner_forced_or_foreign (W'' := W'') (F := F) (R := R) hgrid hSD hcls (hTS hw)
    hg ha hpart hzC hzExc rfl hane hgne with hfor | hrow
  · exact hfor
  · exact absurd hrow (hblock w hw z hz)

/-- **The foreign plan of `BKLO.RoutedSweepInvCellCountStep` cannot meet the merge's demand.**

This is the obstruction in its final form.  Suppose a merge books, for each link `w` of a family
`T`, at least `D` foreign slots -- one per unit of the perturbation, which is what
`BKLO.count_partner_forced_or_foreign` leaves it when the forced index of a partner is unavailable
-- all drawn from a common pool `Ground` of at most `(2 h - 1) c` places.  At the design's own
sizes (`T` the links meeting a class, `t = 16 D`, `8 c ≤ 7 t + 8`) this is *inconsistent* with
`BKLO.ForeignSpreadLeftoverPlan`: no such plan `M` exists.

So the route prescribed for the one-link step -- cycle bulk, perturbed forced leftovers routed
cross-side, foreign leftovers in `M` -- cannot be completed against the `K² t` foreign capacity of
`BKLO.RoutedSweepInvCellCountStep`.  Against the `3 K² t` capacity of
`BKLO.ForeignSpreadLeftoverPlanWide` the same count is not contradictory
(`BKLO.foreign_demand_witness_arith`), which is why the repaired step
`BKLO.RoutedSweepInvCellCountWide6hStep` is stated against the wide plan. -/
theorem foreignPlan_cannot_meet_merge_demand
    (hM : ForeignSpreadLeftoverPlan ε K W W' M)
    {T Ground : Finset V} {c D : ℕ}
    (hTW : T ⊆ W \ W')
    (hsub : ∀ w ∈ T, M w ⊆ Ground) (hD : ∀ w ∈ T, D ≤ (M w).card)
    (hT : (2 * gridSize ε K - 1) * (20 * (K * K) * gridClassSize ε K W'.card + 1) ≤ T.card)
    (hZ : Ground.card ≤ (2 * gridSize ε K - 1) * c)
    (ht : gridClassSize ε K W'.card = 16 * D)
    (hc : 8 * c ≤ 7 * gridClassSize ε K W'.card + 8)
    (hK : 2 ≤ K) (hh : 2 ≤ gridSize ε K) (hD0 : 0 < D) : False := by
  classical
  obtain ⟨a, -, hbig⟩ := foreign_demand_exceeds_capacity hsub hD hT hZ ht hc hK hh hD0
  have hmono : T.filter (fun w => a ∈ M w) ⊆ (W \ W').filter (fun w => a ∈ M w) :=
    Finset.filter_subset_filter _ hTW
  exact absurd (le_trans (Finset.card_le_card hmono) (hM a)) (by omega)

/-- **The exact obstruction to `BKLO.RoutedSweepInvCellCountStep` along the prescribed route.**

Put the two halves together.  At a sweep satisfying the counted invariant against the foreign plan
the step offers, suppose an adversarial history has blocked the *forced* routing index of the
partners of the perturbation at each link of a family `T` as large as the design's own count of
links meeting a class, and that each link's perturbation has size `D = t / 16`, its partners drawn
from the pool of `≤ (2 h - 1) c` places the region offers.  Then the situation is contradictory:
no foreign plan of capacity `K² t` can absorb the perturbation.

The free routing index of `BKLO.free_routing_index_available_of_countInv` does not help: it is the
*leftover's* index that the count leaves free, never its partner's.  This is why the step is
re-stated against the wide plan in `BKLO.RoutedSweepInvCellCountWide6hStep`, where the same count
is consistent (`BKLO.foreign_demand_witness_arith`). -/
theorem merge_route_obstruction
    (hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y)
    (hM : ForeignSpreadLeftoverPlan ε K W W' M)
    {φ : V → ℕ} {S : Finset V} {g : V → V → V} {Exc : V → Finset V}
    {Cc Cr Pc Pr Fo Po : V → Finset V} {rt : V → V → ℕ} (hSD : S ⊆ W \ W')
    (hcls : IsCountClassification ε K W' C x y φ L M S g Exc Cc Cr Pc Pr Fo Po rt)
    {T Ground : Finset V} {Z : V → Finset V} {gam alp : V → V → ℕ} {c D : ℕ}
    (hTS : T ⊆ S)
    (hZ : ∀ w ∈ T, ∀ z ∈ Z w,
      gam w z < gridSize ε K ∧ alp w z < gridSize ε K ∧
        g w z ∈ C (x w * gridSize ε K + gam w z) ∧
        z ∈ C (alp w z * gridSize ε K + y w) ∧ z ∈ Exc w ∧
        alp w z ≠ x w ∧ gam w z ≠ crossShiftInv (gridSize ε K) φ (x w) w)
    (hblock : ∀ w ∈ T, ∀ z ∈ Z w, ¬ (z ∈ Pr w ∧ rt w z = gam w z))
    (hpool : ∀ w ∈ T, Z w ⊆ Ground) (hD : ∀ w ∈ T, D ≤ (Z w).card)
    (hT : (2 * gridSize ε K - 1) * (20 * (K * K) * gridClassSize ε K W'.card + 1) ≤ T.card)
    (hGround : Ground.card ≤ (2 * gridSize ε K - 1) * c)
    (ht : gridClassSize ε K W'.card = 16 * D)
    (hc : 8 * c ≤ 7 * gridClassSize ε K W'.card + 8)
    (hK : 2 ≤ K) (hh : 2 ≤ gridSize ε K) (hD0 : 0 < D) : False := by
  classical
  have hZM : ∀ w ∈ T, Z w ⊆ M w :=
    blocked_partners_are_foreign (W'' := W'') (F := F) (R := R) hgrid hSD hcls hTS hZ hblock
  obtain ⟨a, -, hbig⟩ :=
    foreign_demand_exceeds_capacity (M := Z) hpool hD hT hGround ht hc hK hh hD0
  have hmono : T.filter (fun w => a ∈ Z w) ⊆ (W \ W').filter (fun w => a ∈ M w) := by
    intro w hw
    obtain ⟨hwT, hwa⟩ := Finset.mem_filter.1 hw
    exact Finset.mem_filter.2 ⟨hSD (hTS hwT), hZM w hwT hwa⟩
  exact absurd (le_trans (Finset.card_le_card hmono) (hM a)) (by omega)

/-- The arithmetic of `BKLO.foreign_demand_exceeds_capacity_witness`: at those sizes the foreign
demand of the merge exceeds the capacity `K^2 t` of `BKLO.ForeignSpreadLeftoverPlan` and stays
inside the capacity `3 K^2 t` of `BKLO.ForeignSpreadLeftoverPlanWide`. -/
theorem foreign_demand_witness_arith :
    (2 * 2) * 512 * (51199 * 448) < 51199 * (20 * (2 * 2) * 512 + 1) * 32 ∧
      51199 * (20 * (2 * 2) * 512 + 1) * 32 ≤ 3 * ((2 * 2) * 512) * (51199 * 448) := by
  norm_num

end BKLO

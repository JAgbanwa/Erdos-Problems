/-
# The routed residual of AX2 §10 with **free** leftovers: off-class and foreign partners

`BKLO.ForeignObs.not_routedSweepInvCellStepResized` (`BKLO/AX2CellStepForeign.lean`) refutes the
re-sized one-link routed step of `BKLO/AX2RoutedResidualCellResized.lean`.  The refutation has
nothing to do with the sizing of the reservoir: it exploits the fact that
`BKLO.RoutedSweepInvCell` is **region-rigid**.  Every clause of that invariant —
`BKLO.IsCycleRoutedLeftover` for the cycle part, `BKLO.IsCrossRoutedLeftover` for the forced part —
places the partner of a reserved place of a swept link in some class of the grid
(`BKLO.partner_mem_class_of_routedSweepInvCell`).  The classes occupy only a tenth of the reservoir
(`IsGridTwoSidedReservoir.classVolume`), so the adversary may perturb a link by adding one place
`z` of the reservoir lying in **no** class of the grid; `z` then has no legal partner, while both
perturbation budgets `32 · 1 ≤ t` are met.

This file removes that rigidity, and the neighbouring one — a partner in a *foreign* class of the
grid, one belonging to no line of the link's own region — at no cost in the ledger:

* `BKLO.RoutedSweepInvCellFree` — the invariant of `BKLO.RoutedSweepInvCell` with two further
  leftover families:
  - `Po w`, the leftovers of `w` whose partner lies in **no** class of the grid;
  - `Fo w`, the leftovers of `w` whose partner is unconstrained, planned in a second, *globally*
    spread plan `M` (`BKLO.ForeignSpreadLeftoverPlan`).
* `BKLO.excLoad_eq_zero_of_offClassPartner` — an off-class partner is **free**: `BKLO.excLoad`
  filters the leftovers of a vertex by the cell the *partner* lies in, and a partner in no class
  lies in no `BKLO.gridRegion`.  So `Po` costs nothing whatever its size.
* `BKLO.excLoad_le_of_routedSweepInvCellFree` — the per-cell load of the enlarged invariant:
  `4 (t + 1)` for the cycle part, `4 (5 K² t + 1)` for the cross-routed part and `K² t` for the
  foreign part, which the ledger budget `25 K² t` of `BKLO.excLedgerSpread_of_load_le` affords with
  room to spare.
* `BKLO.excLedgerSpread_of_routedSweepInvCellFree`, `BKLO.routedSweepInvCellFree_empty` — the two
  easy halves of the demand;
* `BKLO.RoutedSweepInvCellFreeStep` — the one-link step for the enlarged invariant, at the re-sized
  reservoir, and
* `BKLO.twoSidedUsedClassMatchedResizedPairing_of_cell_step_free` — the re-sized residual demand of
  AX2 §10 from it.

The foreign leftovers are *few*, which is why a globally spread plan is the right shape for them:
at the re-sized perturbation scale a link has at most `t / 32` added places, and on average a place
`a` is claimed by `≈ 20 K² t / c ≈ 20 K²` of the links whose region contains it, since each of the
`≈ 40 K² t h` links of the two grid lines of `a` spreads its `≤ t / 32` claims over the `≈ 2 h t`
places of its own region.  That is far inside the `K² t` of `BKLO.ForeignSpreadLeftoverPlan`, and
unlike the *forced* leftovers — about `t` per link, for which `BKLO.not_routedSweepInvSpreadStep`
shows a global plan needs `≈ 5 K² t · h`.  Exhibiting such a plan is part of the unproved one-link
step below; the cell-balanced plan `L`, by contrast, is constructed outright in
`BKLO.exists_cell_balanced_plan_of_resized` (`BKLO/AX2CellPlanExists.lean`).

Everything here is `sorry`-free; the one-link step `BKLO.RoutedSweepInvCellFreeStep` is *not*
proved.
-/
import BKLO.AX2RoutedResidualCellResized

open Finset

namespace BKLO

variable {V : Type} [DecidableEq V]
variable {ε : ℝ} {K : ℕ} {W W' W'' : Finset V} {F R : Finset (Sym2 V)} {C : ℕ → Finset V}
  {x y : V → ℕ} {L M : V → Finset V}

/-! ### The second plan, and the enlarged invariant -/

/-- **A globally spread plan for the foreign leftovers.**  `M w` is the set of places at which the
link `w` may leave a leftover whose partner is not routed at all, and the plan is spread when no
place is planned at more than `K² t` links altogether.  Unlike `BKLO.SpreadLeftoverPlan` — which
`BKLO.not_routedSweepInvSpreadStep` refutes for the *forced* leftovers, of which a link may have a
whole quarter class — this is affordable, because at the re-sized perturbation scale a link has at
most `t / 32` foreign places to place. -/
def ForeignSpreadLeftoverPlan (ε : ℝ) (K : ℕ) (W W' : Finset V) (M : V → Finset V) : Prop :=
  ∀ a : V, (((W \ W').filter (fun w => a ∈ M w)).card) ≤ K * K * gridClassSize ε K W'.card

/-- **The routed invariant of a class-matched sweep against a cell-balanced plan, with free
leftovers.**  As `BKLO.RoutedSweepInvCell`, with two further families of leftovers:

* `Po w`, whose partners lie in no class of the grid — these are free of charge in the ledger,
  because `BKLO.excLoad` only counts a leftover when its partner lies in the queried region;
* `Fo w`, whose partners are unconstrained — these are charged in full, and are therefore confined
  to the globally spread plan `M`. -/
def RoutedSweepInvCellFree (ε : ℝ) (K : ℕ) (W W' : Finset V) (C : ℕ → Finset V) (x y φ : V → ℕ)
    (L M : V → Finset V) (S : Finset V) (g : V → V → V) (Exc : V → Finset V) : Prop :=
  S ⊆ W \ W' ∧
  ∃ (Cc Cr Pc Pr Fo Po : V → Finset V) (rt : V → V → ℕ),
    -- the leftovers split into the cycle part, the forced part and the two free parts
    (∀ w ∈ S, Exc w ⊆ ((Cc w ∪ Cr w) ∪ (Pc w ∪ Pr w)) ∪ (Fo w ∪ Po w)) ∧
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
    (∀ w ∈ S, ∀ w' ∈ S, ∀ a : V, a ∈ Pr w → a ∈ Pr w' → rt w a = rt w' a → x w = x w') ∧
    -- the foreign leftovers are planned in the globally spread plan
    (∀ w ∈ S, Fo w ⊆ M w) ∧
    -- and the free leftovers have a partner in no class of the grid
    (∀ w ∈ S, ∀ a ∈ Po w, ∀ i < gridSize ε K * gridSize ε K, g w a ∉ C i)

/-- The empty sweep satisfies the enlarged invariant, against any pair of plans. -/
theorem routedSweepInvCellFree_empty (φ : V → ℕ) (L M : V → Finset V) :
    RoutedSweepInvCellFree ε K W W' C x y φ L M (∅ : Finset V) (fun _ a => a) (fun _ => ∅) := by
  classical
  refine ⟨Finset.empty_subset _, (fun _ => ∅), (fun _ => ∅), (fun _ => ∅), (fun _ => ∅),
    (fun _ => ∅), (fun _ => ∅), (fun _ _ => 0), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩ <;>
    intro a ha <;> simp_all

/-! ### An off-class partner is free -/

/-- **A leftover whose partner lies in no class of the grid costs nothing.**  `BKLO.excLoad`
counts a leftover of `a` at the cell `(P, Q)` only when the partner of `a` lies in the region of
that cell, and a region is a union of classes. -/
theorem excLoad_eq_zero_of_offClassPartner {h : ℕ} {C : ℕ → Finset V} {g : V → V → V}
    {S : Finset V} {Po : V → Finset V} {a : V} {P Q : ℕ} (hP : P < h) (hQ : Q < h)
    (hPo : ∀ w ∈ S, ∀ b ∈ Po w, ∀ i < h * h, g w b ∉ C i) :
    excLoad h C g S Po a P Q = 0 := by
  classical
  rw [excLoad, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro w hwS ⟨hwa, hwreg⟩
  rw [gridRegion_eq_biUnion] at hwreg
  obtain ⟨k, hk, hmem⟩ := Finset.mem_biUnion.1 hwreg
  exact hPo w hwS a hwa k (gridIdx_lt hP hQ hk) hmem

/-! ### The load of the enlarged invariant -/

/-- **The per-cell load of the enlarged invariant.**  The cycle part costs `4 (t + 1)`
(`BKLO.excLoad_le_of_cycleRouted`), the cross-routed part its four cell counts
`4 (5 K² t + 1)` (`BKLO.excLoad_le_routed`, `BKLO.excRouteCount_le_of_cellPlan_col`), the foreign
part the global load `K² t` of its plan, and the off-class part nothing at all. -/
theorem excLoad_le_of_routedSweepInvCellFree
    (hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y)
    {φ : V → ℕ} (hφlt : ∀ w, φ w < gridSize ε K)
    (hbal : ∀ p q j : ℕ, (((W \ W').filter (fun w => x w = p ∧ y w = q ∧ φ w = j)).card)
      ≤ (((W \ W').filter (fun w => x w = p ∧ y w = q)).card) / gridSize ε K + 1)
    (hL : CellSpreadLeftoverPlan ε K W W' x y L) (hM : ForeignSpreadLeftoverPlan ε K W W' M)
    {S : Finset V} {g : V → V → V} {Exc : V → Finset V}
    (hInv : RoutedSweepInvCellFree ε K W W' C x y φ L M S g Exc)
    (a : V) {P Q : ℕ} (hP : P < gridSize ε K) (hQ : Q < gridSize ε K) :
    excLoad (gridSize ε K) C g S Exc a P Q
      ≤ 4 * ((20 * (K * K) * gridClassSize ε K W'.card + 1) / gridSize ε K + 1)
        + 4 * (5 * (K * K) * gridClassSize ε K W'.card + 1)
        + K * K * gridClassSize ε K W'.card := by
  classical
  obtain ⟨hSD, Cc, Cr, Pc, Pr, Fo, Po, rt, hsplit, hdisjC, hcyc, hrtlt, hroute, hPcL, hPrL,
    hPcRow, hPrCol, hpinC, hpinR, hFoM, hPo⟩ := hInv
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
      · -- an off-class partner cannot lie in the queried region
        rw [gridRegion_eq_biUnion] at hwreg
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
  have hb1 : excRouteCount S Pc a (fun w => rt w a) P ≤ 5 * (K * K) * t + 1 :=
    excRouteCount_le_of_cellPlan_col (W'' := W'') (F := F) (R := R) hgrid hSD hL hPcL hPcRow a
      (fun w => rt w a) (fun w hw w' hw' ha ha' hpf => hpinC w hw w' hw' a ha ha' hpf) P
  have hb2 : excRouteCount S Pc a y Q ≤ 5 * (K * K) * t + 1 :=
    excRouteCount_le_of_cellPlan_col (W'' := W'') (F := F) (R := R) hgrid hSD hL hPcL hPcRow a
      y (fun w _ w' _ _ _ hpf => hpf) Q
  have hb3 : excRouteCount S Pr a x P ≤ 5 * (K * K) * t + 1 :=
    excRouteCount_le_of_cellPlan_row (W'' := W'') (F := F) (R := R) hgrid hSD hL hPrL hPrCol a
      x (fun w _ w' _ _ _ hpf => hpf) P
  have hb4 : excRouteCount S Pr a (fun w => rt w a) Q ≤ 5 * (K * K) * t + 1 :=
    excRouteCount_le_of_cellPlan_row (W'' := W'') (F := F) (R := R) hgrid hSD hL hPrL hPrCol a
      (fun w => rt w a) (fun w hw w' hw' ha ha' hpf => hpinR w hw w' hw' a ha ha' hpf) Q
  -- the foreign part
  have hfor : A3.card ≤ K * K * t := by
    refine le_trans (Finset.card_le_card ?_) (hM a)
    intro w hw
    obtain ⟨hwS, hwa⟩ := Finset.mem_filter.1 hw
    exact Finset.mem_filter.2 ⟨hSD hwS, hFoM w hwS hwa⟩
  omega

/-- **The enlarged invariant keeps the leftover ledger spread.**  Its load is
`4 (t + 1) + 4 (5 K² t + 1) + K² t ≤ 25 K² t`, the budget of
`BKLO.excLedgerSpread_of_load_le`. -/
theorem excLedgerSpread_of_routedSweepInvCellFree
    (hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y)
    (hε : 0 < ε) (hε' : ε ≤ 1 / 100) (hK : 2 ≤ K)
    (ht : 512 ≤ gridClassSize ε K W'.card)
    {φ : V → ℕ} (hφlt : ∀ w, φ w < gridSize ε K)
    (hbal : ∀ p q j : ℕ, (((W \ W').filter (fun w => x w = p ∧ y w = q ∧ φ w = j)).card)
      ≤ (((W \ W').filter (fun w => x w = p ∧ y w = q)).card) / gridSize ε K + 1)
    (hL : CellSpreadLeftoverPlan ε K W W' x y L) (hM : ForeignSpreadLeftoverPlan ε K W W' M)
    {S : Finset V} {g : V → V → V} {Exc : V → Finset V}
    (hInv : RoutedSweepInvCellFree ε K W W' C x y φ L M S g Exc) :
    ExcLedgerSpread ε K W' C g S Exc := by
  classical
  refine excLedgerSpread_of_load_le (C := C) (W' := W') hε hε' ?_
  intro a P hP Q hQ
  have h1 := excLoad_le_of_routedSweepInvCellFree (W'' := W'') (F := F) (R := R) hgrid hφlt hbal
    hL hM hInv a hP hQ
  set t : ℕ := gridClassSize ε K W'.card with htdef
  have h2 : (20 * (K * K) * t + 1) / gridSize ε K + 1 ≤ t + 1 :=
    cell_shift_fibre_le_succ_class (W' := W') hε hε' hK ht
  have h3 : 4 * ((20 * (K * K) * t + 1) / gridSize ε K + 1) ≤ 4 * (t + 1) :=
    Nat.mul_le_mul_left 4 h2
  have hKK : 4 ≤ K * K := Nat.mul_le_mul hK hK
  have e1 : 25 * (K * K) * t = 25 * ((K * K) * t) := by ring
  have e2 : 5 * (K * K) * t = 5 * ((K * K) * t) := by ring
  have h4 : 4 * t ≤ (K * K) * t := Nat.mul_le_mul_right _ hKK
  have h5 : 1 ≤ (K * K) * t := Nat.one_le_iff_ne_zero.2 (by positivity)
  omega

/-! ### The residual, from the one-link step with free leftovers -/

/-- **The one-link routed step against a cell-balanced plan and a foreign plan, at the re-sized
reservoir.**  This is `BKLO.RoutedSweepInvCellStepResized` with the enlarged invariant: besides the
cell-balanced plan `L` for the forced leftovers the step may fix a globally spread plan `M` for the
foreign ones, and a leftover whose partner lies in no class of the grid is free.

The obstruction `BKLO.ForeignObs.not_routedSweepInvCellStepResized` does not apply to this
statement: the added place lying in no class of the grid is paired with a reserved place of the
region, which joins the free family `Po`. -/
def RoutedSweepInvCellFreeStep : Prop :=
  ∀ {V : Type} [DecidableEq V] {ε : ℝ} {K : ℕ} {W W' W'' : Finset V}
    {F R : Finset (Sym2 V)} {C : ℕ → Finset V} {x y : V → ℕ} {q c : ℕ},
    IsGridTwoSidedReservoirEighth ε K W W' W'' F R C x y →
    (∀ e ∈ F, ¬ e.IsDiag) → W' ⊆ W →
    (∀ i < gridSize ε K * gridSize ε K, (C i).card = q) →
    (∀ v ∈ W \ W', ∀ i ∈ gridIdx (gridSize ε K) (x v) (y v),
      (resLink R W' v ∩ C i).card = c) →
    7 * q ≤ 8 * c →
    0 < ε → ε ≤ 1 / 100 → 2 ≤ K → 512 ≤ gridClassSize ε K W'.card →
    ∀ {φ : V → ℕ}, (∀ w, φ w < gridSize ε K) →
    (∀ p q j : ℕ, (((W \ W').filter (fun w => x w = p ∧ y w = q ∧ φ w = j)).card)
      ≤ (((W \ W').filter (fun w => x w = p ∧ y w = q)).card) / gridSize ε K + 1) →
    ∀ {X : V → Finset V},
    ∃ L M : V → Finset V, CellSpreadLeftoverPlan ε K W W' x y L ∧
      ForeignSpreadLeftoverPlan ε K W W' M ∧
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
      RoutedSweepInvCellFree ε K W W' C x y φ L M S g₀ Exc →
      ∃ (p : V → V) (e : Finset V),
        (∀ a ∈ X u, p a ∈ X u) ∧ (∀ a ∈ X u, p (p a) = a) ∧ (∀ a ∈ X u, p a ≠ a) ∧
        (∀ a ∈ X u, s(a, p a) ∈ F ∧ s(a, p a) ∉ U) ∧
        IsClassMatchedSweep (gridSize ε K) C R W' X x y
          (fun w β => crossShift (gridSize ε K) φ β w)
          (fun w α => crossShiftInv (gridSize ε K) φ α w)
          (insert u S) (Function.update g₀ u p) (Function.update Exc u e) ∧
        RoutedSweepInvCellFree ε K W W' C x y φ L M (insert u S) (Function.update g₀ u p)
          (Function.update Exc u e)

/-- **The re-sized residual demand of AX2 §10, from the one-link routed step with free
leftovers.** -/
theorem twoSidedUsedClassMatchedResizedPairing_of_cell_step_free
    (hstep : RoutedSweepInvCellFreeStep) : TwoSidedUsedClassMatchedResizedPairing := by
  intro V _ ε K W W' W'' F R C x y q c X hgrid8 hnd hW'W hq hcres hqc8 hε hε' hK hbig
  classical
  set hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y :=
    hgrid8.toIsGridTwoSidedReservoir with hgriddef
  obtain ⟨φ, hφlt, hφcell⟩ :=
    exists_cell_balanced_shift (W \ W') x y (gridSize_pos ε K)
  obtain ⟨L, M, hL, hM, hstep'⟩ :=
    hstep hgrid8 hnd hW'W hq hcres hqc8 hε hε' hK hbig hφlt hφcell (X := X)
  refine ⟨fun w β => crossShift (gridSize ε K) φ β w,
    fun w α => crossShiftInv (gridSize ε K) φ α w,
    RoutedSweepInvCellFree ε K W W' C x y φ L M,
    fun w β => crossShift_lt (gridSize_pos ε K) φ β w,
    fun w α => crossShiftInv_lt (gridSize_pos ε K) φ α w,
    classMatchingFibres_of_cellBalanced hgrid hφlt hφcell,
    routedSweepInvCellFree_empty φ L M, ?_, ?_⟩
  · intro S g Exc hInv
    exact excLedgerSpread_of_routedSweepInvCellFree (W'' := W'') (F := F) (R := R) hgrid hε hε' hK
      hbig hφlt hφcell hL hM hInv
  · intro S g₀ Exc u n m U hu hXu hXeven hadd32 hdel32 hadd hdel hUdeg hUused hmargin hSD huS
      hmaps hginv hsweep hInv
    exact hstep' hu hXu hXeven hadd32 hdel32 hadd hdel hUdeg hUused hmargin hSD huS hmaps hginv
      hsweep hInv

/-- **Main theorem (AX2 half of Erdős #81), from the three classical inputs and the one-link
routed step with free leftovers at the re-sized reservoir.** -/
theorem triangle_decomposition_of_inputs_and_cell_step_free
    (hDross : FracTriangleThreshold) (hNib : FracToApproxMaxDeg) (hDirac : PerfectMatchingDirac)
    (hstep : RoutedSweepInvCellFreeStep) :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        n₀ ≤ Fintype.card V →
        (3 ∣ G.edgeFinset.card ∧ ∀ v, Even (G.degree v)) →
        (9 / 10 + ε) * (Fintype.card V : ℝ) ≤ (G.minDegree : ℝ) →
        TriangleDecomposable G :=
  triangle_decomposition_of_inputs_and_twoSidedUsedClassMatchedResized hDross hNib hDirac
    (twoSidedUsedClassMatchedResizedPairing_of_cell_step_free hstep)

end BKLO

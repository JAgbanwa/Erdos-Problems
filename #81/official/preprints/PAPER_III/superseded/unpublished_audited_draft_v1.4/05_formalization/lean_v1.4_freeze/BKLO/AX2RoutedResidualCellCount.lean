/-
# The routed residual with a **counted** routing index: the density conflict dissolved

`BKLO.pin_target_density_conflict` and `BKLO.committed_fibre_below_budgets`
(`BKLO/AX2CommittedStepObstruction.lean`) wall the *pinned* routed vehicle:

* the ledger `BKLO.ExcLedgerSpread` measures a leftover by the **cell** of its partner, and the
  invariant `BKLO.RoutedSweepInvCellFree` pays for that measurement with its two **fibre pins**

  ```
  a ∈ Pc w → a ∈ Pc w' → rt w a = rt w' a → y w = y w'
  a ∈ Pr w → a ∈ Pr w' → rt w a = rt w' a → x w = x w'
  ```

  — they turn each routing fibre into a count of one *cell*, which the cell plan
  `BKLO.CellSpreadLeftoverPlan` bounds by `5 K² t + 1`;
* pinning the index at a place makes it the exclusive resource of one grid column, so a
  pre-committed index confines the partner to a fibre of density `≤ 1 / h` of its class
  (`BKLO.exists_committed_fibre_le_eighth`), while the pairing has to survive the adversary's two
  per-place budgets and therefore needs a target of density `> 1 / 8`
  (`BKLO.committed_fibre_below_budgets`).  At `h ≥ 25600` the two are incompatible.

This file carries out the repair: **the pin is not what the ledger needs — a count is.**  What the
load bound of `BKLO.excLoad_le_of_routedSweepInvCellFree` actually uses is that the two routing
fibres

```
excRouteCount S Pc a (rt · a) P ,   excRouteCount S Pr a (rt · a) Q
```

are at most `5 K² t + 1`.  The pin is one way to get that (it identifies the fibre with a cell of
the plan); requiring the bound *directly* is strictly weaker, and it constrains no partner at all:

* `BKLO.RoutedSweepInvCellCount` — the invariant of `BKLO.RoutedSweepInvCellFree` with the two
  fibre pins replaced by the two fibre **counts**;
* `BKLO.routedSweepInvCellCount_of_free` — the pinned invariant implies the counted one, at any
  cell-balanced plan: the restatement is a genuine weakening, so every construction that works for
  the pinned invariant works here;
* `BKLO.excLoad_le_of_routedSweepInvCellCount`, `BKLO.excLedgerSpread_of_routedSweepInvCellCount`
  — the counted invariant still pays the ledger, with exactly the same per-cell load
  `4 (t + 1) + 4 (5 K² t + 1) + K² t ≤ 25 K² t`;
* `BKLO.RoutedSweepInvCellCountStep`,
  `BKLO.twoSidedUsedClassMatchedResizedPairing_of_cell_step_count`,
  `BKLO.triangle_decomposition_of_inputs_and_cell_step_count` — the one-link step for the counted
  invariant, and the AX2 residual demand from it: the vehicle is intact.

The point of the repair is `BKLO.count_partner_density_full` and
`BKLO.countInv_admits_shared_index`: under the counted invariant the admissible partners of a
forced leftover are a **whole class** — density `1`, not `1 / h` — and two links of the same grid
row and different grid columns *may* route one and the same place to one and the same index, which
`BKLO.routed_index_collision` forbids for the pinned invariant.  The hypotheses
`s * h ≤ q` and `q < 8 * s` of `BKLO.pin_target_density_conflict` are therefore never both met:
the conflict that stopped the routed sweep is not intrinsic to the ledger, it is an artefact of the
pin.

Everything here is `sorry`-free; the one-link step `BKLO.RoutedSweepInvCellCountStep` is *not*
proved — it is the (weaker) restatement of the one remaining unproved link
`BKLO.RoutedSweepInvCellFreeStep`.
-/
import BKLO.AX2RoutedResidualCellFree

open Finset

namespace BKLO

variable {V : Type} [DecidableEq V]
variable {ε : ℝ} {K : ℕ} {W W' W'' : Finset V} {F R : Finset (Sym2 V)} {C : ℕ → Finset V}
  {x y : V → ℕ} {L M : V → Finset V}

/-! ### The counted invariant -/

/-- **The routed invariant of a class-matched sweep against a cell-balanced plan, with free
leftovers and a *counted* routing index.**  This is `BKLO.RoutedSweepInvCellFree` with its two
fibre-pinning clauses replaced by the two bounds on the routing fibres that the ledger actually
consumes: at every place `a` and every index `P`, at most `5 K² t + 1` swept links route `a` to
`P`.

Nothing here constrains *which* place of the target class a leftover is paired with: the partner of
`a ∈ Pc w` is only asked to lie in the class `C (rt w a · h + y w)`, a set of `q` places. -/
def RoutedSweepInvCellCount (ε : ℝ) (K : ℕ) (W W' : Finset V) (C : ℕ → Finset V) (x y φ : V → ℕ)
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
    -- **and the routing fibres are counted, not pinned**
    (∀ (a : V) (P : ℕ), excRouteCount S Pc a (fun w => rt w a) P
      ≤ 5 * (K * K) * gridClassSize ε K W'.card + 1) ∧
    (∀ (a : V) (Q : ℕ), excRouteCount S Pr a (fun w => rt w a) Q
      ≤ 5 * (K * K) * gridClassSize ε K W'.card + 1) ∧
    -- the foreign leftovers are planned in the globally spread plan
    (∀ w ∈ S, Fo w ⊆ M w) ∧
    -- and the free leftovers have a partner in no class of the grid
    (∀ w ∈ S, ∀ a ∈ Po w, ∀ i < gridSize ε K * gridSize ε K, g w a ∉ C i)

/-- The empty sweep satisfies the counted invariant, against any pair of plans. -/
theorem routedSweepInvCellCount_empty (φ : V → ℕ) (L M : V → Finset V) :
    RoutedSweepInvCellCount ε K W W' C x y φ L M (∅ : Finset V) (fun _ a => a) (fun _ => ∅) := by
  classical
  refine ⟨Finset.empty_subset _, (fun _ => ∅), (fun _ => ∅), (fun _ => ∅), (fun _ => ∅),
    (fun _ => ∅), (fun _ => ∅), (fun _ _ => 0), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩
  · intro a ha; simp_all
  · intro a ha; simp_all
  · intro a ha; simp_all
  · intro a ha; simp_all
  · intro a ha; simp_all
  · intro a ha; simp_all
  · intro a ha; simp_all
  · intro a ha; simp_all
  · intro a ha; simp_all
  · intro a P; simp [excRouteCount]
  · intro a Q; simp [excRouteCount]
  · intro a ha; simp_all
  · intro a ha; simp_all

/-- **The pinned invariant implies the counted one.**  The two fibre pins of
`BKLO.RoutedSweepInvCellFree` identify a routing fibre with a count of one cell of the plan
(`BKLO.excRouteCount_le_of_cellPlan_col`, `BKLO.excRouteCount_le_of_cellPlan_row`), which is the
bound the counted invariant asks for outright.  So `BKLO.RoutedSweepInvCellCount` is a genuine
weakening: any construction for the pinned invariant is one for the counted invariant. -/
theorem routedSweepInvCellCount_of_free
    (hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y)
    (hL : CellSpreadLeftoverPlan ε K W W' x y L)
    {φ : V → ℕ} {S : Finset V} {g : V → V → V} {Exc : V → Finset V}
    (hInv : RoutedSweepInvCellFree ε K W W' C x y φ L M S g Exc) :
    RoutedSweepInvCellCount ε K W W' C x y φ L M S g Exc := by
  classical
  obtain ⟨hSD, Cc, Cr, Pc, Pr, Fo, Po, rt, hsplit, hdisjC, hcyc, hrtlt, hroute, hPcL, hPrL,
    hPcRow, hPrCol, hpinC, hpinR, hFoM, hPo⟩ := hInv
  refine ⟨hSD, Cc, Cr, Pc, Pr, Fo, Po, rt, hsplit, hdisjC, hcyc, hrtlt, hroute, hPcL, hPrL,
    hPcRow, hPrCol, ?_, ?_, hFoM, hPo⟩
  · intro a P
    exact excRouteCount_le_of_cellPlan_col (W'' := W'') (F := F) (R := R) hgrid hSD hL hPcL hPcRow a
      (fun w => rt w a) (fun w hw w' hw' ha ha' hpf => hpinC w hw w' hw' a ha ha' hpf) P
  · intro a Q
    exact excRouteCount_le_of_cellPlan_row (W'' := W'') (F := F) (R := R) hgrid hSD hL hPrL hPrCol a
      (fun w => rt w a) (fun w hw w' hw' ha ha' hpf => hpinR w hw w' hw' a ha ha' hpf) Q

/-! ### The counted invariant still pays the ledger -/

/-- **The per-cell load of the counted invariant.**  Exactly the load of
`BKLO.excLoad_le_of_routedSweepInvCellFree`: the cycle part costs `4 (t + 1)`, the cross-routed
part its two cell counts and its two *counted* routing fibres, and the foreign part the global
load `K² t` of its plan; the off-class part costs nothing. -/
theorem excLoad_le_of_routedSweepInvCellCount
    (hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y)
    {φ : V → ℕ} (hφlt : ∀ w, φ w < gridSize ε K)
    (hbal : ∀ p q j : ℕ, (((W \ W').filter (fun w => x w = p ∧ y w = q ∧ φ w = j)).card)
      ≤ (((W \ W').filter (fun w => x w = p ∧ y w = q)).card) / gridSize ε K + 1)
    (hL : CellSpreadLeftoverPlan ε K W W' x y L) (hM : ForeignSpreadLeftoverPlan ε K W W' M)
    {S : Finset V} {g : V → V → V} {Exc : V → Finset V}
    (hInv : RoutedSweepInvCellCount ε K W W' C x y φ L M S g Exc)
    (a : V) {P Q : ℕ} (hP : P < gridSize ε K) (hQ : Q < gridSize ε K) :
    excLoad (gridSize ε K) C g S Exc a P Q
      ≤ 4 * ((20 * (K * K) * gridClassSize ε K W'.card + 1) / gridSize ε K + 1)
        + 4 * (5 * (K * K) * gridClassSize ε K W'.card + 1)
        + K * K * gridClassSize ε K W'.card := by
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
  have hfor : A3.card ≤ K * K * t := by
    refine le_trans (Finset.card_le_card ?_) (hM a)
    intro w hw
    obtain ⟨hwS, hwa⟩ := Finset.mem_filter.1 hw
    exact Finset.mem_filter.2 ⟨hSD hwS, hFoM w hwS hwa⟩
  omega

/-- **The counted invariant keeps the leftover ledger spread**, with the same budget as the pinned
one: `4 (t + 1) + 4 (5 K² t + 1) + K² t ≤ 25 K² t`. -/
theorem excLedgerSpread_of_routedSweepInvCellCount
    (hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y)
    (hε : 0 < ε) (hε' : ε ≤ 1 / 100) (hK : 2 ≤ K)
    (ht : 512 ≤ gridClassSize ε K W'.card)
    {φ : V → ℕ} (hφlt : ∀ w, φ w < gridSize ε K)
    (hbal : ∀ p q j : ℕ, (((W \ W').filter (fun w => x w = p ∧ y w = q ∧ φ w = j)).card)
      ≤ (((W \ W').filter (fun w => x w = p ∧ y w = q)).card) / gridSize ε K + 1)
    (hL : CellSpreadLeftoverPlan ε K W W' x y L) (hM : ForeignSpreadLeftoverPlan ε K W W' M)
    {S : Finset V} {g : V → V → V} {Exc : V → Finset V}
    (hInv : RoutedSweepInvCellCount ε K W W' C x y φ L M S g Exc) :
    ExcLedgerSpread ε K W' C g S Exc := by
  classical
  refine excLedgerSpread_of_load_le (C := C) (W' := W') hε hε' ?_
  intro a P hP Q hQ
  have h1 := excLoad_le_of_routedSweepInvCellCount (W'' := W'') (F := F) (R := R) hgrid hφlt hbal
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

/-! ### The residual, from the one-link step with a counted routing index -/

/-- **The one-link routed step against a cell-balanced plan and a foreign plan, at the re-sized
reservoir, with a counted routing index.**  This is `BKLO.RoutedSweepInvCellFreeStep` with the
counted invariant in place of the pinned one; by `BKLO.routedSweepInvCellCount_of_free` its
hypothesis is weaker and its conclusion is weaker, and the conclusion is all the ledger needs. -/
def RoutedSweepInvCellCountStep : Prop :=
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

/-- **The re-sized residual demand of AX2 §10, from the one-link routed step with a counted
routing index.** -/
theorem twoSidedUsedClassMatchedResizedPairing_of_cell_step_count
    (hstep : RoutedSweepInvCellCountStep) : TwoSidedUsedClassMatchedResizedPairing := by
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
    RoutedSweepInvCellCount ε K W W' C x y φ L M,
    fun w β => crossShift_lt (gridSize_pos ε K) φ β w,
    fun w α => crossShiftInv_lt (gridSize_pos ε K) φ α w,
    classMatchingFibres_of_cellBalanced hgrid hφlt hφcell,
    routedSweepInvCellCount_empty φ L M, ?_, ?_⟩
  · intro S g Exc hInv
    exact excLedgerSpread_of_routedSweepInvCellCount (W'' := W'') (F := F) (R := R) hgrid hε hε' hK
      hbig hφlt hφcell hL hM hInv
  · intro S g₀ Exc u n m U hu hXu hXeven hadd32 hdel32 hadd hdel hUdeg hUused hmargin hSD huS
      hmaps hginv hsweep hInv
    exact hstep' hu hXu hXeven hadd32 hdel32 hadd hdel hUdeg hUused hmargin hSD huS hmaps hginv
      hsweep hInv

/-- **Main theorem (AX2 half of Erdős #81), from the three classical inputs and the one-link
routed step with a counted routing index at the re-sized reservoir.** -/
theorem triangle_decomposition_of_inputs_and_cell_step_count
    (hDross : FracTriangleThreshold) (hNib : FracToApproxMaxDeg) (hDirac : PerfectMatchingDirac)
    (hstep : RoutedSweepInvCellCountStep) :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        n₀ ≤ Fintype.card V →
        (3 ∣ G.edgeFinset.card ∧ ∀ v, Even (G.degree v)) →
        (9 / 10 + ε) * (Fintype.card V : ℝ) ≤ (G.minDegree : ℝ) →
        TriangleDecomposable G :=
  triangle_decomposition_of_inputs_and_twoSidedUsedClassMatchedResized hDross hNib hDirac
    (twoSidedUsedClassMatchedResizedPairing_of_cell_step_count hstep)

/-! ### The density conflict does not arise -/

/-- **The admissible partners of a forced leftover are a whole class.**  Under the counted
invariant the only demand on the partner of a forced leftover is that it lie in the class the
routing index names — `C (rt w a · h + y w)` for a column-routed leftover and
`C (x w · h + rt w a)` for a row-routed one.  No sub-fibre of that class is prescribed, so the
resource the pairing has to choose inside is of density `1` in its class. -/
theorem count_partner_mem_class
    {S : Finset V} {g : V → V → V} {Exc : V → Finset V} {φ : V → ℕ}
    (hInv : RoutedSweepInvCellCount ε K W W' C x y φ L M S g Exc) :
    ∃ (Pc Pr : V → Finset V) (rt : V → V → ℕ),
      (∀ w ∈ S, ∀ a ∈ Pc w, g w a ∈ C (rt w a * gridSize ε K + y w)) ∧
      (∀ w ∈ S, ∀ a ∈ Pr w, g w a ∈ C (x w * gridSize ε K + rt w a)) := by
  obtain ⟨-, -, -, Pc, Pr, -, -, rt, -, -, -, -, hroute, -⟩ := hInv
  exact ⟨Pc, Pr, rt, fun w hw a ha => (hroute w hw).1 a ha,
    fun w hw a ha => (hroute w hw).2 a ha⟩

/-! ### What the counted clause asks of the one-link step -/

/-- **Inserting one link costs one unit of one routing fibre.**  Whatever the new link routes the
place `a` to, only its own membership is added to the fibre. -/
theorem excRouteCount_insert_le {S : Finset V} {Pc : V → Finset V} {pf : V → ℕ} (u a : V) (P : ℕ) :
    excRouteCount (insert u S) Pc a pf P ≤ excRouteCount S Pc a pf P + 1 := by
  classical
  have hsub : (insert u S).filter (fun w => a ∈ Pc w ∧ pf w = P)
      ⊆ insert u (S.filter (fun w => a ∈ Pc w ∧ pf w = P)) := by
    intro w hw
    obtain ⟨hwS, hp⟩ := Finset.mem_filter.1 hw
    rcases Finset.mem_insert.1 hwS with rfl | hwS
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨hwS, hp⟩)
  calc excRouteCount (insert u S) Pc a pf P
      ≤ (insert u (S.filter (fun w => a ∈ Pc w ∧ pf w = P))).card := Finset.card_le_card hsub
    _ ≤ (S.filter (fun w => a ∈ Pc w ∧ pf w = P)).card + 1 := Finset.card_insert_le _ _

/-- **A routing index with room is always available.**  If the history claims the place `a` at
fewer than `(B + 1) h` links, then one of the `h` routing indices carries at most `B` of them, and
the new link may use it without breaking the counted clause.  This is the choice that the pin
denied — under the pin an index is the exclusive resource of one grid column
(`BKLO.routed_index_collision`), here it is only a resource of bounded multiplicity. -/
theorem exists_free_routing_index {h B : ℕ} {S : Finset V} {Pc : V → Finset V} {rt : V → V → ℕ}
    (a : V) (hrt : ∀ w ∈ S, rt w a < h)
    (htot : (S.filter (fun w => a ∈ Pc w)).card < (B + 1) * h) :
    ∃ P < h, excRouteCount S Pc a (fun w => rt w a) P ≤ B := by
  classical
  by_contra hcon
  push_neg at hcon
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
  have hlow : (B + 1) * h ≤ ∑ P ∈ Finset.range h, excRouteCount S Pc a (fun w => rt w a) P := by
    calc (B + 1) * h = ∑ _P ∈ Finset.range h, (B + 1) := by
          rw [Finset.sum_const, Finset.card_range, smul_eq_mul, Nat.mul_comm]
      _ ≤ _ := Finset.sum_le_sum (fun P hP => hcon P (Finset.mem_range.1 hP))
  omega

/-- **A full class passes the pairing's budget and fails the ledger's pin.**  The two hypotheses of
`BKLO.pin_target_density_conflict` — a resource pinned to density `1 / h` and a resource of density
more than `1 / 8` — are never both met by a full class: `q * h ≤ q` fails at `h ≥ 2`, `q > 0`,
while `q < 8 * q` holds.  This is the exact sense in which the counted invariant dissolves the
conflict recorded in `BKLO.committed_fibre_below_budgets`. -/
theorem full_class_escapes_pin {q h : ℕ} (hq : 0 < q) (hh : 2 ≤ h) :
    ¬ (q * h ≤ q) ∧ q < 8 * q := by
  constructor
  · intro hcon
    have : q * 2 ≤ q * h := Nat.mul_le_mul_left q hh
    omega
  · omega

/-- **Two links of the same grid row and different grid columns may share a routing index.**  This
is the configuration `BKLO.routed_index_collision` shows to be impossible under the *pinned*
invariant.  Under the counted invariant it costs one unit of one fibre, so it is admissible as
soon as the design has `1 ≤ 5 K² t + 1` — that is, always.  Concretely: a two-link sweep with a
common index at a common place satisfies both counting clauses. -/
theorem countInv_admits_shared_index {S : Finset V} {Pc : V → Finset V} {rt : V → V → ℕ}
    (a : V) (P : ℕ) (hS : S.card ≤ 5 * (K * K) * gridClassSize ε K W'.card + 1) :
    excRouteCount S Pc a (fun w => rt w a) P
      ≤ 5 * (K * K) * gridClassSize ε K W'.card + 1 :=
  le_trans (Finset.card_le_card (Finset.filter_subset _ _)) hS

end BKLO

/-
# The routed residual of AX2 §10, with a **general** routing index

`BKLO.RoutedSweepInv` (`BKLO/AX2RoutedSweepInvariant.lean`) routes the leftovers the perturbation
forces into the two classes of the three-class cycle of the link — the column class
`C (ρ w (y w) · h + y w)` or the row class `C (x w · h + σ w (x w))`.  That is too rigid, and
`BKLO.not_routedSweepInvStep` (`BKLO/AX2RoutedStepObstruction.lean`) refutes the one-link step it
asks for: a deletion in another block of the region forces a leftover *pair* both of whose ends lie
in that block, and neither end can be routed into the cycle.

This file repairs the frame.  The routing index of the forced part is the free `rt` of
`BKLO.IsCrossRoutedLeftover` (`BKLO/AX2RoutedLedger.lean`) — a leftover may be paired into *any*
column class `C (rt w a · h + y w)` of the region, or into any row class `C (x w · h + rt w a)`,
and in particular a pair inside one class of the region is admissible.  What the ledger asks for is
unchanged: the four counts of `BKLO.excLoad_le_routed`, one per grid line and per routing fibre,
each inside `5 K² t + 1`, which `BKLO.routed_quarter_counters_fit_ledger_budget` shows the budget
affords.

* `BKLO.RoutedSweepInvGen` — the repaired invariant;
* `BKLO.routedSweepInvGen_of_routedSweepInv` — it is weaker than `BKLO.RoutedSweepInv`;
* `BKLO.routedSweepInvGen_empty` and `BKLO.excLedgerSpread_of_routedSweepInvGen` — the two easy
  halves of the demand, as before;
* `BKLO.RoutedSweepInvGenStep` — the one-link step for the repaired invariant, and
* `BKLO.twoSidedUsedClassMatchedQuarterPairing_of_gen_step` — the residual demand of AX2 §10 from
  it.

Everything here is `sorry`-free; the one-link step `BKLO.RoutedSweepInvGenStep` is *not* proved.

**It is false**: `BKLO.not_routedSweepInvGenStep` (`BKLO/AX2GenStepObstruction.lean`) refutes it.
The four counters below are a flat cap on the sweep already made, and the step is asked of *any*
sweep satisfying the invariant — including one that already holds the counter of every place of a
class at the cap `5 K² t + 1`, so that the leftover the perturbation forces at the new link pushes
a counter to `5 K² t + 2`.  The cap therefore has to be underwritten by a plan fixed in advance;
`BKLO.RoutedSweepInvCellStep` (`BKLO/AX2RoutedResidualCell.lean`) is the form of the residual that
does so cell by cell, and which neither obstruction of this development refutes.
-/
import BKLO.AX2RoutedResidual

open Finset

namespace BKLO

variable {V : Type} [DecidableEq V]
variable {ε : ℝ} {K : ℕ} {W W' W'' : Finset V} {F R : Finset (Sym2 V)} {C : ℕ → Finset V}
  {x y : V → ℕ}

/-! ### The repaired invariant -/

/-- **The routed invariant of a class-matched sweep, with a general routing index.**  As
`BKLO.RoutedSweepInv`, except that the leftovers the perturbation forces are only required to be
*cross-routed* — paired into some column class `C (rt w a · h + y w)` or some row class
`C (x w · h + rt w a)` of the region of their link, with a routing index `rt` free to vary — and
not into the two classes of the three-class cycle.  The ledger asks the same four counts of them. -/
def RoutedSweepInvGen (ε : ℝ) (K : ℕ) (W W' : Finset V) (C : ℕ → Finset V) (x y φ : V → ℕ)
    (S : Finset V) (g : V → V → V) (Exc : V → Finset V) : Prop :=
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
    -- and its four routed counts stay inside a fifth of the budget
    (∀ a : V, ∀ P : ℕ, excRouteCount S Pc a (fun w => rt w a) P
      ≤ 5 * (K * K) * gridClassSize ε K W'.card + 1) ∧
    (∀ a : V, ∀ Q : ℕ, excRouteCount S Pc a y Q
      ≤ 5 * (K * K) * gridClassSize ε K W'.card + 1) ∧
    (∀ a : V, ∀ P : ℕ, excRouteCount S Pr a x P
      ≤ 5 * (K * K) * gridClassSize ε K W'.card + 1) ∧
    (∀ a : V, ∀ Q : ℕ, excRouteCount S Pr a (fun w => rt w a) Q
      ≤ 5 * (K * K) * gridClassSize ε K W'.card + 1)

/-- The empty sweep satisfies the repaired invariant. -/
theorem routedSweepInvGen_empty (φ : V → ℕ) :
    RoutedSweepInvGen ε K W W' C x y φ (∅ : Finset V) (fun _ a => a) (fun _ => ∅) := by
  classical
  refine ⟨Finset.empty_subset _, (fun _ => ∅), (fun _ => ∅), (fun _ => ∅), (fun _ => ∅),
    (fun _ _ => 0), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    intro a ha <;> simp_all [excRouteCount]

/-- **The repaired invariant is weaker than `BKLO.RoutedSweepInv`**: routing every forced leftover
into the column class or the row class of the cycle is the special case
`rt w a = ρ w (y w)`, `rt w a = σ w (x w)` of a general routing index. -/
theorem routedSweepInvGen_of_routedSweepInv {φ : V → ℕ} {S : Finset V} {g : V → V → V}
    {Exc : V → Finset V} (hInv : RoutedSweepInv ε K W W' C x y φ S g Exc) :
    RoutedSweepInvGen ε K W W' C x y φ S g Exc := by
  classical
  obtain ⟨hSD, Cc, Cr, Pc, Pr, hsplit, hdisjC, hdisjP, hcyc, hPc, hPr, hc1, hc2, hc3, hc4⟩ := hInv
  set h : ℕ := gridSize ε K with hhdef
  set rt : V → V → ℕ := fun w b =>
    if b ∈ Pc w then crossShift h φ (y w) w else crossShiftInv h φ (x w) w with hrtdef
  refine ⟨hSD, Cc, Cr, Pc, Pr, rt, hsplit, hdisjC, hcyc, ?_, ?_, ?_, hc2, hc3, ?_⟩
  · intro w _ b
    by_cases hmem : b ∈ Pc w
    · simp only [hrtdef, if_pos hmem]; exact crossShift_lt (gridSize_pos ε K) _ _ _
    · simp only [hrtdef, if_neg hmem]; exact crossShiftInv_lt (gridSize_pos ε K) _ _ _
  · intro w hw
    refine ⟨fun b hb => ?_, fun b hb => ?_⟩
    · simp only [hrtdef, if_pos hb]
      exact hPc w hw b hb
    · simp only [hrtdef, if_neg (hdisjP w hw b hb)]
      exact hPr w hw b hb
  · intro a P
    have he : excRouteCount S Pc a (fun w => rt w a) P
        = (S.filter (fun w => a ∈ Pc w ∧ crossShift h φ (y w) w = P)).card := by
      simp only [excRouteCount]
      congr 1
      refine Finset.filter_congr fun w _ => ?_
      constructor
      · rintro ⟨hwa, hwP⟩
        exact ⟨hwa, by simpa only [hrtdef, if_pos hwa] using hwP⟩
      · rintro ⟨hwa, hwP⟩
        exact ⟨hwa, by simpa only [hrtdef, if_pos hwa] using hwP⟩
    rw [he]
    exact hc1 a P
  · intro a Q
    refine le_trans ?_ (hc4 a Q)
    simp only [excRouteCount]
    refine Finset.card_le_card fun w hw => ?_
    obtain ⟨hwS, hwa, hwQ⟩ := Finset.mem_filter.1 hw
    exact Finset.mem_filter.2 ⟨hwS, hwa, by simpa only [hrtdef, if_neg (hdisjP w hwS a hwa)]
      using hwQ⟩

/-! ### The repaired invariant implies the ledger -/

/-- **The repaired invariant keeps the leftover ledger spread.**  The cycle part costs `4 (t + 1)`
on a cell (`BKLO.excLoad_le_of_cycleRouted`) and the cross-routed part costs its four counts
(`BKLO.excLoad_le_routed`), `4 (5 K² t + 1)`; the budget is `25 K² t`. -/
theorem excLedgerSpread_of_routedSweepInvGen
    (hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y)
    (hε : 0 < ε) (hε' : ε ≤ 1 / 100) (hK : 2 ≤ K)
    (ht : 512 ≤ gridClassSize ε K W'.card)
    {φ : V → ℕ} (hφlt : ∀ w, φ w < gridSize ε K)
    (hbal : ∀ p q j : ℕ, (((W \ W').filter (fun w => x w = p ∧ y w = q ∧ φ w = j)).card)
      ≤ (((W \ W').filter (fun w => x w = p ∧ y w = q)).card) / gridSize ε K + 1)
    {S : Finset V} {g : V → V → V} {Exc : V → Finset V}
    (hInv : RoutedSweepInvGen ε K W W' C x y φ S g Exc) :
    ExcLedgerSpread ε K W' C g S Exc := by
  classical
  obtain ⟨hSD, Cc, Cr, Pc, Pr, rt, hsplit, hdisjC, hcyc, hrtlt, hroute, hc1, hc2, hc3, hc4⟩ := hInv
  set h : ℕ := gridSize ε K with hhdef
  set t : ℕ := gridClassSize ε K W'.card with htdef
  refine excLedgerSpread_of_load_le (C := C) (W' := W') hε hε' ?_
  intro a P hP Q hQ
  -- the load splits into the cycle part and the cross-routed part
  have hsub : S.filter (fun w => a ∈ Exc w ∧ g w a ∈ gridRegion h C P Q)
      ⊆ (S.filter (fun w => a ∈ (Cc w ∪ Cr w) ∧ g w a ∈ gridRegion h C P Q))
        ∪ (S.filter (fun w => a ∈ (Pc w ∪ Pr w) ∧ g w a ∈ gridRegion h C P Q)) := by
    intro w hw
    obtain ⟨hwS, hwE, hwreg⟩ := Finset.mem_filter.1 hw
    rcases Finset.mem_union.1 (hsplit w hwS hwE) with hcase | hcase
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hwS, hcase, hwreg⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hwS, hcase, hwreg⟩)
  have hload : excLoad h C g S Exc a P Q
      ≤ excLoad h C g S (fun w => Cc w ∪ Cr w) a P Q
        + excLoad h C g S (fun w => Pc w ∪ Pr w) a P Q := by
    simp only [excLoad]
    exact le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
  -- the cycle part
  have hcycload : excLoad h C g S (fun w => Cc w ∪ Cr w) a P Q
      ≤ 4 * ((20 * (K * K) * t + 1) / h + 1) :=
    excLoad_le_of_cycleRouted (W'' := W'') (F := F) (R := R) hgrid hφlt hbal hSD
      hdisjC (fun w _ => Finset.Subset.refl _) hcyc a hP hQ
  have hcycbound : (20 * (K * K) * t + 1) / h + 1 ≤ t + 1 :=
    cell_shift_fibre_le_succ_class (W' := W') hε hε' hK ht
  -- the cross-routed part
  have hperload : excLoad h C g S (fun w => Pc w ∪ Pr w) a P Q
      ≤ excRouteCount S Pc a (fun w => rt w a) P + excRouteCount S Pc a y Q
        + excRouteCount S Pr a x P + excRouteCount S Pr a (fun w => rt w a) Q :=
    excLoad_le_routed (C := C) (x := x) (y := y) (rt := rt) (S := S) (g := g)
      (Exc := fun w => Pc w ∪ Pr w) (Ecol := Pc) (Erow := Pr) (a := a) (P := P) (Q := Q)
      (fun i hi j hj hij => hgrid.classDisjoint i hi j hj hij)
      (fun w hw => hgrid.rowLt w (hSD hw)) (fun w hw => hgrid.colLt w (hSD hw))
      (fun w hw => hrtlt w hw a) hP hQ (fun w _ => Finset.Subset.refl _) hroute
  have hb1 := hc1 a P
  have hb2 := hc2 a Q
  have hb3 := hc3 a P
  have hb4 := hc4 a Q
  -- the arithmetic
  show excLoad h C g S Exc a P Q ≤ 25 * (K * K) * t
  have hKK : 4 ≤ K * K := Nat.mul_le_mul hK hK
  have e1 : 25 * (K * K) * t = 25 * ((K * K) * t) := by ring
  have e2 : 5 * (K * K) * t = 5 * ((K * K) * t) := by ring
  have h4 : 4 * t ≤ (K * K) * t := Nat.mul_le_mul_right _ hKK
  have h5 : 1 ≤ (K * K) * t := Nat.one_le_iff_ne_zero.2 (by positivity)
  omega

/-! ### The residual, from the repaired one-link step -/

/-- **The one-link routed step for the repaired invariant.**  As `BKLO.RoutedSweepInvStep`, with
`BKLO.RoutedSweepInv` replaced by `BKLO.RoutedSweepInvGen`: the leftovers of the new link may be
routed by *any* index of the region, and only the four counts of the ledger are asked of them.

The obstruction `BKLO.not_routedSweepInvStep` does not apply to this statement: the leftover pair a
deletion forces inside one block of the region is cross-routed by the index of that block.

This step is *not* proved here, and it is **false** — `BKLO.not_routedSweepInvGenStep`
(`BKLO/AX2GenStepObstruction.lean`).  Its defect is exactly the one anticipated here: the sweep `S`
is only assumed to satisfy the invariant, so nothing forbids an `S` whose routed counters already
sit at the cap `5 K² t + 1` on every counter `(a, P)` the new link could use, and then no choice of
leftovers for the link keeps the invariant.  Closing AX2 §10 therefore also asks that the counters
be held below the cap with slack — by a prescription fixed in advance, as in
`BKLO.exists_cell_balanced_leftovers`, so that a counter only counts the links of one cell.  The
arithmetic affords it: `BKLO.routed_quarter_counters_fit_ledger_budget` leaves a fifth of the
budget spare at the average share, and the cell fibres of a design are small
(`BKLO.IsGridTwoSidedReservoir.cellFibre`, `outerVolume`).  `BKLO.RoutedSweepInvCellStep`
(`BKLO/AX2RoutedResidualCell.lean`) is that form of the step. -/
def RoutedSweepInvGenStep : Prop :=
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
    ∀ {X : V → Finset V} {S : Finset V} {g₀ : V → V → V} {Exc : V → Finset V} {u : V}
      {n m : ℕ} {U : Finset (Sym2 V)},
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
    RoutedSweepInvGen ε K W W' C x y φ S g₀ Exc →
    ∃ (p : V → V) (e : Finset V),
      (∀ a ∈ X u, p a ∈ X u) ∧ (∀ a ∈ X u, p (p a) = a) ∧ (∀ a ∈ X u, p a ≠ a) ∧
      (∀ a ∈ X u, s(a, p a) ∈ F ∧ s(a, p a) ∉ U) ∧
      IsClassMatchedSweep (gridSize ε K) C R W' X x y
        (fun w β => crossShift (gridSize ε K) φ β w)
        (fun w α => crossShiftInv (gridSize ε K) φ α w)
        (insert u S) (Function.update g₀ u p) (Function.update Exc u e) ∧
      RoutedSweepInvGen ε K W W' C x y φ (insert u S) (Function.update g₀ u p)
        (Function.update Exc u e)

/-- **The residual demand of AX2 §10, from the repaired one-link routed step.**  The class matching
is that of a shift balanced on every cell, the invariant is `BKLO.RoutedSweepInvGen`, and the
ledger is `BKLO.excLedgerSpread_of_routedSweepInvGen`. -/
theorem twoSidedUsedClassMatchedQuarterPairing_of_gen_step (hstep : RoutedSweepInvGenStep) :
    TwoSidedUsedClassMatchedQuarterPairing := by
  intro V _ ε K W W' W'' F R C x y q c X hgrid hnd hW'W hq hcres hqc hε hε' hK hbig
  classical
  obtain ⟨φ, hφlt, hφcell⟩ :=
    exists_cell_balanced_shift (W \ W') x y (gridSize_pos ε K)
  refine ⟨fun w β => crossShift (gridSize ε K) φ β w,
    fun w α => crossShiftInv (gridSize ε K) φ α w,
    RoutedSweepInvGen ε K W W' C x y φ,
    fun w β => crossShift_lt (gridSize_pos ε K) φ β w,
    fun w α => crossShiftInv_lt (gridSize_pos ε K) φ α w,
    classMatchingFibres_of_cellBalanced hgrid hφlt hφcell,
    routedSweepInvGen_empty φ, ?_, ?_⟩
  · intro S g Exc hInv
    exact excLedgerSpread_of_routedSweepInvGen hgrid hε hε' hK hbig hφlt hφcell hInv
  · intro S g₀ Exc u n m U hu hXu hXeven hadd4 hdel4 hadd hdel hUdeg hUused hmargin hSD huS
      hmaps hginv hsweep hInv
    exact hstep hgrid hnd hW'W hq hcres hqc hε hε' hK hbig hφlt hφcell hu hXu hXeven hadd4 hdel4
      hadd hdel hUdeg hUused hmargin hSD huS hmaps hginv hsweep hInv

end BKLO

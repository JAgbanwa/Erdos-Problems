/-
# The residual `BKLO.TwoSidedUsedClassMatchedQuarterPairing`, assembled from the routed sweep

This file assembles the residual demand of AX2 §10 out of

* the **class matching** of a shift balanced on every cell
  (`BKLO.exists_cell_balanced_shift`), whose fibres are small
  (`BKLO.classMatchingFibres_of_cellBalanced`) and which therefore does *not* fix the corner class
  of a link — the three-class cycle of `BKLO/AX2CyclePairing.lean` is what pays for that;
* the **routed invariant** `BKLO.RoutedSweepInv` (`BKLO/AX2RoutedSweepInvariant.lean`), which
  implies the leftover ledger `BKLO.ExcLedgerSpread`
  (`BKLO.excLedgerSpread_of_routedSweepInv`);
* the **one-link routed step** `BKLO.RoutedSweepInvStep`, which extends a routed sweep by one
  perturbed link.

`BKLO.twoSidedUsedClassMatchedQuarterPairing_of_step` is the assembly; it is `sorry`-free.

The one-link step itself, however, is **false**: `BKLO.not_routedSweepInvStep`
(`BKLO/AX2RoutedStepObstruction.lean`) refutes it.  `BKLO.RoutedSweepInv` routes every leftover of
a link into the column class `C (ρ w (y w) · h + y w)` or the row class `C (x w · h + σ w (x w))`
of the link, and by `BKLO.routedSweep_block_trace_eq` that forces the link to meet the two classes
of every other block of its region equally often — which a deletion of two places of one class
breaks, well inside the quarter-of-a-class perturbation the demand allows.  So the assembly below
is sound but its premise is not available: closing AX2 §10 needs an invariant carrying a *general*
routing index (`BKLO.IsCrossRoutedLeftover` with a free `rt`, `BKLO/AX2RoutedLedger.lean`) rather
than the two fixed classes of `BKLO.RoutedSweepInv`.
-/
import BKLO.AX2CyclePairing
import BKLO.AX2RoutedSweepInvariant
import BKLO.TwoSidedUsedClassMatchedQuarter

open Finset

namespace BKLO

variable {V : Type} [DecidableEq V]
variable {ε : ℝ} {K : ℕ} {W W' W'' : Finset V} {F R : Finset (Sym2 V)} {C : ℕ → Finset V}
  {x y : V → ℕ}

/-! ### The class matching of a cell-balanced shift -/

/-- **The class matching of a shift balanced on every cell has small fibres.**  This is
`BKLO.exists_classMatching_fibres` for a shift given in advance — the sweep needs to name the shift
itself, because the routed ledger of `BKLO.excLoad_le_of_cycleRouted` is a statement about the
*same* shift. -/
theorem classMatchingFibres_of_cellBalanced
    (hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y) {φ : V → ℕ}
    (hφlt : ∀ w, φ w < gridSize ε K)
    (hφcell : ∀ p q j : ℕ, (((W \ W').filter (fun w => x w = p ∧ y w = q ∧ φ w = j)).card)
      ≤ (((W \ W').filter (fun w => x w = p ∧ y w = q)).card) / gridSize ε K + 1) :
    ClassMatchingFibres ε K W W' x y
      (fun w β => crossShift (gridSize ε K) φ β w)
      (fun w α => crossShiftInv (gridSize ε K) φ α w) := by
  classical
  set h : ℕ := gridSize ε K with hhdef
  constructor
  · intro p β P
    show ((W \ W').filter (fun w => x w = p ∧ crossShift h φ β w = P)).card
      ≤ 20 * (K * K) * gridClassSize ε K W'.card + 1 + h
    rcases Finset.eq_empty_or_nonempty
      ((W \ W').filter (fun w => x w = p ∧ crossShift h φ β w = P)) with he | ⟨w₀, hw₀⟩
    · rw [he]; simp
    · obtain ⟨-, -, hw₀P⟩ := Finset.mem_filter.1 hw₀
      have hsub : (W \ W').filter (fun w => x w = p ∧ crossShift h φ β w = P)
          ⊆ (W \ W').filter (fun w => x w = p ∧ φ w = φ w₀) := by
        intro w hw
        obtain ⟨hwD, hwx, hwP⟩ := Finset.mem_filter.1 hw
        exact Finset.mem_filter.2 ⟨hwD, hwx,
          crossShift_inj (hφlt w) (hφlt w₀) (by rw [hwP, hw₀P])⟩
      exact le_trans (Finset.card_le_card hsub)
        (card_row_fibre_of_cell_balanced hgrid hφcell p (φ w₀))
  · intro q α Q
    show ((W \ W').filter (fun w => y w = q ∧ crossShiftInv h φ α w = Q)).card
      ≤ 20 * (K * K) * gridClassSize ε K W'.card + 1 + h
    rcases Finset.eq_empty_or_nonempty
      ((W \ W').filter (fun w => y w = q ∧ crossShiftInv h φ α w = Q)) with he | ⟨w₀, hw₀⟩
    · rw [he]; simp
    · obtain ⟨-, -, hw₀Q⟩ := Finset.mem_filter.1 hw₀
      have hsub : (W \ W').filter (fun w => y w = q ∧ crossShiftInv h φ α w = Q)
          ⊆ (W \ W').filter (fun w => y w = q ∧ φ w = φ w₀) := by
        intro w hw
        obtain ⟨hwD, hwy, hwQ⟩ := Finset.mem_filter.1 hw
        exact Finset.mem_filter.2 ⟨hwD, hwy,
          crossShiftInv_inj (hφlt w) (hφlt w₀) (by rw [hwQ, hw₀Q])⟩
      exact le_trans (Finset.card_le_card hsub)
        (card_col_fibre_of_cell_balanced hgrid hφcell q (φ w₀))

/-! ### The one-link routed step -/

/- **One perturbed link joins a routed class-matched sweep.**

This is the only remaining gap of the AX2 §10 residual in this development.  The link `X u` is the
reserved link of `u` perturbed by at most a quarter of a class in each direction; the sweep so far
follows the class matching of the cell-balanced shift `φ` and satisfies the routed invariant
`BKLO.RoutedSweepInv`.  The step asks for a fixed-point-free involution of `X u` by edges of `F`
outside the sweep's own forbidden set `U` which

* obeys the cross-side rule of `BKLO.IsClassMatchedSweep` outside a leftover set `e`, and
* keeps the routed invariant: the leftovers of `u` split into the leftovers of the three-class
  cycle of `u` (`BKLO.exists_classMatched_pairing_cycle_shift`) and the leftovers the perturbation
  forces, both routed into the column class `C (ρ u (y u) · h + y u)` or the row class
  `C (x u · h + σ u (x u))` of `u`, and the four routed counts of the forced part stay inside
  `5 K² t`.

**This statement is false**, and is kept here, commented out, for the record; see
`BKLO/AX2RoutedStepObstruction.lean`.  `BKLO.routedSweep_block_trace_eq` shows that a link of a
sweep satisfying `BKLO.RoutedSweepInv` has to meet the two classes of every block of its region in
the *same* number of places, and `BKLO.not_routedSweepInvStep` exhibits a design and a perturbation
obeying every hypothesis below at which they differ.  The defect is in the invariant, not in the
demand: `BKLO.RoutedSweepInv` routes every leftover into the column class `C (ρ w (y w) · h + y w)`
or the row class `C (x w · h + σ w (x w))` of the link, and the leftovers a deletion forces in
another block of the region cannot be routed there — their partners would have to be leftovers
routed back, and the two ends of such a pair lie in different classes.

-- theorem routedSweepInv_step
--     (hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y)
--     (hnd : ∀ e ∈ F, ¬ e.IsDiag) (hW'W : W' ⊆ W) {q c : ℕ}
--     (hq : ∀ i < gridSize ε K * gridSize ε K, (C i).card = q)
--     (hcres : ∀ v ∈ W \ W', ∀ i ∈ gridIdx (gridSize ε K) (x v) (y v),
--       (resLink R W' v ∩ C i).card = c)
--     (hqc : 3 * q ≤ 4 * c)
--     (hε : 0 < ε) (hε' : ε ≤ 1 / 100) (hK : 2 ≤ K)
--     (hbig : 512 ≤ gridClassSize ε K W'.card)
--     {φ : V → ℕ} (hφlt : ∀ w, φ w < gridSize ε K)
--     (hφcell : ∀ p q j : ℕ, (((W \ W').filter (fun w => x w = p ∧ y w = q ∧ φ w = j)).card)
--       ≤ (((W \ W').filter (fun w => x w = p ∧ y w = q)).card) / gridSize ε K + 1)
--     {X : V → Finset V} {S : Finset V} {g₀ : V → V → V} {Exc : V → Finset V} {u : V} {n m : ℕ}
--     {U : Finset (Sym2 V)}
--     (hu : u ∈ W \ W') (hXu : X u ⊆ W') (hXeven : Even (X u).card)
--     (hadd4 : 4 * (X u \ resLink R W' u).card ≤ gridClassSize ε K W'.card)
--     (hdel4 : 4 * (resLink R W' u \ X u).card ≤ gridClassSize ε K W'.card)
--     (hadd : (X u \ resLink R W' u).card ≤ n) (hdel : (resLink R W' u \ X u).card ≤ n)
--     (hUdeg : ∀ a ∈ X u, (resLink U (X u) a).card ≤ m)
--     (hUused : UsedForbidden X g₀ S W'' U)
--     (hmargin : 12 * n + 8 * m ≤ (2 * gridSize ε K - 1) * c)
--     (hSD : S ⊆ W \ W') (huS : u ∉ S)
--     (hmaps : ∀ w ∈ S, ∀ b ∈ X w, g₀ w b ∈ X w)
--     (hginv : ∀ w ∈ S, ∀ b ∈ X w, g₀ w (g₀ w b) = b)
--     (hsweep : IsClassMatchedSweep (gridSize ε K) C R W' X x y
--       (fun w β => crossShift (gridSize ε K) φ β w)
--       (fun w α => crossShiftInv (gridSize ε K) φ α w) S g₀ Exc)
--     (hInv : RoutedSweepInv ε K W W' C x y φ S g₀ Exc) :
--     ∃ (p : V → V) (e : Finset V),
--       (∀ a ∈ X u, p a ∈ X u) ∧ (∀ a ∈ X u, p (p a) = a) ∧ (∀ a ∈ X u, p a ≠ a) ∧
--       (∀ a ∈ X u, s(a, p a) ∈ F ∧ s(a, p a) ∉ U) ∧
--       IsClassMatchedSweep (gridSize ε K) C R W' X x y
--         (fun w β => crossShift (gridSize ε K) φ β w)
--         (fun w α => crossShiftInv (gridSize ε K) φ α w)
--         (insert u S) (Function.update g₀ u p) (Function.update Exc u e) ∧
--       RoutedSweepInv ε K W W' C x y φ (insert u S) (Function.update g₀ u p)
--         (Function.update Exc u e) := by
--   sorry
-/

/-- **The one-link routed step, as a proposition.**  This is exactly what
`BKLO.twoSidedUsedClassMatchedQuarterPairing_of_step` consumes: one perturbed link joins a routed
class-matched sweep, keeping the cross-side discipline of `BKLO.IsClassMatchedSweep` outside a
leftover set and keeping the routed invariant `BKLO.RoutedSweepInv`.

It is **false** — `BKLO.not_routedSweepInvStep` (`BKLO/AX2RoutedStepObstruction.lean`). -/
def RoutedSweepInvStep : Prop :=
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
    RoutedSweepInv ε K W W' C x y φ S g₀ Exc →
    ∃ (p : V → V) (e : Finset V),
      (∀ a ∈ X u, p a ∈ X u) ∧ (∀ a ∈ X u, p (p a) = a) ∧ (∀ a ∈ X u, p a ≠ a) ∧
      (∀ a ∈ X u, s(a, p a) ∈ F ∧ s(a, p a) ∉ U) ∧
      IsClassMatchedSweep (gridSize ε K) C R W' X x y
        (fun w β => crossShift (gridSize ε K) φ β w)
        (fun w α => crossShiftInv (gridSize ε K) φ α w)
        (insert u S) (Function.update g₀ u p) (Function.update Exc u e) ∧
      RoutedSweepInv ε K W W' C x y φ (insert u S) (Function.update g₀ u p)
        (Function.update Exc u e)

/-! ### The residual -/

/-- **The residual demand of AX2 §10, from the one-link routed step.**  The class matching is that
of a shift balanced on every cell, the invariant is `BKLO.RoutedSweepInv`, and the ledger is
`BKLO.excLedgerSpread_of_routedSweepInv`. -/
theorem twoSidedUsedClassMatchedQuarterPairing_of_step (hstep : RoutedSweepInvStep) :
    TwoSidedUsedClassMatchedQuarterPairing := by
  intro V _ ε K W W' W'' F R C x y q c X hgrid hnd hW'W hq hcres hqc hε hε' hK hbig
  classical
  obtain ⟨φ, hφlt, hφcell⟩ :=
    exists_cell_balanced_shift (W \ W') x y (gridSize_pos ε K)
  refine ⟨fun w β => crossShift (gridSize ε K) φ β w,
    fun w α => crossShiftInv (gridSize ε K) φ α w,
    RoutedSweepInv ε K W W' C x y φ,
    fun w β => crossShift_lt (gridSize_pos ε K) φ β w,
    fun w α => crossShiftInv_lt (gridSize_pos ε K) φ α w,
    classMatchingFibres_of_cellBalanced hgrid hφlt hφcell,
    routedSweepInv_empty φ, ?_, ?_⟩
  · intro S g Exc hInv
    exact excLedgerSpread_of_routedSweepInv hgrid hε hε' hK hbig hφlt hφcell hInv
  · intro S g₀ Exc u n m U hu hXu hXeven hadd4 hdel4 hadd hdel hUdeg hUused hmargin hSD huS
      hmaps hginv hsweep hInv
    exact hstep hgrid hnd hW'W hq hcres hqc hε hε' hK hbig hφlt hφcell hu hXu hXeven hadd4 hdel4
      hadd hdel hUdeg hUused hmargin hSD huS hmaps hginv hsweep hInv

end BKLO

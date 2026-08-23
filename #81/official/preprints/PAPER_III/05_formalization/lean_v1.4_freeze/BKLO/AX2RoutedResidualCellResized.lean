/-
# The routed residual of AX2 §10 against a cell-balanced plan, at the **re-sized** reservoir

`BKLO.not_routedSweepInvCellStep` (`BKLO/AX2CellStepObstruction.lean`) refutes the one-link routed
step of `BKLO/AX2RoutedResidualCell.lean` by a *capacity* count: at the old sizing a link may be
asked to plan `t / 4` leftovers of one class, a cell may carry `(20 K² - 10) t` links all asking it
of the same class, and a class holds only `3 t / 4` places of capacity `5 K² t + 1` each, so

  `(20 K² - 10) t · (t / 4) > (3 t / 4) · (5 K² t + 1)`  for every `K ≥ 2`.

`BKLO/AX2CellStepRepair.lean` prescribes the re-sizing that removes exactly this: a perturbation
scale of `t / 32` in place of `t / 4`.  This file restates the one-link step at the re-sized
reservoir and verifies that the count now goes the other way, with a factor of more than two to
spare (`BKLO.cell_plan_capacity_ge_demand_resized`):

  `(20 K²) t · (t / 32) ≤ (3 t / 4) · (5 K² t)`  for every `K` and `t`.

* `BKLO.RoutedSweepInvCellStepResized` — the one-link routed step at the re-sized reservoir;
* `BKLO.twoSidedUsedClassMatchedResizedPairing_of_cell_step_resized` — the re-sized residual demand
  of AX2 §10 from it;
* `BKLO.cell_plan_capacity_ge_demand_resized` — the capacity count of
  `BKLO.not_routedSweepInvCellStep`, at the re-sized perturbation scale.

Everything here is `sorry`-free; the one-link step is *not* proved.
-/
import BKLO.AX2RoutedResidualCell
import BKLO.TwoSidedUsedClassMatchedResized

open Finset

namespace BKLO

/-! ### The capacity count of the refutation, at the re-sized scale -/

/-- **The capacity obstruction of `BKLO.not_routedSweepInvCellStep` disappears under the
re-sizing.**  At the old sizing a link of a cell may be forced to plan `t / 4` places of one class,
and the demand `(20 K² - 10) t · (t / 4)` of a full cell exceeds the capacity
`(3 t / 4) · (5 K² t + 1)` of the class.  At the re-sized perturbation scale a link plans at most
`t / 32` places, and the demand of a full cell — here bounded generously by the whole cell,
`20 K² t` links — is at most *half* the capacity. -/
theorem cell_plan_capacity_ge_demand_resized (K t d : ℕ) (hd : 32 * d ≤ t) :
    (20 * (K * K) * t) * d ≤ (3 * t / 4) * (5 * (K * K) * t) := by
  have hd' : 20 * d ≤ 5 * (3 * t / 4) := by omega
  calc (20 * (K * K) * t) * d = (K * K * t) * (20 * d) := by ring
    _ ≤ (K * K * t) * (5 * (3 * t / 4)) := Nat.mul_le_mul_left _ hd'
    _ = (3 * t / 4) * (5 * (K * K) * t) := by ring

/-! ### The one-link routed step at the re-sized reservoir -/

/-- **The one-link routed step against a cell-balanced plan, at the re-sized reservoir.**  This is
`BKLO.RoutedSweepInvCellStep` with the two re-sizings of `BKLO/AX2CellStepRepair.lean`: the design
is eighth-balanced (so the equalized trace satisfies `7 q ≤ 8 c`) and the perturbation of a link is
at most a thirty-second of a class on each side.  Those are exactly the hypotheses of
`BKLO.exists_cell_balanced_leftovers_of_resized`, so the cell prescription that
`BKLO.cell_quarter_condition_fails_of_quarter_equalized` denies at the old sizing is available
here. -/
def RoutedSweepInvCellStepResized : Prop :=
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
    ∃ L : V → Finset V, CellSpreadLeftoverPlan ε K W W' x y L ∧
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

/-- **The re-sized residual demand of AX2 §10, from the re-sized one-link routed step against a
cell-balanced plan.** -/
theorem twoSidedUsedClassMatchedResizedPairing_of_cell_step_resized
    (hstep : RoutedSweepInvCellStepResized) : TwoSidedUsedClassMatchedResizedPairing := by
  intro V _ ε K W W' W'' F R C x y q c X hgrid8 hnd hW'W hq hcres hqc8 hε hε' hK hbig
  classical
  set hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y :=
    hgrid8.toIsGridTwoSidedReservoir with hgriddef
  obtain ⟨φ, hφlt, hφcell⟩ :=
    exists_cell_balanced_shift (W \ W') x y (gridSize_pos ε K)
  obtain ⟨L, hL, hstep'⟩ :=
    hstep hgrid8 hnd hW'W hq hcres hqc8 hε hε' hK hbig hφlt hφcell (X := X)
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
  · intro S g₀ Exc u n m U hu hXu hXeven hadd32 hdel32 hadd hdel hUdeg hUused hmargin hSD huS
      hmaps hginv hsweep hInv
    exact hstep' hu hXu hXeven hadd32 hdel32 hadd hdel hUdeg hUused hmargin hSD huS hmaps hginv
      hsweep hInv

/-- **Main theorem (AX2 half of Erdős #81), from the three classical inputs and the re-sized
one-link routed step against a cell-balanced plan.** -/
theorem triangle_decomposition_of_inputs_and_cell_step_resized
    (hDross : FracTriangleThreshold) (hNib : FracToApproxMaxDeg) (hDirac : PerfectMatchingDirac)
    (hstep : RoutedSweepInvCellStepResized) :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        n₀ ≤ Fintype.card V →
        (3 ∣ G.edgeFinset.card ∧ ∀ v, Even (G.degree v)) →
        (9 / 10 + ε) * (Fintype.card V : ℝ) ≤ (G.minDegree : ℝ) →
        TriangleDecomposable G :=
  triangle_decomposition_of_inputs_and_twoSidedUsedClassMatchedResized hDross hNib hDirac
    (twoSidedUsedClassMatchedResizedPairing_of_cell_step_resized hstep)

end BKLO

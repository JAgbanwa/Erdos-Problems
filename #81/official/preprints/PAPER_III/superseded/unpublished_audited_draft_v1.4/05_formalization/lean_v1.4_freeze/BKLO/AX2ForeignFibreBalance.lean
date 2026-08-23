/-
# The foreign family, fibre-balanced over the classes

`BKLO/AX2ForeignCapacityAudit.lean` isolates the one term of
`BKLO.partnerClassSpread_of_spreadPlans` that the perturbation scale cannot fix: the **foreign**
term.  The routed families are paid by `BKLO.FibreBalanced`, which divides a global plan load by
the number of indices; the class-matched and cycle families are paid by cell-shift fibres; the
foreign family is paid by the *whole* global load `BM` of the foreign plan, because
`BKLO.IsCountClassification` constrains `Fo` only by `Fo w ⊆ M w`.  That forces `BM ≤ mc` and makes
the pool the forcing needs unaffordable, by a factor `K - 1 ≥ 799`, at every perturbation scale.

This file carries out the repair the audit's §4 describes, and re-threads the chain against it.
The foreign family gets a **class index** `ft` and the same fibre-balance clause the routed
families have, now over the `h²` classes of the design:

* `BKLO.ForeignIndexed` — the partner of a foreign leftover lies in the class `ft w a` names;
* `BKLO.FibreBalanced (h * h) S M Fo ft` — no class carries more than the average, up to one, of
  the links at which the foreign plan claims the place;
* `BKLO.foreignClassLoad_le_of_foreignFibreBalanced` — the foreign term of the partner-class ledger
  is then `BM` where the plan's global load is `BM · h²`, instead of the global load itself;
* `BKLO.RoutedSweepInvCellCountForeignBalanced` — the invariant with the two extra clauses;
* `BKLO.partnerClassSpread_of_spreadPlansForeignBalanced` — the assembled spread, with the foreign
  term paid the same way as the routed ones;
* `BKLO.RoutedSweepInvCellCountForeignBalancedWide6hStepScaledComplete` — the one-link step at the
  finer perturbation scale of `BKLO/AX2ScaledPerturbation.lean` for the repaired invariant;
* `BKLO.twoSidedUsedClassMatchedResized6hPairingScaledComplete_of_foreignBalancedStep`,
  `BKLO.triangle_decomposition_of_inputs_and_cell_step_countWideForeignBalanced` — the chain to the
  AX2 half of the main theorem, at the unchanged density budget `(9/10 + ε) n ≤ δ(G)`.

The re-threading is free: the invariant of the demand
`BKLO.TwoSidedUsedClassMatchedResized6hPairingScaledComplete` is existentially quantified, and the
repaired invariant implies the old one
(`BKLO.routedSweepInvCellCountBalanced_of_foreignBalanced`), so it pays exactly the same ledger.

With the repair the capacity inequality of the audit is met at the design sizes with room to spare
(`BKLO.foreign_capacity_with_fibre_balanced_term_witness`).  What remains open is the construction
of the step itself.

Everything here is `sorry`-free.
-/
import BKLO.AX2ForeignCapacityAudit

open Finset

namespace BKLO

variable {V : Type} [DecidableEq V]
variable {ε : ℝ} {K : ℕ} {W W' W'' : Finset V} {F R : Finset (Sym2 V)} {C : ℕ → Finset V}
  {x y : V → ℕ} {L M : V → Finset V}

/-! ### The foreign class index -/

/-- **The foreign leftovers carry a class index.**  If the partner of a foreign leftover lies in a
class of the design, `ft` names that class.  This is the structure the other four families of
`BKLO.IsCountClassification` already have and the foreign one lacks. -/
def ForeignIndexed (h : ℕ) (C : ℕ → Finset V) (S : Finset V) (g : V → V → V)
    (Fo : V → Finset V) (ft : V → V → ℕ) : Prop :=
  ∀ w ∈ S, ∀ a ∈ Fo w, ∀ i < h * h, g w a ∈ C i → ft w a = i

omit [DecidableEq V] in
/-- The empty sweep is foreign-indexed. -/
theorem foreignIndexed_empty (h : ℕ) (C : ℕ → Finset V) (g : V → V → V) (Fo : V → Finset V)
    (ft : V → V → ℕ) : ForeignIndexed h C (∅ : Finset V) g Fo ft := by
  intro w hw
  exact absurd hw (Finset.notMem_empty w)

/-- **The foreign part of the partner-class load is a fibre of the foreign index.** -/
theorem foreignClassLoad_le_excRouteCount {h : ℕ} {C : ℕ → Finset V} {S : Finset V}
    {g : V → V → V} {Fo : V → Finset V} {ft : V → V → ℕ}
    (hft : ForeignIndexed h C S g Fo ft) (a : V) {i : ℕ} (hi : i < h * h) :
    foreignClassLoad C S g Fo a i ≤ excRouteCount S Fo a (fun w => ft w a) i := by
  classical
  refine Finset.card_le_card fun w hw => ?_
  obtain ⟨hwS, hwFo, hwC⟩ : w ∈ S ∧ a ∈ Fo w ∧ g w a ∈ C i := by
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hw
    exact ⟨h1, h2.1, h2.2⟩
  exact Finset.mem_filter.2 ⟨hwS, hwFo, hft w hwS a hwFo i hi hwC⟩

/-- **The foreign term of the partner-class ledger, paid the way the routed ones are.**  A foreign
plan whose global per-place load is `BM · h²` contributes only `BM` to the partner-class load of a
place in any one class, once the foreign family is fibre-balanced over the classes. -/
theorem foreignClassLoad_le_of_foreignFibreBalanced {h BM : ℕ} {C : ℕ → Finset V} {S : Finset V}
    {g : V → V → V} {M Fo : V → Finset V} {ft : V → V → ℕ} (hh : 0 < h)
    (hft : ForeignIndexed h C S g Fo ft) (hbal : FibreBalanced (h * h) S M Fo ft)
    {a : V} (hload : (S.filter (fun w => a ∈ M w)).card ≤ BM * (h * h))
    {i : ℕ} (hi : i < h * h) :
    foreignClassLoad C S g Fo a i ≤ BM :=
  le_trans (foreignClassLoad_le_excRouteCount hft a hi)
    (excRouteCount_le_of_fibreBalanced (Nat.mul_pos hh hh) hbal hload i)

/-! ### The repaired invariant -/

/-- **The counted routed invariant with balanced fibres and a fibre-balanced foreign family.**
`BKLO.RoutedSweepInvCellCountBalanced` with the two clauses the audit asks for. -/
def RoutedSweepInvCellCountForeignBalanced (ε : ℝ) (K : ℕ) (W W' : Finset V) (C : ℕ → Finset V)
    (x y φ : V → ℕ) (L M : V → Finset V) (S : Finset V) (g : V → V → V) (Exc : V → Finset V) :
    Prop :=
  S ⊆ W \ W' ∧
  ∃ (Cc Cr Pc Pr Fo Po : V → Finset V) (rt ft : V → V → ℕ),
    IsCountClassificationBalanced ε K W' C x y φ L M S g Exc Cc Cr Pc Pr Fo Po rt ∧
    ForeignIndexed (gridSize ε K) C S g Fo ft ∧
    FibreBalanced (gridSize ε K * gridSize ε K) S M Fo ft

/-- The repaired invariant is a strengthening of the balanced one. -/
theorem routedSweepInvCellCountBalanced_of_foreignBalanced {φ : V → ℕ} {S : Finset V}
    {g : V → V → V} {Exc : V → Finset V}
    (hInv : RoutedSweepInvCellCountForeignBalanced ε K W W' C x y φ L M S g Exc) :
    RoutedSweepInvCellCountBalanced ε K W W' C x y φ L M S g Exc := by
  obtain ⟨hSD, Cc, Cr, Pc, Pr, Fo, Po, rt, ft, hcls, -, -⟩ := hInv
  exact ⟨hSD, Cc, Cr, Pc, Pr, Fo, Po, rt, hcls⟩

/-- The empty sweep satisfies the repaired invariant. -/
theorem routedSweepInvCellCountForeignBalanced_empty (φ : V → ℕ) (L M : V → Finset V) :
    RoutedSweepInvCellCountForeignBalanced ε K W W' C x y φ L M (∅ : Finset V) (fun _ a => a)
      (fun _ => ∅) := by
  classical
  obtain ⟨hSD, Cc, Cr, Pc, Pr, Fo, Po, rt, hcls⟩ :=
    routedSweepInvCellCountBalanced_empty (ε := ε) (K := K) (W := W) (W' := W') (C := C)
      (x := x) (y := y) φ L M
  exact ⟨hSD, Cc, Cr, Pc, Pr, Fo, Po, rt, fun _ _ => 0, hcls,
    foreignIndexed_empty _ _ _ _ _, fibreBalanced_empty _ _ _ _⟩

/-- **The repaired invariant pays the same ledger.** -/
theorem excLedgerSpread_of_routedSweepInvCellCountForeignBalancedWide
    (hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y)
    (hε : 0 < ε) (hε' : ε ≤ 1 / 100) (hK : 2 ≤ K)
    (ht : 512 ≤ gridClassSize ε K W'.card)
    {φ : V → ℕ} (hφlt : ∀ w, φ w < gridSize ε K)
    (hbal : ∀ p q j : ℕ, (((W \ W').filter (fun w => x w = p ∧ y w = q ∧ φ w = j)).card)
      ≤ (((W \ W').filter (fun w => x w = p ∧ y w = q)).card) / gridSize ε K + 1)
    (hL : CellSpreadLeftoverPlan ε K W W' x y L) (hM : ForeignSpreadLeftoverPlanWide ε K W W' M)
    {S : Finset V} {g : V → V → V} {Exc : V → Finset V}
    (hInv : RoutedSweepInvCellCountForeignBalanced ε K W W' C x y φ L M S g Exc) :
    ExcLedgerSpread ε K W' C g S Exc :=
  excLedgerSpread_of_routedSweepInvCellCountBalancedWide (W'' := W'') (F := F) (R := R) hgrid hε
    hε' hK ht hφlt hbal hL hM (routedSweepInvCellCountBalanced_of_foreignBalanced hInv)

/-! ### The partner-class spread of the repaired invariant -/

/-- **The partner-class spread with the foreign term fibre-balanced.**
`BKLO.partnerClassSpread_of_spreadPlans` with the foreign plan allowed a global per-place load of
`BM · h²` in place of `BM`: the class index of the foreign family divides it by the number of
classes, exactly as `BKLO.FibreBalanced` divides the cell plan's load by the number of routing
indices.  This is what makes the pool of `BKLO/AX2ForeignCapacityAudit.lean` affordable. -/
theorem partnerClassSpread_of_spreadPlansForeignBalanced
    (hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y)
    {φ : V → ℕ} (hφlt : ∀ w, φ w < gridSize ε K)
    (hφcell : ∀ p q j : ℕ, (((W \ W').filter (fun w => x w = p ∧ y w = q ∧ φ w = j)).card)
      ≤ (((W \ W').filter (fun w => x w = p ∧ y w = q)).card) / gridSize ε K + 1)
    {X : V → Finset V} {S : Finset V} {g : V → V → V} {Exc : V → Finset V}
    {Cc Cr Pc Pr Fo Po : V → Finset V} {rt ft : V → V → ℕ} (hSD : S ⊆ W \ W')
    (hcls : IsCountClassificationBalanced ε K W' C x y φ L M S g Exc Cc Cr Pc Pr Fo Po rt)
    (hft : ForeignIndexed (gridSize ε K) C S g Fo ft)
    (hfbal : FibreBalanced (gridSize ε K * gridSize ε K) S M Fo ft)
    (hsweep : IsClassMatchedSweep (gridSize ε K) C R W' X x y
      (fun w β => crossShift (gridSize ε K) φ β w)
      (fun w α => crossShiftInv (gridSize ε K) φ α w) S g Exc)
    {BL BM N : ℕ}
    (hLload : PlanGlobalLoad W W' L (BL * gridSize ε K))
    (hMload : PlanGlobalLoad W W' M (BM * (gridSize ε K * gridSize ε K)))
    {a : V}
    (hmult : (((W \ W').filter (fun w => a ∈ X w ∧ a ∉ resLink R W' w)).card) ≤ N)
    {i : ℕ} (hi : i < gridSize ε K * gridSize ε K) :
    partnerClassLoad C X S g a i
      ≤ N + 4 * ((20 * (K * K) * gridClassSize ε K W'.card + 1) / gridSize ε K + 1)
        + 2 * BL + BM := by
  classical
  set h : ℕ := gridSize ε K with hhdef
  have hhpos : 0 < h := gridSize_pos ε K
  have hbalC := hcls.2.1
  have hbalR := hcls.2.2
  have hsplit := partnerClassLoad_le_split hgrid hSD hcls.1 X a hi
  have h1 : prescribedClassLoad C X S g Exc a i
      ≤ N + 2 * ((20 * (K * K) * gridClassSize ε K W'.card + 1) / h + 1) :=
    prescribedClassLoad_le_cellShift hgrid hφlt hφcell hSD hsweep hmult hi
  have h2 : cycleClassLoad C S g Cc Cr a i
      ≤ 2 * ((20 * (K * K) * gridClassSize ε K W'.card + 1) / h + 1) :=
    cycleClassLoad_le_cellShift hgrid hφlt hφcell hSD (hcls.1.2.2.1) a hi
  have hload : (S.filter (fun w => a ∈ L w)).card ≤ BL * h :=
    planLoad_on_sweep hSD hLload a
  have h3 : excRouteCount S Pc a (fun w => rt w a) (i / h) ≤ BL :=
    excRouteCount_le_of_fibreBalanced hhpos hbalC hload _
  have h4 : excRouteCount S Pr a (fun w => rt w a) (i % h) ≤ BL :=
    excRouteCount_le_of_fibreBalanced hhpos hbalR hload _
  have h5 : foreignClassLoad C S g Fo a i ≤ BM :=
    foreignClassLoad_le_of_foreignFibreBalanced hhpos hft hfbal
      (planLoad_on_sweep hSD hMload a) hi
  obtain ⟨B, hBdef⟩ : ∃ B : ℕ,
      (20 * (K * K) * gridClassSize ε K W'.card + 1) / h + 1 = B := ⟨_, rfl⟩
  rw [hBdef] at h1 h2 ⊢
  rw [← hhdef] at hsplit
  omega

/-! ### The one-link step for the repaired invariant, at the finer perturbation scale -/

/-- **The one-link routed step of the repaired invariant.**
`BKLO.RoutedSweepInvCellCountBalancedWide6hStepScaledComplete` with
`BKLO.RoutedSweepInvCellCountBalanced` replaced by
`BKLO.RoutedSweepInvCellCountForeignBalanced`, at the finer perturbation scale
`8192 K² d ≤ t`. -/
def RoutedSweepInvCellCountForeignBalancedWide6hStepScaledComplete : Prop :=
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
      8192 * (K * K) * (X u \ resLink R W' u).card ≤ gridClassSize ε K W'.card →
      8192 * (K * K) * (resLink R W' u \ X u).card ≤ gridClassSize ε K W'.card →
      (X u \ resLink R W' u).card ≤ n → (resLink R W' u \ X u).card ≤ n →
      (∀ a ∈ X u, (resLink U (X u) a).card ≤ m) →
      UsedForbidden X g₀ S W'' U →
      12 * n + 8 * m ≤ (2 * gridSize ε K - 1) * c →
      S ⊆ W \ W' → u ∉ S →
      (∀ w ∈ S, X w ⊆ W') →
      (∀ w ∈ S, Even (X w).card) →
      (∀ w ∈ S, ∀ a ∈ X w, s(w, a) ∈ F) →
      (∀ w ∈ S, 8192 * (K * K) * (X w \ resLink R W' w).card ≤ gridClassSize ε K W'.card) →
      (∀ w ∈ S, 8192 * (K * K) * (resLink R W' w \ X w).card ≤ gridClassSize ε K W'.card) →
      (∀ a ∈ W', 8192 * (K * K) * (((W \ W').filter (fun w => a ∈ X w \ resLink R W' w)).card)
        ≤ gridClassSize ε K W'.card) →
      (∀ w ∈ S, ∀ b ∈ X w, g₀ w b ∈ X w) → (∀ w ∈ S, ∀ b ∈ X w, g₀ w (g₀ w b) = b) →
      (∀ w ∈ S, ∀ b ∈ X w, g₀ w b ≠ b) →
      (∀ w ∈ S, ∀ b ∈ X w, s(b, g₀ w b) ∈ F) →
      IsClassMatchedSweep (gridSize ε K) C R W' X x y
        (fun w β => crossShift (gridSize ε K) φ β w)
        (fun w α => crossShiftInv (gridSize ε K) φ α w) S g₀ Exc →
      RoutedSweepInvCellCountForeignBalanced ε K W W' C x y φ L M S g₀ Exc →
      ∃ (p : V → V) (e : Finset V),
        (∀ a ∈ X u, p a ∈ X u) ∧ (∀ a ∈ X u, p (p a) = a) ∧ (∀ a ∈ X u, p a ≠ a) ∧
        (∀ a ∈ X u, s(a, p a) ∈ F ∧ s(a, p a) ∉ U) ∧
        IsClassMatchedSweep (gridSize ε K) C R W' X x y
          (fun w β => crossShift (gridSize ε K) φ β w)
          (fun w α => crossShiftInv (gridSize ε K) φ α w)
          (insert u S) (Function.update g₀ u p) (Function.update Exc u e) ∧
        RoutedSweepInvCellCountForeignBalanced ε K W W' C x y φ L M (insert u S)
          (Function.update g₀ u p) (Function.update Exc u e)

/-! ### The chain, re-threaded through the repaired invariant -/

/-- **The demand of `BKLO/AX2ScaledCompleteStep.lean` from the repaired step.**  The invariant of
the demand is existentially quantified, so the repaired invariant may be used in its place: it is
initialised by `BKLO.routedSweepInvCellCountForeignBalanced_empty` and pays the same ledger by
`BKLO.excLedgerSpread_of_routedSweepInvCellCountForeignBalancedWide`. -/
theorem twoSidedUsedClassMatchedResized6hPairingScaledComplete_of_foreignBalancedStep
    (hstep : RoutedSweepInvCellCountForeignBalancedWide6hStepScaledComplete) :
    TwoSidedUsedClassMatchedResized6hPairingScaledComplete := by
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
    RoutedSweepInvCellCountForeignBalanced ε K W W' C x y φ L M,
    fun w β => crossShift_lt (gridSize_pos ε K) φ β w,
    fun w α => crossShiftInv_lt (gridSize_pos ε K) φ α w,
    classMatchingFibres_of_cellBalanced hgrid hφlt hφcell,
    routedSweepInvCellCountForeignBalanced_empty φ L M, ?_, ?_⟩
  · intro S g Exc hInv
    exact excLedgerSpread_of_routedSweepInvCellCountForeignBalancedWide (W'' := W'') (F := F)
      (R := R) hgrid hε hε' hK ht512 hφlt hφcell hL hM hInv
  · intro S g₀ Exc u n m U hu hXu hXeven hadd hdel hadd' hdel' hUdeg hUused hmargin hSD huS
      hSW' hSeven hSF hSadd hSdel hSmult hmaps hginv hne hFleg hsweep hInv
    exact hstep' hu hXu hXeven hadd hdel hadd' hdel' hUdeg hUused hmargin hSD huS hSW' hSeven
      hSF hSadd hSdel hSmult hmaps hginv hne hFleg hsweep hInv

/-- **Main theorem (AX2 half of Erdős #81), from the three classical inputs and the one-link step
of the repaired invariant** at the finer perturbation scale.  The density budget is unchanged:
`(9/10 + ε) n ≤ δ(G)`. -/
theorem triangle_decomposition_of_inputs_and_cell_step_countWideForeignBalanced
    (hDross : FracTriangleThreshold) (hNib : FracToApproxMaxDeg) (hDirac : PerfectMatchingDirac)
    (hstep : RoutedSweepInvCellCountForeignBalancedWide6hStepScaledComplete) :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        n₀ ≤ Fintype.card V →
        (3 ∣ G.edgeFinset.card ∧ ∀ v, Even (G.degree v)) →
        (9 / 10 + ε) * (Fintype.card V : ℝ) ≤ (G.minDegree : ℝ) →
        TriangleDecomposable G :=
  triangle_decomposition_of_inputs_and_gridPairingTwoSidedScaled hDross hNib hDirac
    (gridPairingResidualTwoSidedScaled_of_usedClassMatchedResized6hScaledComplete
      (twoSidedUsedClassMatchedResized6hPairingScaledComplete_of_foreignBalancedStep hstep))

end BKLO

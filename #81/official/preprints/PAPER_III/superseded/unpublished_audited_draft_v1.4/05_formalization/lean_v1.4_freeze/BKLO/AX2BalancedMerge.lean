/-
# The counted routed invariant with the balanced-fibre clause

`BKLO/AX2FibreBalance.lean` isolates the clause the counted invariant is missing:
`BKLO.FibreBalanced` — no routing index of a place carries more than the average, up to one, of the
links at which the plan claims that place.  This file *installs* that clause in the invariant and
re-runs the whole chain of `BKLO/AX2CountedMerge.lean` against the strengthened vehicle:

* `BKLO.IsCountClassificationBalanced` — the classification of `BKLO.IsCountClassification` with
  the two balanced-fibre clauses, one per side.  As everywhere in this development the witnesses
  are **named**, never re-existentialised: a statement about the merge is a statement about a fixed
  classification.
* `BKLO.RoutedSweepInvCellCountBalanced` — the invariant carried by such a classification;
  `BKLO.routedSweepInvCellCount_of_balanced` shows it is a strengthening of
  `BKLO.RoutedSweepInvCellCount`, and `BKLO.routedSweepInvCellCountBalanced_empty` starts the
  induction (`BKLO.fibreBalanced_empty`).
* `BKLO.excLedgerSpread_of_routedSweepInvCellCountBalancedWide` — the strengthened invariant pays
  the same ledger: the ledger argument uses only clauses the counted invariant already has.
* `BKLO.RoutedSweepInvCellCountBalancedWide6hStep` — the one-link step of the *balanced* counted
  invariant, against a cell-balanced plan and the wide foreign plan, at the reservoir re-sized to
  `6 h ≤ t`;
* `BKLO.twoSidedUsedClassMatchedResized6hPairing_of_cell_step_countBalanced`,
  `BKLO.triangle_decomposition_of_inputs_and_cell_step_countBalanced` — and the chain to the AX2
  half of the main theorem, intact.

Under the balanced clause every routing index of every planned place is usable
(`BKLO.excRouteCount_le_of_fibreBalanced`), and the clause is maintained at no cost by routing at a
least-loaded index (`BKLO.exists_least_loaded_index`,
`BKLO.fibreBalanced_insert_of_least_loaded`); `BKLO.balancedIndexSupply_of_countBalanced` records
the resulting index supply at the new link in the form the merge uses.

Everything here is `sorry`-free.  The one-link step
`BKLO.RoutedSweepInvCellCountBalancedWide6hStep` itself is *not* proved here; what remains between
it and the chain is audited in `BKLO/AX2BalancedMergeObstruction.lean`.
-/
import BKLO.AX2CountedMerge
import BKLO.AX2FibreBalance

open Finset

namespace BKLO

variable {V : Type} [DecidableEq V]
variable {ε : ℝ} {K : ℕ} {W W' W'' : Finset V} {F R : Finset (Sym2 V)} {C : ℕ → Finset V}
  {x y : V → ℕ} {L M : V → Finset V}

/-! ### The classification with balanced fibres -/

/-- **The counted classification with the balanced-fibre clause.**  `BKLO.IsCountClassification`
together with `BKLO.FibreBalanced` on each of the two cross-routed families: no routing index of a
place carries more than the average of the plan's claim on that place, up to one. -/
def IsCountClassificationBalanced (ε : ℝ) (K : ℕ) (W' : Finset V) (C : ℕ → Finset V)
    (x y φ : V → ℕ) (L M : V → Finset V) (S : Finset V) (g : V → V → V) (Exc : V → Finset V)
    (Cc Cr Pc Pr Fo Po : V → Finset V) (rt : V → V → ℕ) : Prop :=
  IsCountClassification ε K W' C x y φ L M S g Exc Cc Cr Pc Pr Fo Po rt ∧
  FibreBalanced (gridSize ε K) S L Pc rt ∧
  FibreBalanced (gridSize ε K) S L Pr rt

/-- **The counted routed invariant with balanced fibres.** -/
def RoutedSweepInvCellCountBalanced (ε : ℝ) (K : ℕ) (W W' : Finset V) (C : ℕ → Finset V)
    (x y φ : V → ℕ) (L M : V → Finset V) (S : Finset V) (g : V → V → V) (Exc : V → Finset V) :
    Prop :=
  S ⊆ W \ W' ∧
  ∃ (Cc Cr Pc Pr Fo Po : V → Finset V) (rt : V → V → ℕ),
    IsCountClassificationBalanced ε K W' C x y φ L M S g Exc Cc Cr Pc Pr Fo Po rt

/-- A balanced counted sweep is carried by a fixed balanced classification. -/
theorem isCountClassificationBalanced_of_inv {φ : V → ℕ} {S : Finset V} {g : V → V → V}
    {Exc : V → Finset V}
    (hInv : RoutedSweepInvCellCountBalanced ε K W W' C x y φ L M S g Exc) :
    S ⊆ W \ W' ∧ ∃ Cc Cr Pc Pr Fo Po rt,
      IsCountClassificationBalanced ε K W' C x y φ L M S g Exc Cc Cr Pc Pr Fo Po rt := hInv

/-- Conversely, a balanced classification witnesses the balanced invariant. -/
theorem routedSweepInvCellCountBalanced_of_classification {φ : V → ℕ} {S : Finset V}
    {g : V → V → V} {Exc : V → Finset V} {Cc Cr Pc Pr Fo Po : V → Finset V} {rt : V → V → ℕ}
    (hSD : S ⊆ W \ W')
    (hcls : IsCountClassificationBalanced ε K W' C x y φ L M S g Exc Cc Cr Pc Pr Fo Po rt) :
    RoutedSweepInvCellCountBalanced ε K W W' C x y φ L M S g Exc :=
  ⟨hSD, Cc, Cr, Pc, Pr, Fo, Po, rt, hcls⟩

/-- **The balanced invariant is a strengthening of the counted one.**  Everything the chain of
`BKLO/AX2CountedMerge.lean` asks of the invariant is already there. -/
theorem routedSweepInvCellCount_of_balanced {φ : V → ℕ} {S : Finset V} {g : V → V → V}
    {Exc : V → Finset V}
    (hInv : RoutedSweepInvCellCountBalanced ε K W W' C x y φ L M S g Exc) :
    RoutedSweepInvCellCount ε K W W' C x y φ L M S g Exc := by
  obtain ⟨hSD, Cc, Cr, Pc, Pr, Fo, Po, rt, hcls, -, -⟩ := hInv
  exact ⟨hSD, Cc, Cr, Pc, Pr, Fo, Po, rt, hcls⟩

/-- The empty sweep satisfies the balanced counted invariant: `BKLO.fibreBalanced_empty`. -/
theorem routedSweepInvCellCountBalanced_empty (φ : V → ℕ) (L M : V → Finset V) :
    RoutedSweepInvCellCountBalanced ε K W W' C x y φ L M (∅ : Finset V) (fun _ a => a)
      (fun _ => ∅) := by
  classical
  obtain ⟨hSD, Cc, Cr, Pc, Pr, Fo, Po, rt, hcls⟩ :=
    isCountClassification_of_inv (routedSweepInvCellCount_empty (ε := ε) (K := K) (W := W)
      (W' := W') (C := C) (x := x) (y := y) φ L M)
  exact ⟨hSD, Cc, Cr, Pc, Pr, Fo, Po, rt, hcls,
    fibreBalanced_empty _ _ _ _, fibreBalanced_empty _ _ _ _⟩

/-! ### The ledger, unchanged -/

/-- **The balanced counted invariant keeps the leftover ledger spread against a wide foreign
plan.**  The ledger argument of `BKLO.excLedgerSpread_of_routedSweepInvCellCountWide` uses only
clauses the counted invariant already has, so the strengthened invariant pays the same ledger. -/
theorem excLedgerSpread_of_routedSweepInvCellCountBalancedWide
    (hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y)
    (hε : 0 < ε) (hε' : ε ≤ 1 / 100) (hK : 2 ≤ K)
    (ht : 512 ≤ gridClassSize ε K W'.card)
    {φ : V → ℕ} (hφlt : ∀ w, φ w < gridSize ε K)
    (hbal : ∀ p q j : ℕ, (((W \ W').filter (fun w => x w = p ∧ y w = q ∧ φ w = j)).card)
      ≤ (((W \ W').filter (fun w => x w = p ∧ y w = q)).card) / gridSize ε K + 1)
    (hL : CellSpreadLeftoverPlan ε K W W' x y L) (hM : ForeignSpreadLeftoverPlanWide ε K W W' M)
    {S : Finset V} {g : V → V → V} {Exc : V → Finset V}
    (hInv : RoutedSweepInvCellCountBalanced ε K W W' C x y φ L M S g Exc) :
    ExcLedgerSpread ε K W' C g S Exc :=
  excLedgerSpread_of_routedSweepInvCellCountWide (W'' := W'') (F := F) (R := R) hgrid hε hε' hK ht
    hφlt hbal hL hM (routedSweepInvCellCount_of_balanced hInv)

/-! ### What the balanced clause buys at the new link -/

/-- **Under the balanced clause every index of every planned place is free at the new link.**
This is the statement `BKLO.free_routing_index_available_of_countInv` cannot give: there, *one*
index per place is all the counted clause guarantees
(`BKLO.exists_free_routing_index_sharp`), and `BKLO.pool_blocking_affordable` shows a history can
own all the others.  Here the hypothesis is that the plan's claim on the place is at most
`(5 K² t + 1) h` — which `BKLO.planned_row_line_card_lt` and `BKLO.planned_col_line_card_lt` prove
for a place the plan offers the new link. -/
theorem balancedIndexSupply_of_countBalanced
    {φ : V → ℕ} {S : Finset V} {g : V → V → V} {Exc : V → Finset V}
    {Cc Cr Pc Pr Fo Po : V → Finset V} {rt : V → V → ℕ}
    (hcls : IsCountClassificationBalanced ε K W' C x y φ L M S g Exc Cc Cr Pc Pr Fo Po rt)
    {a : V}
    (hload : (S.filter (fun w => a ∈ L w)).card
      ≤ (5 * (K * K) * gridClassSize ε K W'.card) * gridSize ε K) :
    (∀ P : ℕ, excRouteCount S Pc a (fun w => rt w a) P
        ≤ 5 * (K * K) * gridClassSize ε K W'.card) ∧
      (∀ Q : ℕ, excRouteCount S Pr a (fun w => rt w a) Q
        ≤ 5 * (K * K) * gridClassSize ε K W'.card) :=
  ⟨fun P => excRouteCount_le_of_fibreBalanced (gridSize_pos ε K) hcls.2.1 hload P,
    fun Q => excRouteCount_le_of_fibreBalanced (gridSize_pos ε K) hcls.2.2 hload Q⟩

/-! ### The one-link step of the balanced invariant, and the chain to the main theorem -/

/-- **The one-link routed step of the *balanced* counted invariant** against a cell-balanced plan
and the wide foreign plan, at the reservoir re-sized to `6 h ≤ t`.  This is
`BKLO.RoutedSweepInvCellCountWide6hStep` with `BKLO.RoutedSweepInvCellCount` replaced by
`BKLO.RoutedSweepInvCellCountBalanced`: the merge may *assume* the balanced-fibre clause of the
history — under which every routing index of every planned place is free — and must *re-establish*
it at the new link, which `BKLO.fibreBalanced_insert_of_least_loaded` does as soon as the new
link routes each of its planned leftovers at a least-loaded index. -/
def RoutedSweepInvCellCountBalancedWide6hStep : Prop :=
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
      RoutedSweepInvCellCountBalanced ε K W W' C x y φ L M S g₀ Exc →
      ∃ (p : V → V) (e : Finset V),
        (∀ a ∈ X u, p a ∈ X u) ∧ (∀ a ∈ X u, p (p a) = a) ∧ (∀ a ∈ X u, p a ≠ a) ∧
        (∀ a ∈ X u, s(a, p a) ∈ F ∧ s(a, p a) ∉ U) ∧
        IsClassMatchedSweep (gridSize ε K) C R W' X x y
          (fun w β => crossShift (gridSize ε K) φ β w)
          (fun w α => crossShiftInv (gridSize ε K) φ α w)
          (insert u S) (Function.update g₀ u p) (Function.update Exc u e) ∧
        RoutedSweepInvCellCountBalanced ε K W W' C x y φ L M (insert u S)
          (Function.update g₀ u p) (Function.update Exc u e)

/-- **The re-sized `6 h ≤ t` residual demand of AX2 §10, from the balanced one-link step.** -/
theorem twoSidedUsedClassMatchedResized6hPairing_of_cell_step_countBalanced
    (hstep : RoutedSweepInvCellCountBalancedWide6hStep) :
    TwoSidedUsedClassMatchedResized6hPairing := by
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
    RoutedSweepInvCellCountBalanced ε K W W' C x y φ L M,
    fun w β => crossShift_lt (gridSize_pos ε K) φ β w,
    fun w α => crossShiftInv_lt (gridSize_pos ε K) φ α w,
    classMatchingFibres_of_cellBalanced hgrid hφlt hφcell,
    routedSweepInvCellCountBalanced_empty φ L M, ?_, ?_⟩
  · intro S g Exc hInv
    exact excLedgerSpread_of_routedSweepInvCellCountBalancedWide (W'' := W'') (F := F) (R := R)
      hgrid hε hε' hK ht512 hφlt hφcell hL hM hInv
  · intro S g₀ Exc u n m U hu hXu hXeven hadd32 hdel32 hadd hdel hUdeg hUused hmargin hSD huS
      hmaps hginv hsweep hInv
    exact hstep' hu hXu hXeven hadd32 hdel32 hadd hdel hUdeg hUused hmargin hSD huS hmaps hginv
      hsweep hInv

/-- **Main theorem (AX2 half of Erdős #81), from the three classical inputs and the balanced
one-link counted step.** -/
theorem triangle_decomposition_of_inputs_and_cell_step_countBalanced
    (hDross : FracTriangleThreshold) (hNib : FracToApproxMaxDeg) (hDirac : PerfectMatchingDirac)
    (hstep : RoutedSweepInvCellCountBalancedWide6hStep) :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        n₀ ≤ Fintype.card V →
        (3 ∣ G.edgeFinset.card ∧ ∀ v, Even (G.degree v)) →
        (9 / 10 + ε) * (Fintype.card V : ℝ) ≤ (G.minDegree : ℝ) →
        TriangleDecomposable G :=
  triangle_decomposition_of_inputs_and_twoSidedUsedClassMatchedResized6h hDross hNib hDirac
    (twoSidedUsedClassMatchedResized6hPairing_of_cell_step_countBalanced hstep)

end BKLO

/-
# The partner-class spread of a balanced counted sweep, from a spread plan

`BKLO/AX2PartnerClassLedger.lean` splits the partner-class load of a place into five terms;
`BKLO/AX2PrescribedClassFibre.lean` caps the two terms the invariant does not touch by cell-shift
fibres of the design.  This file caps the remaining three and assembles the clause
`BKLO.PartnerClassSpread` — the hypothesis every pairing engine of the development wants and which
`BKLO/AX2BalancedMergeObstruction.lean` reported missing.

The three remaining terms are paid by the *plans*, and this is where the repair pays off:

* the two routed terms are paid by `BKLO.FibreBalanced` — a plan claiming a place at `B · h` links
  routes it at most `B` times at each index (`BKLO.excRouteCount_le_of_fibreBalanced`) — so a plan
  whose **global** per-place load is `B · h` is enough;
* the foreign term is paid by the global per-place load of the foreign plan directly.

`BKLO.PlanGlobalLoad` is that hypothesis, and `BKLO.partnerClassSpread_of_spreadPlans` is the
assembly.  `BKLO.classDegree_le_of_spreadPlans` is the form the engines take: a class-level degree
bound at the presented link, on the perturbed link system itself.

The obstruction file's §3 argues that no class-level degree bound is derivable from a *cell*
ceiling of `5 K² t + 1`; that argument is about the cell ceiling, which is a worst-case ceiling.
What is used here is the global load of the plan that the merge actually builds, together with
`BKLO.FibreBalanced`, which divides it by `h`.

Everything here is `sorry`-free.
-/
import BKLO.AX2PrescribedClassFibre

open Finset

namespace BKLO

variable {V : Type} [DecidableEq V]
variable {ε : ℝ} {K : ℕ} {W W' W'' : Finset V} {F R : Finset (Sym2 V)} {C : ℕ → Finset V}
  {x y : V → ℕ} {L M : V → Finset V}

/-! ### The global load of a plan -/

/-- **The global per-place load of a plan**: no place is claimed by the plan at more than `B`
links of the whole design.  `BKLO.CellSpreadLeftoverPlan` is the *per cell* ceiling the invariant
uses; this is the global one, which is what `BKLO.FibreBalanced` converts into a per-index cap. -/
def PlanGlobalLoad (W W' : Finset V) (L : V → Finset V) (B : ℕ) : Prop :=
  ∀ a : V, (((W \ W').filter (fun w => a ∈ L w)).card) ≤ B

/-- A global load bound restricts to a sweep. -/
theorem planLoad_on_sweep {B : ℕ} {S : Finset V} (hSD : S ⊆ W \ W')
    (hL : PlanGlobalLoad W W' L B) (a : V) :
    (S.filter (fun w => a ∈ L w)).card ≤ B := by
  classical
  refine le_trans (Finset.card_le_card ?_) (hL a)
  intro w hw
  obtain ⟨hwS, hwL⟩ := Finset.mem_filter.1 hw
  exact Finset.mem_filter.2 ⟨hSD hwS, hwL⟩

/-! ### The foreign term -/

/-- **The foreign part of the partner-class load is bounded by the load of the foreign plan.**
A foreign leftover of a link is a place the plan claims there. -/
theorem foreignClassLoad_le_planLoad {S : Finset V} {g : V → V → V} {Fo : V → Finset V}
    (hFoM : ∀ w ∈ S, Fo w ⊆ M w) (a : V) (i : ℕ) :
    foreignClassLoad C S g Fo a i ≤ (S.filter (fun w => a ∈ M w)).card := by
  classical
  refine Finset.card_le_card fun w hw => ?_
  obtain ⟨hwS, hwFo, -⟩ : w ∈ S ∧ a ∈ Fo w ∧ g w a ∈ C i := by
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hw
    exact ⟨h1, h2.1, h2.2⟩
  exact Finset.mem_filter.2 ⟨hwS, hFoM w hwS hwFo⟩

/-! ### The assembly -/

/-- **The partner-class spread of a balanced counted sweep against spread plans.**  Every link at
which a place is paired into a fixed class is a class-matched link, a cycle leftover, a routed
leftover at the index the class forces, or a foreign leftover
(`BKLO.partnerClassLoad_le_split`).  The first two are cell-shift fibres of the design
(`BKLO.prescribedClassLoad_le_cellShift`, `BKLO.cycleClassLoad_le_cellShift`) plus the links at
which the place lies outside its reserved link, which the sweep-wide perturbation multiplicity
bounds; the two routed terms are the global load of the cell plan divided by `h`
(`BKLO.excRouteCount_le_of_fibreBalanced`); the last is the global load of the foreign plan. -/
theorem partnerClassSpread_of_spreadPlans
    (hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y)
    {φ : V → ℕ} (hφlt : ∀ w, φ w < gridSize ε K)
    (hφcell : ∀ p q j : ℕ, (((W \ W').filter (fun w => x w = p ∧ y w = q ∧ φ w = j)).card)
      ≤ (((W \ W').filter (fun w => x w = p ∧ y w = q)).card) / gridSize ε K + 1)
    {X : V → Finset V} {S : Finset V} {g : V → V → V} {Exc : V → Finset V}
    {Cc Cr Pc Pr Fo Po : V → Finset V} {rt : V → V → ℕ} (hSD : S ⊆ W \ W')
    (hcls : IsCountClassificationBalanced ε K W' C x y φ L M S g Exc Cc Cr Pc Pr Fo Po rt)
    (hsweep : IsClassMatchedSweep (gridSize ε K) C R W' X x y
      (fun w β => crossShift (gridSize ε K) φ β w)
      (fun w α => crossShiftInv (gridSize ε K) φ α w) S g Exc)
    {BL BM N : ℕ}
    (hLload : PlanGlobalLoad W W' L (BL * gridSize ε K))
    (hMload : PlanGlobalLoad W W' M BM)
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
  obtain ⟨-, -, hcyc, -, -, -, -, -, -, -, -, hFoM, -⟩ := hcls.1
  have hsplit := partnerClassLoad_le_split hgrid hSD hcls.1 X a hi
  have h1 : prescribedClassLoad C X S g Exc a i
      ≤ N + 2 * ((20 * (K * K) * gridClassSize ε K W'.card + 1) / h + 1) :=
    prescribedClassLoad_le_cellShift hgrid hφlt hφcell hSD hsweep hmult hi
  have h2 : cycleClassLoad C S g Cc Cr a i
      ≤ 2 * ((20 * (K * K) * gridClassSize ε K W'.card + 1) / h + 1) :=
    cycleClassLoad_le_cellShift hgrid hφlt hφcell hSD hcyc a hi
  have hload : (S.filter (fun w => a ∈ L w)).card ≤ BL * h :=
    planLoad_on_sweep hSD hLload a
  have h3 : excRouteCount S Pc a (fun w => rt w a) (i / h) ≤ BL :=
    excRouteCount_le_of_fibreBalanced hhpos hbalC hload _
  have h4 : excRouteCount S Pr a (fun w => rt w a) (i % h) ≤ BL :=
    excRouteCount_le_of_fibreBalanced hhpos hbalR hload _
  have h5 : foreignClassLoad C S g Fo a i ≤ BM :=
    le_trans (foreignClassLoad_le_planLoad hFoM a i) (planLoad_on_sweep hSD hMload a)
  obtain ⟨B, hBdef⟩ : ∃ B : ℕ,
      (20 * (K * K) * gridClassSize ε K W'.card + 1) / h + 1 = B := ⟨_, rfl⟩
  rw [hBdef] at h1 h2 ⊢
  rw [← hhdef] at hsplit
  omega

/-- **The class-level degree of the forbidden set at the presented link.**  This is the hypothesis
every pairing engine of the development takes, on the perturbed link system itself: under the
partner-class spread of `BKLO.partnerClassSpread_of_spreadPlans` the forbidden set denies a place
of the link only `mc` places of any one class. -/
theorem classDegree_le_of_partnerClassLoad
    (hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y)
    {X : V → Finset V} {S : Finset V} {g : V → V → V} {U : Finset (Sym2 V)} {mc : ℕ}
    (hmaps : ∀ w ∈ S, ∀ b ∈ X w, g w b ∈ X w)
    (hginv : ∀ w ∈ S, ∀ b ∈ X w, g w (g w b) = b)
    (hUused : UsedForbidden X g S W'' U)
    {a : V} (haW'' : a ∉ W'')
    (hspread : ∀ k < gridSize ε K * gridSize ε K, partnerClassLoad C X S g a k ≤ mc)
    {k : ℕ} (hk : k < gridSize ε K * gridSize ε K) (T : Finset V) :
    (((C k ∩ T)).filter (fun b => s(a, b) ∈ U)).card ≤ mc := by
  classical
  have hsub : ((C k ∩ T)).filter (fun b => s(a, b) ∈ U)
      ⊆ ((C k ∩ T)).filter (fun b => s(a, b) ∈ usedPairs X g S) := by
    intro b hb
    obtain ⟨hbCT, hbU⟩ := Finset.mem_filter.1 hb
    rcases hUused a b hbU with h1 | h1 | h1
    · exact Finset.mem_filter.2 ⟨hbCT, h1⟩
    · exact absurd h1 haW''
    · exact absurd (Finset.mem_inter.1 hbCT).1
        (Finset.disjoint_right.1 (hgrid.classAvoid k hk) h1)
  calc (((C k ∩ T)).filter (fun b => s(a, b) ∈ U)).card
      ≤ (((C k ∩ T)).filter (fun b => s(a, b) ∈ usedPairs X g S)).card :=
        Finset.card_le_card hsub
    _ ≤ partnerClassLoad C X S g a k := card_used_class_le_partnerClassLoad hmaps hginv a k T
    _ ≤ mc := hspread k hk

end BKLO

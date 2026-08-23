import Mathlib.Data.Fintype.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Algebra.Monoid

/-!
# Finite fractional-cover layer (reused, verified)

Generic compact-polytope layer for a finite family of finite covering constraints,
giving an attained minimum `tauStar`.  This is the project's previously machine-checked
`FiniteCover` scaffold (sorry-free under Lean/Mathlib v4.28.0), reproduced here so Paper II
is self-contained.  The triangle specialization (`PaperII.Model`) instantiates:

* `ι` = edge coordinates;
* `κ` = triangles;
* `A.support T` = the three edge coordinates of triangle `T`.

Faithfulness to ledger D2: D2's cover is `z ≥ 0` (no upper bound).  The `[0,1]` box used here
is without loss (capping a coordinate above `1` to `1` keeps every unit-RHS cover constraint and
does not increase cost), and every Paper II step (notably L1) keeps weights in `[0,1]`.
-/

open scoped BigOperators
open Set

namespace PaperII

section FiniteCover

variable {ι κ : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype κ] [DecidableEq κ]

/-- A finite nonempty family of coordinates attached to each constraint. -/
structure CoverSystem (ι κ : Type*) [Fintype ι] [DecidableEq ι] where
  support : κ → Finset ι
  support_nonempty : ∀ k, (support k).Nonempty

variable (A : CoverSystem ι κ)

/-- Coordinatewise box constraint `0 ≤ x_i ≤ 1`. -/
def InUnitBox (x : ι → ℝ) : Prop :=
  ∀ i, 0 ≤ x i ∧ x i ≤ 1

/-- Every covering constraint receives total weight at least one. -/
def SatisfiesCover (x : ι → ℝ) : Prop :=
  ∀ k, 1 ≤ ∑ i ∈ A.support k, x i

/-- Feasible fractional covers. -/
def FeasibleCover : Set (ι → ℝ) :=
  {x | InUnitBox x ∧ SatisfiesCover A x}

/-- Linear objective. -/
def coverCost (x : ι → ℝ) : ℝ :=
  ∑ i, x i

/-- The all-one vector. -/
def oneCover : ι → ℝ := fun _ => 1

omit [Fintype κ] [DecidableEq κ] in
theorem oneCover_mem : oneCover ∈ FeasibleCover A := by
  constructor
  · intro i
    constructor <;> simp [oneCover]
  · intro k
    rw [show (∑ i ∈ A.support k, oneCover i : ℝ) = (A.support k).card by
      simp [oneCover]]
    exact_mod_cast (A.support_nonempty k).card_pos

omit [Fintype κ] [DecidableEq κ] in
theorem feasibleCover_isClosed : IsClosed (FeasibleCover A) := by
  have e : FeasibleCover A =
      (⋂ i, {x : ι → ℝ | 0 ≤ x i}) ∩ (⋂ i, {x : ι → ℝ | x i ≤ 1}) ∩
        (⋂ k, {x : ι → ℝ | 1 ≤ ∑ j ∈ A.support k, x j}) := by
    ext x
    simp only [FeasibleCover, InUnitBox, SatisfiesCover, Set.mem_setOf_eq,
      Set.mem_inter_iff, Set.mem_iInter, forall_and]
  rw [e]
  refine ((isClosed_iInter fun i => ?_).inter (isClosed_iInter fun i => ?_)).inter
    (isClosed_iInter fun k => ?_)
  · exact isClosed_le continuous_const (continuous_apply i)
  · exact isClosed_le (continuous_apply i) continuous_const
  · exact isClosed_le continuous_const
      (continuous_finset_sum _ (fun j _ => continuous_apply j))

theorem feasibleCover_isCompact : IsCompact (FeasibleCover A) := by
  have hbox : IsCompact (Set.univ.pi (fun _ : ι => Set.Icc (0:ℝ) 1)) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  apply hbox.of_isClosed_subset (feasibleCover_isClosed A)
  intro x hx i _
  exact Set.mem_Icc.mpr ⟨(hx.1 i).1, (hx.1 i).2⟩

/-- Existence of an optimal fractional cover. -/
theorem exists_minimizer :
    ∃ x ∈ FeasibleCover A, ∀ y ∈ FeasibleCover A, coverCost x ≤ coverCost y := by
  have hne : (FeasibleCover A).Nonempty := ⟨oneCover, oneCover_mem A⟩
  have hcont : Continuous (coverCost : (ι → ℝ) → ℝ) := by
    unfold coverCost
    fun_prop
  exact (feasibleCover_isCompact A).exists_isMinOn hne hcont.continuousOn

/-- Chosen optimal cover. -/
noncomputable def optimalCover : ι → ℝ :=
  Classical.choose (exists_minimizer A)

/-- The minimum fractional-cover value. -/
noncomputable def tauStar : ℝ :=
  coverCost (optimalCover A)

theorem optimalCover_mem : optimalCover A ∈ FeasibleCover A :=
  (Classical.choose_spec (exists_minimizer A)).1

theorem tauStar_le_cost {x : ι → ℝ} (hx : x ∈ FeasibleCover A) :
    tauStar A ≤ coverCost x := by
  exact (Classical.choose_spec (exists_minimizer A)).2 x hx

theorem tauStar_nonneg : 0 ≤ tauStar A := by
  rw [tauStar]
  exact Finset.sum_nonneg fun i _ => (optimalCover_mem A).1 i |>.1

theorem tauStar_le_card : tauStar A ≤ Fintype.card ι :
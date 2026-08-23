/-
  Paper I — parametric-stability (Lipschitz) export, §3.1(C) of the revision doc.

  The residual-cover value `M(κ) = min_{z ∈ P} ⟨1−κ, z⟩` is the minimum of a linear
  objective over a *fixed* polytope `P ⊆ [0,1]^ι`. Such a value is 1-Lipschitz in the
  objective vector (ℓ¹): perturbing the baseline/profile by `Δ` moves the fractional
  value by at most `‖Δ‖₁`. This is the transfer interface the revision proposes.

  Stated abstractly (graph-agnostic), so it is reusable for robust versions of Paper II
  and for split / near-split perturbations. Incremental: does NOT touch the frozen
  Paper I artifact.
-/
import Mathlib

open scoped BigOperators

namespace Contrib

variable {ι : Type*} [Fintype ι]

/-- LP value: minimum of the linear objective `⟨c, ·⟩` over a fixed feasible set `P`. -/
noncomputable def lpVal (P : Set (ι → ℝ)) (c : ι → ℝ) : ℝ :=
  sInf ((fun z => ∑ i, c i * z i) '' P)

/-- The objective-value set is bounded below when `P ⊆ [0,1]^ι`. -/
lemma bddBelow_obj (P : Set (ι → ℝ)) (hbdd : ∀ z ∈ P, ∀ i, 0 ≤ z i ∧ z i ≤ 1)
    (c : ι → ℝ) : BddBelow ((fun z => ∑ i, c i * z i) '' P) := by
  refine ⟨∑ i, min (c i) 0, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  refine Finset.sum_le_sum (fun i _ => ?_)
  rcases le_total 0 (c i) with hci | hci
  · rw [min_eq_right hci]; exact mul_nonneg hci (hbdd z hz i).1
  · rw [min_eq_left hci]
    calc c i = c i * 1 := (mul_one _).symm
      _ ≤ c i * z i := mul_le_mul_of_nonpos_left (hbdd z hz i).2 hci

/-- **Parametric stability (Lipschitz).** `M` is 1-Lipschitz in the objective (ℓ¹):
`|lpVal P c − lpVal P c'| ≤ ∑ i |c i − c' i|`, for a fixed feasible set `P ⊆ [0,1]^ι`. -/
theorem lpVal_lipschitz (P : Set (ι → ℝ)) (hP : P.Nonempty)
    (hbdd : ∀ z ∈ P, ∀ i, 0 ≤ z i ∧ z i ≤ 1) (c c' : ι → ℝ) :
    |lpVal P c - lpVal P c'| ≤ ∑ i, |c i - c' i| := by
  set K := ∑ i, |c i - c' i| with hK
  -- per-point bound: |⟨c,z⟩ − ⟨c',z⟩| ≤ K for every feasible z
  have hpt : ∀ z ∈ P, |(∑ i, c i * z i) - (∑ i, c' i * z i)| ≤ K := by
    intro z hz
    rw [← Finset.sum_sub_distrib]
    calc |∑ i, (c i * z i - c' i * z i)|
        ≤ ∑ i, |c i * z i - c' i * z i| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i, |c i - c' i| * z i := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [← sub_mul, abs_mul, abs_of_nonneg (hbdd z hz i).1]
      _ ≤ ∑ i, |c i - c' i| := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          calc |c i - c' i| * z i ≤ |c i - c' i| * 1 :=
                mul_le_mul_of_nonneg_left (hbdd z hz i).2 (abs_nonneg _)
            _ = |c i - c' i| := mul_one _
  have hne' : ∀ d : ι → ℝ, ((fun z => ∑ i, d i * z i) '' P).Nonempty := fun d => hP.image _
  -- one-directional Lipschitz bound
  have key : ∀ d d' : ι → ℝ, (∀ z ∈ P, (∑ i, d i * z i) - (∑ i, d' i * z i) ≤ K) →
      lpVal P d - K ≤ lpVal P d' := by
    intro d d' hbnd
    have hbd := bddBelow_obj P hbdd d
    refine le_csInf (hne' d') ?_
    rintro b ⟨z, hz, rfl⟩
    have ha : lpVal P d ≤ ∑ i, d i * z i := csInf_le hbd ⟨z, hz, rfl⟩
    have hb := hbnd z hz
    linarith
  have h1 : lpVal P c - K ≤ lpVal P c' :=
    key c c' (fun z hz => le_of_abs_le (hpt z hz))
  have h2 : lpVal P c' - K ≤ lpVal P c :=
    key c' c (fun z hz => le_of_abs_le (by rw [abs_sub_comm]; exact hpt z hz))
  rw [abs_sub_le_iff]
  exact ⟨by linarith, by linarith⟩

/-- **Affine profile reduction (concavity of the LP value).** Over a fixed feasible set
`P ⊆ [0,1]^ι`, the value `lpVal P` is concave in the objective: a convex combination of
objectives has value at least the convex combination of the values. Paper I §3.1(A). -/
theorem lpVal_concave (P : Set (ι → ℝ)) (hP : P.Nonempty)
    (hbdd : ∀ z ∈ P, ∀ i, 0 ≤ z i ∧ z i ≤ 1)
    {σ : Type*} [Fintype σ] (lam : σ → ℝ) (cs : σ → ι → ℝ) (hlam : ∀ s, 0 ≤ lam s) :
    (∑ s, lam s * lpVal P (cs s)) ≤ lpVal P (fun i => ∑ s, lam s * cs s i) := by
  refine le_csInf (hP.image _) ?_
  rintro b ⟨z, hz, rfl⟩
  show ∑ s, lam s * lpVal P (cs s) ≤ ∑ i, (∑ s, lam s * cs s i) * z i
  have hswap : (∑ i, (∑ s, lam s * cs s i) * z i)
      = ∑ s, lam s * (∑ i, cs s i * z i) := by
    simp_rw [Finset.sum_mul, Finset.mul_sum, mul_assoc]
    exact Finset.sum_comm
  rw [hswap]
  refine Finset.sum_le_sum (fun s _ => ?_)
  exact mul_le_mul_of_nonneg_left
    (csInf_le (bddBelow_obj P hbdd (cs s)) ⟨z, hz, rfl⟩) (hlam s)

/-- The mixed value is at least the smallest pure value (immediate from `lpVal_concave`
when `∑ lam = 1`). -/
theorem lpVal_ge_min (P : Set (ι → ℝ)) (hP : P.Nonempty)
    (hbdd : ∀ z ∈ P, ∀ i, 0 ≤ z i ∧ z i ≤ 1)
    {σ : Type*} [Fintype σ] [Nonempty σ] (lam : σ → ℝ) (cs : σ → ι → ℝ)
    (hlam : ∀ s, 0 ≤ lam s) (hsum : ∑ s, lam s = 1) :
    (⨅ s, lpVal P (cs s)) ≤ lpVal P (fun i => ∑ s, lam s * cs s i) := by
  refine le_trans ?_ (lpVal_concave P hP hbdd lam cs hlam)
  have hmin : ∀ s, (⨅ s', lpVal P (cs s')) ≤ lpVal P (cs s) :=
    fun s => ciInf_le (Set.finite_range _).bddBelow s
  have key : (⨅ s', lpVal P (cs s')) * (∑ s, lam s) ≤ ∑ s, lam s * lpVal P (cs s) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun s _ => ?_)
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (hmin s) (hlam s)
  rwa [hsum, mul_one] at key

end Contrib

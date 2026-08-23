/-
Copyright (c) 2026. Released under Apache 2.0 license.
Draft candidate for Mathlib — extracted from the Erdős-#81 Paper I formalization.
Submission-track (PR) version; see `INTEGRATION_PLAN.md`.

# Finite Farkas lemma and finite LP strong duality

Built on `fg_cone_isClosed` (Weyl, in `FgConeClosed.lean`) and Mathlib's convex-cone
hyperplane separation:
* `Contrib.Submission.farkas_ge` — finite Farkas lemma (inequality form).
* `Contrib.Submission.covering_packing_duality` — finite LP strong duality
  (covering/packing form): the maximum packing value equals the covering optimum and is
  attained.

These stay over `EuclideanSpace ℝ ι` (a finite-dimensional real inner-product space),
the natural setting for the `ProperCone`/inner-dual separation used here.

## Status
`grind`-free and `simp +decide`-free. Uses `simp +zetaDelta`/`+contextual` (Mathlib-OK).
Remaining polish for PR: some long `refine'`/`simp` chains could be tidied.
-/
import Mathlib
import Contrib.Submission.FgConeClosed

open scoped BigOperators

namespace Contrib.Submission

variable {ι κ : Type*}

/-- A real vector viewed in `EuclideanSpace ℝ ι` by its coordinates. -/
noncomputable def toE [Fintype ι] (f : ι → ℝ) : EuclideanSpace ℝ ι :=
  (WithLp.equiv 2 (ι → ℝ)).symm f

@[simp] lemma toE_apply [Fintype ι] (f : ι → ℝ) (i : ι) : toE f i = f i := rfl

lemma inner_toE [Fintype ι] (f : ι → ℝ) (y : EuclideanSpace ℝ ι) :
    (inner ℝ (toE f) y) = ∑ i, f i * y i := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct, toE, mul_comm]

/-- **Finite Farkas lemma (inequality form).** If the primal system `x ≥ 0, N x ≥ c` is
infeasible, then there is a Farkas certificate `y ≥ 0` with `Nᵀ y ≤ 0` and `⟨c, y⟩ > 0`. -/
theorem farkas_ge [Fintype ι] [Fintype κ]
    (N : ι → κ → ℝ) (c : ι → ℝ)
    (hinfeas : ¬ ∃ x : κ → ℝ, (∀ j, 0 ≤ x j) ∧ (∀ i, c i ≤ ∑ j, N i j * x j)) :
    ∃ y : ι → ℝ, (∀ i, 0 ≤ y i) ∧ (∀ j, ∑ i, N i j * y i ≤ 0) ∧ 0 < ∑ i, c i * y i := by
  classical
  set g : (κ ⊕ ι) → EuclideanSpace ℝ ι :=
    Sum.elim (fun j => toE (fun i => N i j)) (fun i => toE (fun i' => if i' = i then (-1:ℝ) else 0)) with hg
  have hind : ∀ a : κ ⊕ ι, ∑ k, (if k = a then (1:ℝ) else 0) • g k = g a := by
    intro a; simp [ite_smul]
  set S : Set (EuclideanSpace ℝ ι) := {y | ∃ coeff : (κ ⊕ ι) → ℝ, (∀ k, 0 ≤ coeff k) ∧ ∑ k, coeff k • g k = y} with hS
  have hSclosed : IsClosed S := fg_cone_isClosed g
  let K : ConvexCone ℝ (EuclideanSpace ℝ ι) :=
    { carrier := S
      smul_mem' := by
        rintro t ht x ⟨coeff, hcoeff, rfl⟩
        exact ⟨fun k => t * coeff k, fun k => mul_nonneg ht.le (hcoeff k), by
          rw [Finset.smul_sum]; apply Finset.sum_congr rfl; intro k _; rw [smul_smul]⟩
      add_mem' := by
        rintro x ⟨c1, h1, rfl⟩ y ⟨c2, h2, rfl⟩
        exact ⟨fun k => c1 k + c2 k, fun k => add_nonneg (h1 k) (h2 k), by
          rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro k _; rw [add_smul]⟩ }
  have hKne : (K : Set (EuclideanSpace ℝ ι)).Nonempty :=
    ⟨0, ⟨fun _ => 0, fun _ => le_refl 0, by simp⟩⟩
  have hcne : (toE c) ∉ K := by
    rintro ⟨coeff, hcoeff, hsum⟩
    apply hinfeas
    refine ⟨fun j => coeff (Sum.inl j), fun j => hcoeff _, ?_⟩
    intro i
    have hcoord := congrArg (fun z => z i) hsum
    simp only [toE_apply] at hcoord
    have hexp : (∑ k, coeff k • g k) i
        = (∑ j, coeff (Sum.inl j) * N i j) - coeff (Sum.inr i) := by
      rw [Fintype.sum_sum_type]
      simp [hg, EuclideanSpace, PiLp, Finset.sum_apply]
      ring
    have hcomm : ∑ j, N i j * coeff (Sum.inl j) = ∑ j, coeff (Sum.inl j) * N i j := by
      apply Finset.sum_congr rfl; intro j _; ring
    rw [hexp] at hcoord
    have hnn : 0 ≤ coeff (Sum.inr i) := hcoeff _
    linarith
  obtain ⟨y, hy1, hy2⟩ :=
    K.hyperplane_separation_of_nonempty_of_isClosed_of_notMem hKne hSclosed hcne
  refine ⟨fun i => -(y i), fun i => ?_, fun j => ?_, ?_⟩
  · have hmem : g (Sum.inr i) ∈ K := ⟨fun k => if k = Sum.inr i then 1 else 0, fun k => by positivity, hind _⟩
    have hh := hy1 _ hmem
    rw [hg] at hh; simp only [Sum.elim_inr] at hh
    rw [inner_toE] at hh
    have hval : ∑ i', (if i' = i then (-1:ℝ) else 0) * y i' = - y i := by
      rw [Finset.sum_eq_single i] <;> simp +contextual
    rw [hval] at hh
    change 0 ≤ - y i; linarith
  · have hmem : g (Sum.inl j) ∈ K := ⟨fun k => if k = Sum.inl j then 1 else 0, fun k => by positivity, hind _⟩
    have hh := hy1 _ hmem
    rw [hg] at hh; simp only [Sum.elim_inl] at hh
    rw [inner_toE] at hh
    have h2 : ∑ i, N i j * -(y i) = - ∑ i, (fun i => N i j) i * y i := by
      rw [← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro i _; ring
    rw [h2]; linarith
  · rw [real_inner_comm] at hy2
    rw [inner_toE] at hy2
    have h2 : ∑ i, c i * -(y i) = - ∑ i, c i * y i := by
      rw [← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro i _; ring
    rw [h2]; linarith

/-- **Finite LP strong duality (covering/packing).** For a nonnegative incidence matrix `A`
with nonnegative capacities `r`, in which every column has a positive entry, there is a
maximum packing `w` whose value equals the covering optimum. -/
theorem covering_packing_duality [Fintype ι] [Fintype κ]
    (A : ι → κ → ℝ) (r : ι → ℝ)
    (hA : ∀ e t, 0 ≤ A e t) (hr : ∀ e, 0 ≤ r e)
    (hcol : ∀ t, ∃ e, 0 < A e t) :
    ∃ w : κ → ℝ, (∀ t, 0 ≤ w t) ∧ (∀ e, (∑ t, A e t * w t) ≤ r e) ∧
      (∑ t, w t) = sInf {v : ℝ | ∃ x : ι → ℝ, (∀ e, 0 ≤ x e) ∧
        (∀ t, 1 ≤ ∑ e, A e t * x e) ∧ v = ∑ e, r e * x e} := by
  by_contra h_no_wstar
  have hP_le_Mr : ∀ w : κ → ℝ, (∀ t, 0 ≤ w t) ∧ (∀ e, ∑ t, A e t * w t ≤ r e) → ∑ t, w t ≤ sInf {v | ∃ x : ι → ℝ, (∀ e, 0 ≤ x e) ∧ (∀ t, 1 ≤ ∑ e, A e t * x e) ∧ v = ∑ e, r e * x e} := by
    intro w hw
    refine' le_csInf _ _
    · refine' ⟨ _, ⟨ fun e => ∑ t, 1 / A e t, _, _, rfl ⟩ ⟩
      · exact fun e => Finset.sum_nonneg fun t _ => one_div_nonneg.2 ( hA e t )
      · intro t; obtain ⟨ e, he ⟩ := hcol t; refine' le_trans _ ( Finset.single_le_sum ( fun e _ => mul_nonneg ( hA e t ) ( Finset.sum_nonneg fun t _ => one_div_nonneg.mpr ( hA e t ) ) ) ( Finset.mem_univ e ) ) ; simp [ he.ne', mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ]
        exact le_trans ( by norm_num [ he.ne' ] ) ( Finset.single_le_sum ( fun i _ => mul_nonneg he.le ( inv_nonneg.2 ( hA e i ) ) ) ( Finset.mem_univ t ) )
    · rintro _ ⟨ x, hx₁, hx₂, rfl ⟩
      have h_fubini : ∑ t, w t * (∑ e, A e t * x e) = ∑ e, (∑ t, A e t * w t) * x e := by
        simpa only [ mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_mul ] using Finset.sum_comm
      exact le_trans ( Finset.sum_le_sum fun t _ => le_mul_of_one_le_right ( hw.1 t ) ( hx₂ t ) ) ( h_fubini.le.trans ( Finset.sum_le_sum fun e _ => mul_le_mul_of_nonneg_right ( hw.2 e ) ( hx₁ e ) ) )
  obtain ⟨w_star, hw_star⟩ : ∃ w_star : κ → ℝ, (∀ t, 0 ≤ w_star t) ∧ (∀ e, ∑ t, A e t * w_star t ≤ r e) ∧ ∀ w : κ → ℝ, (∀ t, 0 ≤ w t) ∧ (∀ e, ∑ t, A e t * w t ≤ r e) → ∑ t, w t ≤ ∑ t, w_star t := by
    have h_compact : IsCompact {w : κ → ℝ | (∀ t, 0 ≤ w t) ∧ (∀ e, ∑ t, A e t * w t ≤ r e)} := by
      refine' CompactIccSpace.isCompact_Icc.of_isClosed_subset _ _
      exact fun t => 0
      exact fun t => sInf { v | ∃ x : ι → ℝ, ( ∀ e, 0 ≤ x e ) ∧ ( ∀ t, 1 ≤ ∑ e, A e t * x e ) ∧ v = ∑ e, r e * x e }
      · simp only [Set.setOf_and, Set.setOf_forall]
        exact IsClosed.inter ( isClosed_iInter fun _ => isClosed_le continuous_const <| continuous_apply _ ) ( isClosed_iInter fun _ => isClosed_le ( continuous_finset_sum _ fun _ _ => continuous_const.mul <| continuous_apply _ ) continuous_const )
      · exact fun w hw => ⟨ hw.1, fun t => le_trans ( Finset.single_le_sum ( fun a _ => hw.1 a ) ( Finset.mem_univ t ) ) ( hP_le_Mr w hw ) ⟩
    have h_nonempty : {w : κ → ℝ | (∀ t, 0 ≤ w t) ∧ (∀ e, ∑ t, A e t * w t ≤ r e)}.Nonempty := by
      exact ⟨ fun _ => 0, fun _ => le_rfl, fun _ => by simp [ hr ] ⟩
    have := h_compact.exists_isMaxOn h_nonempty ( show ContinuousOn ( fun w : κ → ℝ => ∑ t, w t ) _ from Continuous.continuousOn <| continuous_finset_sum _ fun _ _ => continuous_apply _ )
    exact ⟨ this.choose, this.choose_spec.1.1, this.choose_spec.1.2, fun w hw => this.choose_spec.2 hw ⟩
  have hP_lt_Mr : ∑ t, w_star t < sInf {v | ∃ x : ι → ℝ, (∀ e, 0 ≤ x e) ∧ (∀ t, 1 ≤ ∑ e, A e t * x e) ∧ v = ∑ e, r e * x e} := by
    exact lt_of_le_of_ne ( hP_le_Mr w_star ⟨ hw_star.1, hw_star.2.1 ⟩ ) fun h => h_no_wstar ⟨ w_star, hw_star.1, hw_star.2.1, h ⟩
  obtain ⟨y, hy_nonneg, hy_row, hy_obj⟩ : ∃ y : κ ⊕ Unit → ℝ, (∀ i, 0 ≤ y i) ∧ (∀ e, ∑ i, (Sum.elim (fun t e => A e t) (fun _ e => -r e) i e) * y i ≤ 0) ∧ 0 < ∑ i, (Sum.elim (fun _ => 1) (fun _ => -∑ t, w_star t) i) * y i := by
    have h_farkas : ¬∃ x : ι → ℝ, (∀ e, 0 ≤ x e) ∧ (∀ t, 1 ≤ ∑ e, A e t * x e) ∧ ∑ e, r e * x e ≤ ∑ t, w_star t := by
      contrapose! hP_lt_Mr
      exact le_trans ( csInf_le ⟨ 0, by rintro v ⟨ x, hx₁, hx₂, rfl ⟩ ; exact Finset.sum_nonneg fun _ _ => mul_nonneg ( hr _ ) ( hx₁ _ ) ⟩ ⟨ hP_lt_Mr.choose, hP_lt_Mr.choose_spec.1, hP_lt_Mr.choose_spec.2.1, rfl ⟩ ) hP_lt_Mr.choose_spec.2.2
    convert farkas_ge ( fun i e => Sum.elim ( fun t e => A e t ) ( fun _ e => -r e ) i e ) ( fun i => Sum.elim ( fun _ => 1 ) ( fun _ => -∑ t, w_star t ) i ) _ using 1
    simp +zetaDelta at *
    exact h_farkas
  set lam : κ → ℝ := fun t => y (Sum.inl t)
  set mu : ℝ := y (Sum.inr ())
  have hlam_mu : ∀ e, ∑ t, A e t * lam t ≤ mu * r e := by
    intro e; specialize hy_row e; simp [ Finset.sum_add_distrib, mul_comm ] at hy_row ⊢
    exact hy_row
  have hlam_mu_P : ∑ t, lam t > mu * ∑ t, w_star t := by
    simp +zetaDelta at *
    linarith
  by_cases hmu_zero : mu = 0
  · simp +zetaDelta at *
    simp_all [ Finset.sum_eq_zero_iff_of_nonneg, mul_nonneg ]
    exact hy_obj.ne' ( Finset.sum_eq_zero fun t ht => le_antisymm ( le_of_not_gt fun h => by have := hy_row ( Classical.choose ( hcol t ) ) ; exact not_le_of_gt ( lt_of_lt_of_le ( mul_pos ( Classical.choose_spec ( hcol t ) ) h ) ( Finset.single_le_sum ( fun a _ => mul_nonneg ( hA _ a ) ( hy_nonneg a ) ) ht ) ) this ) ( hy_nonneg t ) )
  · have hlam_mu_div : ∀ e, ∑ t, A e t * (lam t / mu) ≤ r e := by
      simp only [← mul_div_assoc, ← Finset.sum_div]
      exact fun e => div_le_iff₀' ( lt_of_le_of_ne ( hy_nonneg _ ) ( Ne.symm hmu_zero ) ) |>.2 ( hlam_mu e )
    have hlam_mu_div_P : ∑ t, (lam t / mu) > ∑ t, w_star t := by
      rw [ ← Finset.sum_div _ _ _, gt_iff_lt, lt_div_iff₀ ] <;> cases lt_or_gt_of_ne hmu_zero <;> nlinarith [ hy_nonneg ( Sum.inr () ) ]
    exact not_le_of_gt hlam_mu_div_P ( hw_star.2.2 _ ⟨ fun t => div_nonneg ( hy_nonneg _ ) ( hy_nonneg _ ), hlam_mu_div ⟩ )

end Contrib.Submission

/-
# Nibble — solving a near rank-one linear system in the sup norm

The link routing of `Nibble/DrossLinkRouting.lean` asks, inside the link of a vertex, for triangle
weights with *prescribed vertex degrees*.  With the ansatz `b_{xyz} = f x + f y + f z` this becomes
a linear system `M f = c`, where `M v w` counts the link triangles through `v` and `w`.

In a near-complete graph that matrix is, up to a small row error, of the shape `D·I + pi·J`
(`D` on the diagonal, the constant `pi` everywhere) — a *near rank-one perturbation of a multiple of
the identity*.  Such a matrix is invertible with a sup-norm bound that is uniform in the dimension:

* `Nibble.IsNearRankOne` — the hypothesis: the row error of `M - (D·I + pi·J)` is at most `eta·D`.
* `Nibble.norm_le_of_matMap` — **the coercivity estimate** `‖f‖ ≤ 4‖M f‖/D`, for `eta ≤ 1/4`.
* `Nibble.exists_matMap_eq` — **the solution**: every right-hand side `c` is attained, by an `f`
  with `‖f‖ ≤ 4‖c‖/D`.  (Injective ⇒ surjective in finite dimension.)

Sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Data.Real.StarOrdered

open Finset

namespace Nibble

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The linear map given by a matrix. -/
noncomputable def matMap (M : V → V → ℝ) : (V → ℝ) →ₗ[ℝ] (V → ℝ) where
  toFun f := fun v => ∑ w, M v w * f w
  map_add' f g := by
    funext v
    simp only [Pi.add_apply, mul_add]
    exact Finset.sum_add_distrib
  map_smul' a f := by
    funext v
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun w _ => by ring)

omit [DecidableEq V] in
theorem matMap_apply (M : V → V → ℝ) (f : V → ℝ) (v : V) :
    matMap M f v = ∑ w, M v w * f w := rfl

/-- **The near rank-one hypothesis**: each row of `M` differs from the corresponding row of
`D·I + pi·J` by at most `eta·D` in total. -/
def IsNearRankOne (M : V → V → ℝ) (D pi eta : ℝ) : Prop :=
  ∀ v : V, |M v v - (D + pi)| + ∑ w ∈ Finset.univ.erase v, |M v w - pi| ≤ eta * D

/-- Splitting off the rank-one part. -/
theorem matMap_sub_eq (M : V → V → ℝ) (D pi : ℝ) (f : V → ℝ) (v : V) :
    matMap M f v - (D * f v + pi * ∑ w, f w)
      = (M v v - (D + pi)) * f v + ∑ w ∈ Finset.univ.erase v, (M v w - pi) * f w := by
  classical
  have h1 : ∑ w, M v w * f w
      = M v v * f v + ∑ w ∈ Finset.univ.erase v, M v w * f w :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ v)).symm
  have h2 : ∑ w, f w = f v + ∑ w ∈ Finset.univ.erase v, f w :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ v)).symm
  have h3 : ∑ w ∈ Finset.univ.erase v, (M v w - pi) * f w
      = (∑ w ∈ Finset.univ.erase v, M v w * f w) - pi * ∑ w ∈ Finset.univ.erase v, f w := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun w _ => by ring)
  rw [matMap_apply, h1, h2, h3]
  ring

/-- **The rank-one approximation is uniform.**  For every `v`, the value `M f v` differs from
`D·f v + pi·∑ f` by at most `eta·D·‖f‖`. -/
theorem abs_matMap_sub_le (M : V → V → ℝ) {D pi eta : ℝ}
    (h : IsNearRankOne M D pi eta) (f : V → ℝ) (v : V) :
    |matMap M f v - (D * f v + pi * ∑ w, f w)| ≤ eta * D * ‖f‖ := by
  classical
  have hfn : ∀ w : V, |f w| ≤ ‖f‖ := fun w => by
    simpa [Real.norm_eq_abs] using norm_le_pi_norm f w
  rw [matMap_sub_eq M D pi f v]
  calc |(M v v - (D + pi)) * f v + ∑ w ∈ Finset.univ.erase v, (M v w - pi) * f w|
      ≤ |(M v v - (D + pi)) * f v| + |∑ w ∈ Finset.univ.erase v, (M v w - pi) * f w| :=
        abs_add_le _ _
    _ ≤ |M v v - (D + pi)| * ‖f‖ + ∑ w ∈ Finset.univ.erase v, |M v w - pi| * ‖f‖ := by
        refine add_le_add ?_ ?_
        · rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hfn v) (abs_nonneg _)
        · refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun w _ => ?_))
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hfn w) (abs_nonneg _)
    _ = (|M v v - (D + pi)| + ∑ w ∈ Finset.univ.erase v, |M v w - pi|) * ‖f‖ := by
        rw [← Finset.sum_mul]; ring
    _ ≤ (eta * D) * ‖f‖ := mul_le_mul_of_nonneg_right (h v) (norm_nonneg f)
    _ = eta * D * ‖f‖ := by ring

/-- **The coercivity estimate.**  A near rank-one matrix with row error at most `D/4` is bounded
below by `D/4` in the sup norm. -/
theorem norm_le_of_matMap (M : V → V → ℝ) {D pi eta : ℝ} (hD : 0 < D) (hpi : 0 ≤ pi)
    (heta : 0 ≤ eta) (heta4 : eta ≤ 1 / 4) (h : IsNearRankOne M D pi eta) (f : V → ℝ) :
    ‖f‖ ≤ 4 * ‖matMap M f‖ / D := by
  classical
  set ε : ℝ := ‖matMap M f‖ with hε
  set Λ : ℝ := ‖f‖ with hΛ
  have hεnn : 0 ≤ ε := norm_nonneg _
  have hΛnn : 0 ≤ Λ := norm_nonneg _
  set F : ℝ := ∑ w, f w with hF
  set ε' : ℝ := ε + eta * D * Λ with hε'
  have hε'nn : 0 ≤ ε' := by positivity
  -- the pointwise estimate
  have hpt : ∀ v : V, |D * f v + pi * F| ≤ ε' := by
    intro v
    have h1 : |matMap M f v| ≤ ε := by
      simpa [Real.norm_eq_abs] using norm_le_pi_norm (matMap M f) v
    have h2 := abs_matMap_sub_le M h f v
    have h3 : |D * f v + pi * F| ≤ |matMap M f v| + |matMap M f v - (D * f v + pi * F)| := by
      have hEq : D * f v + pi * F
          = matMap M f v + (-(matMap M f v - (D * f v + pi * F))) := by ring
      calc |D * f v + pi * F|
          = |matMap M f v + (-(matMap M f v - (D * f v + pi * F)))| := congrArg abs hEq
        _ ≤ |matMap M f v| + |-(matMap M f v - (D * f v + pi * F))| := abs_add_le _ _
        _ = |matMap M f v| + |matMap M f v - (D * f v + pi * F)| := by rw [abs_neg]
    calc |D * f v + pi * F| ≤ |matMap M f v| + |matMap M f v - (D * f v + pi * F)| := h3
      _ ≤ ε + eta * D * Λ := add_le_add h1 h2
  -- the rank-one direction
  have hpiF : pi * |F| ≤ ε' := by
    rcases eq_or_lt_of_le hpi with hpi0 | hpipos
    · rw [← hpi0]; simpa using hε'nn
    · set N : ℕ := Fintype.card V with hN
      have hsum : |D * F + (N : ℝ) * (pi * F)| ≤ (N : ℝ) * ε' := by
        have hid : D * F + (N : ℝ) * (pi * F) = ∑ v : V, (D * f v + pi * F) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← hF, Finset.sum_const, Finset.card_univ,
            nsmul_eq_mul, ← hN]
        rw [hid]
        calc |∑ v : V, (D * f v + pi * F)| ≤ ∑ _v : V, ε' :=
              (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun v _ => hpt v))
          _ = (N : ℝ) * ε' := by
              rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hN]
      have hfac : |F| * (D + (N : ℝ) * pi) ≤ (N : ℝ) * ε' := by
        have : D * F + (N : ℝ) * (pi * F) = F * (D + (N : ℝ) * pi) := by ring
        rw [this, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ D + (N : ℝ) * pi)] at hsum
        exact hsum
      have hNnn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
      rcases Nat.eq_zero_or_pos N with hN0 | hNpos
      · have hN0' : (N : ℝ) = 0 := by rw [hN0]; norm_num
        rw [hN0'] at hfac
        have hFz : |F| ≤ 0 := by nlinarith [abs_nonneg F]
        nlinarith [abs_nonneg F]
      · have hNposR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
        have hNpi : (0 : ℝ) < (N : ℝ) * pi := by positivity
        have hstep : (N : ℝ) * pi * (pi * |F|) ≤ (N : ℝ) * pi * ε' := by
          linarith only [mul_nonneg (mul_nonneg hpi (abs_nonneg F)) hD.le, abs_nonneg F,
            mul_le_mul_of_nonneg_left hfac hpi]
        exact le_of_mul_le_mul_left hstep hNpi
  -- conclude
  have hbound : ∀ v : V, |f v| ≤ 2 * ε' / D := by
    intro v
    have h1 := hpt v
    have h2 : |D * f v| ≤ |D * f v + pi * F| + |pi * F| := by
      have hEq : D * f v = (D * f v + pi * F) + (-(pi * F)) := by ring
      calc |D * f v| = |(D * f v + pi * F) + (-(pi * F))| := congrArg abs hEq
        _ ≤ |D * f v + pi * F| + |-(pi * F)| := abs_add_le _ _
        _ = |D * f v + pi * F| + |pi * F| := by rw [abs_neg]
    have h3 : |pi * F| = pi * |F| := by rw [abs_mul, abs_of_nonneg hpi]
    have h4 : |D * f v| = D * |f v| := by rw [abs_mul, abs_of_nonneg hD.le]
    rw [le_div_iff₀ hD]
    linarith only [h1, h2, h3, h4, hpiF]
  have hΛle : Λ ≤ 2 * ε' / D := by
    rw [hΛ]
    refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr (fun v => ?_)
    simpa [Real.norm_eq_abs] using hbound v
  have hΛD : Λ * D ≤ 2 * ε' := (le_div_iff₀ hD).mp hΛle
  have hetaD : eta * (D * Λ) ≤ (1 / 4) * (D * Λ) :=
    mul_le_mul_of_nonneg_right heta4 (by positivity)
  rw [le_div_iff₀ hD]
  have hε'eq : ε' = ε + eta * D * Λ := hε'
  linarith only [hΛD, hetaD, hΛnn, hD, hεnn]

/-- **The solution.**  A near rank-one system with row error at most `D/4` is solvable, with a
sup-norm bound `4‖c‖/D` on the solution. -/
theorem exists_matMap_eq (M : V → V → ℝ) {D pi eta : ℝ} (hD : 0 < D) (hpi : 0 ≤ pi)
    (heta : 0 ≤ eta) (heta4 : eta ≤ 1 / 4) (h : IsNearRankOne M D pi eta) (c : V → ℝ) :
    ∃ f : V → ℝ, (∀ v, ∑ w, M v w * f w = c v) ∧ ‖f‖ ≤ 4 * ‖c‖ / D := by
  have hinj : Function.Injective (matMap M) := by
    rw [injective_iff_map_eq_zero]
    intro f hf
    have := norm_le_of_matMap M hD hpi heta heta4 h f
    rw [hf] at this
    simp only [norm_zero, mul_zero, zero_div] at this
    have : ‖f‖ = 0 := le_antisymm this (norm_nonneg f)
    exact norm_eq_zero.mp this
  obtain ⟨f, hfc⟩ := (LinearMap.injective_iff_surjective).mp hinj c
  refine ⟨f, fun v => ?_, ?_⟩
  · have := congrFun hfc v
    exact this
  · have := norm_le_of_matMap M hD hpi heta heta4 h f
    rwa [hfc] at this

end Nibble

import PaperI.RationalFarkas
import PaperI.FiniteLP

/-!
# Strong duality and attainment for the finite packing/covering LP

Using the rational Farkas lemma of `PaperI.RationalFarkas`, this file proves that
the finite packing LP

```
maximize  ∑ i, gain i * w i     subject to  w ≥ 0,  ∀ e, ∑ i, A i e * w i ≤ 1
```

and its covering dual

```
minimize  ∑ e, x e              subject to  x ≥ 0,  ∀ i, gain i ≤ ∑ e, A i e * x e
```

both attain their optimum, at the *same rational value*.  The only hypotheses
are that the incidence matrix is nonnegative and that every item uses at least
one resource (otherwise the packing LP is unbounded).

Everything happens over `ℚ`, so no completeness or separation argument is
used, and the optimal value produced is a rational number.

The proof is the standard one: the combined primal/dual system, augmented with
the reversed weak-duality inequality `∑ e, x e ≤ ∑ i, gain i * w i`, is shown
to be feasible by contradiction from a Farkas certificate.

**Procedencia.**  El *resultado* --dualidad fuerte finita en forma cubrimiento/empaquetamiento--
es de Paper I.  La *demostracion* de este fichero no lo es: Paper I la establece sobre `R`
(`EuclideanSpace`, conos simpliciales cerrados, Caratheodory conico), y el modelo mixto de
Paper IV necesita que el valor optimo sea **racional**.  Por eso aqui se reprueba sobre `Q`
por eliminacion de Fourier--Motzkin.  Se cita Paper I por el resultado; la prueba racional es
material nuevo de Paper IV.
-/

open scoped BigOperators
open Finset

namespace PaperI.FiniteLP

variable {Item Resource : Type} [Fintype Item] [Fintype Resource]

/-- Rows of the combined primal/dual system: item nonnegativity, capacity,
resource nonnegativity, covering demand, and the reversed duality row. -/
abbrev DualityRow (Item Resource : Type) :=
  Item ⊕ Resource ⊕ Resource ⊕ Item ⊕ Unit

/-- The matrix of the combined primal/dual system. -/
def dualityMat [DecidableEq Item] [DecidableEq Resource]
    (incidence : Item → Resource → ℚ) (gain : Item → ℚ) :
    DualityRow Item Resource → (Item ⊕ Resource) → ℚ
  | Sum.inl i0, Sum.inl i => if i = i0 then -1 else 0
  | Sum.inl _, Sum.inr _ => 0
  | Sum.inr (Sum.inl e0), Sum.inl i => incidence i e0
  | Sum.inr (Sum.inl _), Sum.inr _ => 0
  | Sum.inr (Sum.inr (Sum.inl _)), Sum.inl _ => 0
  | Sum.inr (Sum.inr (Sum.inl e0)), Sum.inr e => if e = e0 then -1 else 0
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl _))), Sum.inl _ => 0
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl i0))), Sum.inr e => -incidence i0 e
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr ()))), Sum.inl i => -gain i
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr ()))), Sum.inr _ => 1

/-- The right-hand side of the combined primal/dual system. -/
def dualityRhs (gain : Item → ℚ) : DualityRow Item Resource → ℚ
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl _) => 1
  | Sum.inr (Sum.inr (Sum.inl _)) => 0
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl i0))) => -gain i0
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr ()))) => 0

/-- Pulling a common positive scale out of a sum of products. -/
private theorem sum_mul_div_right {ι : Type*} [Fintype ι] (f g : ι → ℚ) (c : ℚ) :
    ∑ j, f j * (g j / c) = (∑ j, g j * f j) / c := by
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **The combined primal/dual system is feasible.**  There are a feasible
packing and a feasible cover whose values satisfy the reversed weak-duality
inequality. -/
theorem exists_primal_dual_pair (incidence : Item → Resource → ℚ)
    (gain : Item → ℚ) (hinc : ∀ i e, 0 ≤ incidence i e)
    (hcol : ∀ i, ∃ e, 0 < incidence i e) :
    ∃ (w : Item → ℚ) (x : Resource → ℚ),
      (∀ i, 0 ≤ w i) ∧ (∀ e, ∑ i, incidence i e * w i ≤ 1) ∧
      (∀ e, 0 ≤ x e) ∧ (∀ i, gain i ≤ ∑ e, incidence i e * x e) ∧
      ∑ e, x e ≤ ∑ i, gain i * w i := by
  classical
  rcases RationalFarkas.farkas (dualityMat incidence gain) (dualityRhs gain) with
    ⟨v, hv⟩ | ⟨y, hy0, hyA, hyb⟩
  · -- a solution of the combined system is exactly the desired pair
    refine ⟨fun i => v (Sum.inl i), fun e => v (Sum.inr e), ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      have h := hv (Sum.inl i)
      simp [dualityMat, dualityRhs, Fintype.sum_sum_type, ite_mul] at h
      linarith
    · intro e
      have h := hv (Sum.inr (Sum.inl e))
      simpa [dualityMat, dualityRhs, Fintype.sum_sum_type] using h
    · intro e
      have h := hv (Sum.inr (Sum.inr (Sum.inl e)))
      simp [dualityMat, dualityRhs, Fintype.sum_sum_type, ite_mul] at h
      linarith
    · intro i
      have h := hv (Sum.inr (Sum.inr (Sum.inr (Sum.inl i))))
      simp only [dualityMat, dualityRhs, Fintype.sum_sum_type] at h
      have h2 : -∑ e, incidence i e * v (Sum.inr e) ≤ -gain i := by
        have hrw : ∑ e, -incidence i e * v (Sum.inr e)
            = -∑ e, incidence i e * v (Sum.inr e) := by
          rw [← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl fun e _ => by ring
        simpa [hrw] using h
      linarith
    · have h := hv (Sum.inr (Sum.inr (Sum.inr (Sum.inr ()))))
      simp only [dualityMat, dualityRhs, Fintype.sum_sum_type] at h
      have hrw1 : ∑ i, -gain i * v (Sum.inl i)
          = -∑ i, gain i * v (Sum.inl i) := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
      have hrw2 : ∑ e, (1 : ℚ) * v (Sum.inr e) = ∑ e, v (Sum.inr e) := by
        exact Finset.sum_congr rfl fun e _ => one_mul _
      rw [hrw1, hrw2] at h
      linarith
  · -- a Farkas certificate is impossible
    exfalso
    set α : Item → ℚ := fun i => y (Sum.inl i) with hα
    set β : Resource → ℚ := fun e => y (Sum.inr (Sum.inl e)) with hβ
    set γ : Resource → ℚ := fun e => y (Sum.inr (Sum.inr (Sum.inl e))) with hγ
    set δ : Item → ℚ := fun i => y (Sum.inr (Sum.inr (Sum.inr (Sum.inl i))))
      with hδ
    set θ : ℚ := y (Sum.inr (Sum.inr (Sum.inr (Sum.inr ())))) with hθ
    have hunit : ∀ f : Unit → ℚ, ∑ u : Unit, f u = f () := fun f => by simp
    have hα0 : ∀ i, 0 ≤ α i := fun i => hy0 _
    have hβ0 : ∀ e, 0 ≤ β e := fun e => hy0 _
    have hγ0 : ∀ e, 0 ≤ γ e := fun e => hy0 _
    have hδ0 : ∀ i, 0 ≤ δ i := fun i => hy0 _
    have hθ0 : 0 ≤ θ := hy0 _
    -- the item columns
    have hitem : ∀ i, θ * gain i + α i = ∑ e, β e * incidence i e := by
      intro i
      have h := hyA (Sum.inl i)
      simp only [dualityMat, Fintype.sum_sum_type] at h
      rw [hunit] at h
      have h1 : ∑ i0, y (Sum.inl i0) * (if i = i0 then (-1 : ℚ) else 0)
          = -α i := by
        simp [hα, mul_ite]
      have h2 : ∑ e, y (Sum.inr (Sum.inl e)) * incidence i e
          = ∑ e, β e * incidence i e := rfl
      have h3 : ∑ e, y (Sum.inr (Sum.inr (Sum.inl e))) * (0 : ℚ) = 0 := by simp
      have h4 : ∑ i0, y (Sum.inr (Sum.inr (Sum.inr (Sum.inl i0)))) * (0 : ℚ)
          = 0 := by simp
      rw [h1, h2, h3, h4] at h
      have h5 : y (Sum.inr (Sum.inr (Sum.inr (Sum.inr ())))) * (-gain i)
          = -(θ * gain i) := by rw [hθ]; ring
      rw [h5] at h
      linarith [h]
    -- the resource columns
    have hres : ∀ e, γ e + ∑ i, δ i * incidence i e = θ := by
      intro e
      have h := hyA (Sum.inr e)
      simp only [dualityMat, Fintype.sum_sum_type] at h
      rw [hunit] at h
      have h1 : ∑ i, y (Sum.inl i) * (0 : ℚ) = 0 := by simp
      have h2 : ∑ e0, y (Sum.inr (Sum.inl e0)) * (0 : ℚ) = 0 := by simp
      have h3 : ∑ e0, y (Sum.inr (Sum.inr (Sum.inl e0)))
            * (if e = e0 then (-1 : ℚ) else 0) = -γ e := by
        simp [hγ, mul_ite]
      have h4 : ∑ i, y (Sum.inr (Sum.inr (Sum.inr (Sum.inl i))))
            * (-incidence i e) = -∑ i, δ i * incidence i e := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun i _ => by rw [hδ]; ring
      have h5 : y (Sum.inr (Sum.inr (Sum.inr (Sum.inr ())))) * (1 : ℚ) = θ := by
        rw [hθ]; ring
      rw [h1, h2, h3, h4, h5] at h
      linarith [h]
    -- the objective row
    have hobj : ∑ e, β e < ∑ i, δ i * gain i := by
      have h := hyb
      simp only [dualityRhs, Fintype.sum_sum_type] at h
      rw [hunit] at h
      have h1 : ∑ i, y (Sum.inl i) * (0 : ℚ) = 0 := by simp
      have h2 : ∑ e, y (Sum.inr (Sum.inl e)) * (1 : ℚ) = ∑ e, β e := by
        exact Finset.sum_congr rfl fun e _ => by rw [hβ]; ring
      have h3 : ∑ e, y (Sum.inr (Sum.inr (Sum.inl e))) * (0 : ℚ) = 0 := by simp
      have h4 : ∑ i, y (Sum.inr (Sum.inr (Sum.inr (Sum.inl i)))) * (-gain i)
          = -∑ i, δ i * gain i := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun i _ => by rw [hδ]; ring
      have h5 : y (Sum.inr (Sum.inr (Sum.inr (Sum.inr ())))) * (0 : ℚ) = 0 := by
        simp
      rw [h1, h2, h3, h4, h5] at h
      linarith [h]
    rcases eq_or_lt_of_le hθ0 with hzero | hpos
    · -- the degenerate case: all covering multipliers vanish
      have hδzero : ∀ i, δ i = 0 := by
        intro i
        obtain ⟨e, he⟩ := hcol i
        have hsum : ∑ i0, δ i0 * incidence i0 e = 0 := by
          have := hres e
          have hγe := hγ0 e
          have hnn : 0 ≤ ∑ i0, δ i0 * incidence i0 e :=
            Finset.sum_nonneg fun i0 _ => mul_nonneg (hδ0 i0) (hinc i0 e)
          linarith [this, hzero ▸ this]
        have hterm : δ i * incidence i e = 0 := by
          have := (Finset.sum_eq_zero_iff_of_nonneg
            (fun i0 (_ : i0 ∈ Finset.univ) => mul_nonneg (hδ0 i0) (hinc i0 e))).mp
            hsum
          exact this i (Finset.mem_univ i)
        rcases mul_eq_zero.mp hterm with h | h
        · exact h
        · exact absurd h (ne_of_gt he)
      have h1 : ∑ i, δ i * gain i = 0 :=
        Finset.sum_eq_zero fun i _ => by rw [hδzero i, zero_mul]
      have h2 : 0 ≤ ∑ e, β e := Finset.sum_nonneg fun e _ => hβ0 e
      rw [h1] at hobj
      linarith
    · -- the main case: rescale the certificate into a feasible pair
      have hw : ∀ e, ∑ i, incidence i e * (δ i / θ) ≤ 1 := by
        intro e
        have h := hres e
        have hle : ∑ i, δ i * incidence i e ≤ θ := by linarith [hγ0 e]
        rw [sum_mul_div_right, div_le_one hpos]
        exact hle
      have hx : ∀ i, gain i ≤ ∑ e, incidence i e * (β e / θ) := by
        intro i
        have h := hitem i
        have hle : θ * gain i ≤ ∑ e, β e * incidence i e := by
          linarith [hα0 i]
        rw [sum_mul_div_right, le_div_iff₀ hpos]
        linarith
      -- weak duality for the rescaled pair
      have hweak : ∑ i, gain i * (δ i / θ) ≤ ∑ e, β e / θ :=
        weak_duality
          ({ weight := fun i => δ i / θ
             weight_nonnegative := fun i => div_nonneg (hδ0 i) hpos.le
             capacity := hw } : PrimalFeasible incidence)
          ({ price := fun e => β e / θ
             price_nonnegative := fun e => div_nonneg (hβ0 e) hpos.le
             demand := hx } : DualFeasible incidence gain)
      rw [sum_mul_div_right, ← Finset.sum_div,
        div_le_div_iff₀ hpos hpos] at hweak
      nlinarith [hobj, hpos]

/-- **Strong duality with attainment for the finite packing/covering LP.**
Both optima are attained, at one and the same rational value. -/
theorem exists_optimal_pair (incidence : Item → Resource → ℚ) (gain : Item → ℚ)
    (hinc : ∀ i e, 0 ≤ incidence i e) (hcol : ∀ i, ∃ e, 0 < incidence i e) :
    ∃ (p : PrimalFeasible incidence) (d : DualFeasible incidence gain),
      primalValue gain p = dualValue d ∧
      (∀ p' : PrimalFeasible incidence, primalValue gain p' ≤ primalValue gain p) ∧
      (∀ d' : DualFeasible incidence gain, dualValue d ≤ dualValue d') := by
  obtain ⟨w, x, hw0, hwcap, hx0, hxdem, hgap⟩ :=
    exists_primal_dual_pair incidence gain hinc hcol
  let p : PrimalFeasible incidence :=
    { weight := w, weight_nonnegative := hw0, capacity := hwcap }
  let d : DualFeasible incidence gain :=
    { price := x, price_nonnegative := hx0, demand := hxdem }
  -- the constructed pair has no duality gap, so weak duality makes each side
  -- optimal in one step
  have hgap' : dualValue d ≤ primalValue gain p := hgap
  exact ⟨p, d, le_antisymm (weak_duality p d) hgap',
    fun p' => (weak_duality p' d).trans hgap',
    fun d' => hgap'.trans (weak_duality p d')⟩

end PaperI.FiniteLP


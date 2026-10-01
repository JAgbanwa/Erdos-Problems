import PaperIV.DegreeConcentration

/-!
# Momentos mixtos de indicadores centrados

Cierra el único hueco de §16.3: `EighthMoment.tail_bound` pide que se factoricen los momentos
mixtos de las variables **centradas**, mientras que lo que la independencia por bloques da
(`DegreeConcentration.expect_prod_blocks`) es la factorización de productos de **indicadores**,
sin centrar.

## El paso

Un indicador toma sólo los valores `0` y `1`, así que **toda** función suya es afín en él:

```
φ(I) = φ(0) + (φ(1) − φ(0))·I.
```

En particular `(I_j − μ_j)^{k_j} = a_j + b_j·I_j`.  Desarrollando el producto con
`Finset.prod_add`,

```
∏_j (a_j + b_j I_j) = ∑_{T} (∏_T b)(∏_{sᶜ∩s} a)(∏_T I_j),
```

y tomando esperanzas, la factorización de los productos de indicadores convierte cada
`E[∏_T I_j]` en `∏_T μ_j`.  Volviendo a plegar con `prod_add` sale `∏_j (a_j + b_j μ_j)`, que
es `∏_j E[(I_j − μ_j)^{k_j}]`.

**No hay contenido probabilístico nuevo**: es álgebra sobre la hipótesis de factorización que
ya se tenía.

## Resultado

`tail_of_indicators` — para una familia de indicadores cuyos productos se factorizan, la suma
centrada satisface la cola del octavo momento **sin hipótesis adicionales**.  Instanciado con
las capas de §16.2 (vía `expect_prod_blocks`), eso es la cola por capa que `§16.3` necesitaba,
y `DegreeConcentration.degree_tail_bound` deja de ser condicional.
-/

namespace PaperIV.CenteredMoments

open Finset
open PaperIV.EighthMoment

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-! ## 1. Linealidad afín de la esperanza -/

theorem expect_affine (P : FinProb Ω) (a b : ℚ) (I : Ω → ℚ) :
    P.expect (fun ω => a + b * I ω) = a + b * P.expect I := by
  classical
  have hterm : ∀ ω, P.w ω * (a + b * I ω) = a * P.w ω + b * (P.w ω * I ω) := by
    intro ω; ring
  show ∑ ω, P.w ω * (a + b * I ω) = _
  rw [Finset.sum_congr rfl (fun ω _ => hterm ω), Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, P.w_total, mul_one]
  rfl

theorem expect_const_mul (P : FinProb Ω) (c : ℚ) (f : Ω → ℚ) :
    P.expect (fun ω => c * f ω) = c * P.expect f := by
  have h := expect_affine P 0 c f
  simpa using h

/-! ## 2. Todo lo que depende de un indicador es afín en él -/

/-- Si `I ω ∈ {0,1}`, entonces `(I ω − μ)^k` es afín en `I ω`. -/
theorem pow_sub_eq_affine {I μ : ℚ} (h : I = 0 ∨ I = 1) (k : ℕ) :
    (I - μ) ^ k = ((0 : ℚ) - μ) ^ k + (((1 : ℚ) - μ) ^ k - ((0 : ℚ) - μ) ^ k) * I := by
  rcases h with h | h <;> rw [h] <;> ring

/-! ## 3. La factorización de productos afines -/

/-- **El paso clave.**  Si los productos de los indicadores se factorizan, también lo hacen los
productos de funciones afines de ellos. -/
theorem expect_prod_affine (P : FinProb Ω) {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (I : ι → Ω → ℚ) (a b : ι → ℚ)
    (hfac : ∀ T ⊆ s, P.expect (fun ω => ∏ j ∈ T, I j ω) = ∏ j ∈ T, P.expect (I j)) :
    P.expect (fun ω => ∏ j ∈ s, (a j + b j * I j ω))
      = ∏ j ∈ s, (a j + b j * P.expect (I j)) := by
  classical
  -- desarrollar el producto
  have hL : ∀ ω, (∏ j ∈ s, (a j + b j * I j ω))
      = ∑ T ∈ s.powerset,
          ((∏ j ∈ T, b j) * (∏ j ∈ s \ T, a j)) * (∏ j ∈ T, I j ω) := by
    intro ω
    have hcomm : ∀ j ∈ s, a j + b j * I j ω = b j * I j ω + a j := fun j _ => add_comm _ _
    rw [Finset.prod_congr rfl hcomm, Finset.prod_add]
    refine Finset.sum_congr rfl ?_
    intro T _
    rw [Finset.prod_mul_distrib]
    ring
  have hfun : (fun ω => ∏ j ∈ s, (a j + b j * I j ω))
      = (fun ω => ∑ T ∈ s.powerset,
          ((∏ j ∈ T, b j) * (∏ j ∈ s \ T, a j)) * (∏ j ∈ T, I j ω)) := funext hL
  rw [hfun, P.expect_sum]
  -- cada término
  have hterm : ∀ T ∈ s.powerset,
      P.expect (fun ω => ((∏ j ∈ T, b j) * (∏ j ∈ s \ T, a j)) * (∏ j ∈ T, I j ω))
        = ((∏ j ∈ T, b j) * (∏ j ∈ s \ T, a j)) * ∏ j ∈ T, P.expect (I j) := by
    intro T hT
    rw [expect_const_mul, hfac T (Finset.mem_powerset.1 hT)]
  rw [Finset.sum_congr rfl hterm]
  -- volver a plegar
  have hR : ∏ j ∈ s, (a j + b j * P.expect (I j))
      = ∑ T ∈ s.powerset,
          ((∏ j ∈ T, b j) * (∏ j ∈ s \ T, a j)) * ∏ j ∈ T, P.expect (I j) := by
    have hcomm : ∀ j ∈ s, a j + b j * P.expect (I j) = b j * P.expect (I j) + a j :=
      fun j _ => add_comm _ _
    rw [Finset.prod_congr rfl hcomm, Finset.prod_add]
    refine Finset.sum_congr rfl ?_
    intro T _
    rw [Finset.prod_mul_distrib]
    ring
  rw [hR]

/-! ## 4. Los momentos mixtos centrados -/

/-- **La factorización de los momentos mixtos centrados.**  Es lo que
`EighthMoment.eighth_moment` pide. -/
theorem centered_mixed_moments (P : FinProb Ω) {m : ℕ} (I : Fin m → Ω → ℚ)
    (hI : ∀ j ω, I j ω = 0 ∨ I j ω = 1)
    (hfac : ∀ T : Finset (Fin m), T ⊆ univ →
      P.expect (fun ω => ∏ j ∈ T, I j ω) = ∏ j ∈ T, P.expect (I j))
    (k : Fin m → ℕ) :
    P.expect (fun ω => ∏ j, (I j ω - P.expect (I j)) ^ (k j))
      = ∏ j, P.expect (fun ω => (I j ω - P.expect (I j)) ^ (k j)) := by
  classical
  set a : Fin m → ℚ := fun j => ((0 : ℚ) - P.expect (I j)) ^ (k j) with ha
  set b : Fin m → ℚ :=
    fun j => ((1 : ℚ) - P.expect (I j)) ^ (k j) - ((0 : ℚ) - P.expect (I j)) ^ (k j) with hb
  have hpt : ∀ ω, (∏ j, (I j ω - P.expect (I j)) ^ (k j))
      = ∏ j, (a j + b j * I j ω) := by
    intro ω
    refine Finset.prod_congr rfl ?_
    intro j _
    exact pow_sub_eq_affine (hI j ω) (k j)
  have hmarg : ∀ j : Fin m,
      P.expect (fun ω => (I j ω - P.expect (I j)) ^ (k j)) = a j + b j * P.expect (I j) := by
    intro j
    have hfunj : (fun ω => (I j ω - P.expect (I j)) ^ (k j))
        = (fun ω => a j + b j * I j ω) :=
      funext (fun ω => pow_sub_eq_affine (hI j ω) (k j))
    rw [hfunj, expect_affine]
  rw [funext hpt, expect_prod_affine P univ I a b (fun T _ => hfac T (Finset.subset_univ T))]
  exact Finset.prod_congr rfl (fun j _ => (hmarg j).symm)

/-! ## 5. La cola, ya sin hipótesis extra -/

theorem expect_indicator_mem (P : FinProb Ω) {I : Ω → ℚ} (hI : ∀ ω, I ω = 0 ∨ I ω = 1) :
    0 ≤ P.expect I ∧ P.expect I ≤ 1 := by
  constructor
  · refine le_trans (le_of_eq (P.expect_const 0).symm) (P.expect_mono ?_)
    intro ω
    rcases hI ω with h | h <;> rw [h] <;> norm_num
  · refine le_trans (P.expect_mono ?_) (le_of_eq (P.expect_const 1))
    intro ω
    rcases hI ω with h | h <;> rw [h] <;> norm_num

/-- **La cola del octavo momento para indicadores.**  Si los productos de los indicadores se
factorizan —lo que da `DegreeConcentration.expect_prod_blocks` para soportes disjuntos—, la
suma centrada cumple la cola **sin ninguna hipótesis adicional**. -/
theorem tail_of_indicators (P : FinProb Ω) {m : ℕ} (I : Fin m → Ω → ℚ)
    (hI : ∀ j ω, I j ω = 0 ∨ I j ω = 1)
    (hfac : ∀ T : Finset (Fin m), T ⊆ univ →
      P.expect (fun ω => ∏ j ∈ T, I j ω) = ∏ j ∈ T, P.expect (I j))
    {z : ℚ} (hz : 0 < z) :
    P.prob (univ.filter (fun ω => z ≤ |∑ j, (I j ω - P.expect (I j))|))
      ≤ 4 ^ 8 * (m : ℚ) ^ 4 / z ^ 8 := by
  classical
  refine PaperIV.EighthMoment.tail_bound P (fun j ω => I j ω - P.expect (I j)) ?_ ?_ ?_ hz
  · intro k
    exact centered_mixed_moments P I hI hfac k
  · intro j
    show P.expect (fun ω => I j ω - P.expect (I j)) = 0
    have hfunj : (fun ω => I j ω - P.expect (I j))
        = (fun ω => (-(P.expect (I j))) + 1 * I j ω) := by
      funext ω; ring
    rw [hfunj, expect_affine]
    ring
  · intro j ω
    show |I j ω - P.expect (I j)| ≤ 1
    obtain ⟨h0, h1⟩ := expect_indicator_mem P (hI j)
    rcases hI j ω with h | h <;> rw [h, abs_le] <;> constructor <;> linarith

/-! ## 6. La cola por capa, incondicional -/

section Blocks

open PaperIV.OwnerCoins PaperIV.DegreeConcentration

variable {ρ κ : Type*} [Fintype ρ] [DecidableEq ρ] [Fintype κ] [DecidableEq κ]

/-- El indicador de supervivencia de un bloque vale `0` o `1`. -/
theorem block_indicator_mem (S : Finset ρ) (σ : κ) (ω : ρ → κ) :
    (∏ f ∈ S, (if ω f = σ then (1 : ℚ) else 0)) = 0
      ∨ (∏ f ∈ S, (if ω f = σ then (1 : ℚ) else 0)) = 1 := by
  classical
  refine Finset.prod_induction _ (fun x => x = 0 ∨ x = 1) ?_ (Or.inr rfl) ?_
  · rintro x y (rfl | rfl) (rfl | rfl) <;> simp
  · intro f _
    by_cases h : ω f = σ
    · exact Or.inr (if_pos h)
    · exact Or.inl (if_neg h)

/-- **La cola por capa, sin hipótesis.**  Soportes disjuntos ⟹ los indicadores de
supervivencia, centrados, cumplen la cola del octavo momento.

Ésta es exactamente la hipótesis `hlayer` de `DegreeConcentration.degree_tail_bound`, así que
con esto §16.3 deja de ser condicional. -/
theorem tail_of_disjoint_blocks (q : ρ → κ → ℚ) (hnn : ∀ e j, 0 ≤ q e j)
    (hsum : ∀ e, ∑ j, q e j = 1) {m : ℕ} (S : Fin m → Finset ρ)
    (hdisj : (Set.univ : Set (Fin m)).PairwiseDisjoint S) (σ : κ) {z : ℚ} (hz : 0 < z) :
    (coinSpace q hnn hsum).prob (univ.filter (fun ω =>
        z ≤ |∑ j, ((∏ f ∈ S j, (if ω f = σ then (1 : ℚ) else 0))
              - (coinSpace q hnn hsum).expect
                  (fun ω' => ∏ f ∈ S j, (if ω' f = σ then (1 : ℚ) else 0)))|))
      ≤ 4 ^ 8 * (m : ℚ) ^ 4 / z ^ 8 := by
  classical
  refine tail_of_indicators (coinSpace q hnn hsum)
    (fun j ω => ∏ f ∈ S j, (if ω f = σ then (1 : ℚ) else 0))
    (fun j ω => block_indicator_mem (S j) σ ω) ?_ hz
  intro T _
  exact expect_prod_blocks q hnn hsum T S
    (hdisj.subset (Set.subset_univ _)) σ

end Blocks

end PaperIV.CenteredMoments

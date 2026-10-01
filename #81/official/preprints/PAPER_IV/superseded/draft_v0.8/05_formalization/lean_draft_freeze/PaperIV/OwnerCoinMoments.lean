import PaperIV.OwnerCoins
import PaperIV.SimultaneousSelection

/-!
# Segundo momento de un conteo de bloques sobre el espacio de monedas por arista

Las monedas de `PaperIV.OwnerCoins` son **por recurso** (por arista): el indicador de un
candidato es un *producto* de indicadores de arista, y dos candidatos que comparten una arista
están correlacionados.  Este módulo da la cota de varianza que sustituye a la independencia:

> Sólo los pares de bloques **no disjuntos** contribuyen a la varianza.

Es la forma cuantitativa del mismo hecho que `CyclicLayering.pageEdges_disjoint` usa para las
capas: si dos bloques son disjuntos, sus indicadores son independientes y su covarianza es
exactamente cero (`variance_le`, primer caso).  Aquí no se supone estructura de capas: lo que
paga la cota es un conteo de pares no disjuntos, que en la aplicación sale del **codegrado**
del pool.

## Contenido

* `prod_ind_eq_if` — un producto de indicadores es el indicador del «todas las monedas valen
  `σ`»;
* `expect_block`, `expect_count` — la media, vía `OwnerCoins.expect_indicator`;
* `expect_count_sq` — el segundo momento, `∑_{i,j} p^{|S i ∪ S j|}`, por idempotencia de los
  indicadores;
* `variance_le` — la varianza, acotada por `(#pares no disjuntos)·p^k`;
* `lower_tail` — Chebyshev unilateral, en la forma de conteo que consume la aplicación.
-/

namespace PaperIV.OwnerCoinMoments

open Finset
open PaperIV.EighthMoment
open PaperIV.OwnerCoins

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-! ## 0. Dos utilidades sobre `FinProb` -/

/-- La probabilidad de un suceso es la esperanza de su indicador. -/
theorem prob_eq_expect_indicator (P : FinProb Ω) (s : Finset Ω) :
    P.prob s = P.expect (fun ω => if ω ∈ s then (1 : ℚ) else 0) := by
  classical
  unfold FinProb.prob FinProb.expect
  rw [← Finset.sum_filter_add_sum_filter_not (univ : Finset Ω) (fun ω => ω ∈ s)]
  have h1 : ∀ ω ∈ univ.filter (fun ω => ω ∈ s), P.w ω * (if ω ∈ s then (1 : ℚ) else 0)
      = P.w ω := by
    intro ω hω
    rw [if_pos (Finset.mem_filter.1 hω).2, mul_one]
  have h2 : ∀ ω ∈ univ.filter (fun ω => ¬ ω ∈ s), P.w ω * (if ω ∈ s then (1 : ℚ) else 0)
      = 0 := by
    intro ω hω
    rw [if_neg (Finset.mem_filter.1 hω).2, mul_zero]
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, Finset.sum_const_zero, add_zero]
  congr 1
  ext ω
  simp

omit [DecidableEq Ω] in
/-- El desarrollo del cuadrado de la desviación. -/
theorem expect_sq_dev (P : FinProb Ω) (X : Ω → ℚ) (μ : ℚ) :
    P.expect (fun ω => (X ω - μ) ^ 2)
      = P.expect (fun ω => (X ω) ^ 2) - 2 * μ * P.expect X + μ ^ 2 := by
  classical
  have hterm : ∀ ω : Ω, P.w ω * (X ω - μ) ^ 2
      = P.w ω * (X ω) ^ 2 - 2 * μ * (P.w ω * X ω) + μ ^ 2 * P.w ω := by
    intro ω; ring
  show ∑ ω, P.w ω * (X ω - μ) ^ 2 = _
  rw [Finset.sum_congr rfl (fun ω _ => hterm ω), Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, P.w_total, mul_one]
  rfl

/-- **Chebyshev unilateral.**  Si la desviación cuadrática media no pasa de `v`, la
probabilidad de que la variable baje de `μ − z` no pasa de `v/z²`. -/
theorem lower_tail (P : FinProb Ω) (X : Ω → ℚ) (μ v : ℚ) {z : ℚ} (hz : 0 < z)
    (hv : P.expect (fun ω => (X ω - μ) ^ 2) ≤ v) :
    P.prob (univ.filter (fun ω => X ω < μ - z)) ≤ v / z ^ 2 := by
  classical
  have hsub : univ.filter (fun ω => X ω < μ - z)
      ⊆ univ.filter (fun ω => z ^ 2 ≤ (X ω - μ) ^ 2) := by
    intro ω hω
    rw [Finset.mem_filter] at hω ⊢
    refine ⟨Finset.mem_univ ω, ?_⟩
    have h : X ω - μ < -z := by linarith [hω.2]
    nlinarith [h, hz]
  calc P.prob (univ.filter (fun ω => X ω < μ - z))
      ≤ P.prob (univ.filter (fun ω => z ^ 2 ≤ (X ω - μ) ^ 2)) := P.prob_mono hsub
    _ ≤ P.expect (fun ω => (X ω - μ) ^ 2) / z ^ 2 :=
        P.markov (fun ω => sq_nonneg _) (by positivity)
    _ ≤ v / z ^ 2 := by
        exact div_le_div_of_nonneg_right hv (by positivity)

/-! ## 1. Productos de indicadores -/

variable {ρ V : Type*} [Fintype ρ] [DecidableEq ρ] [Fintype V] [DecidableEq V]

omit [Fintype V] in
/-- Un producto de indicadores es el indicador de «todas las monedas del bloque valen `σ`». -/
theorem prod_ind_eq_if (ω : ρ → V) (S : Finset ρ) (σ : V) :
    (∏ f ∈ S, (if ω f = σ then (1 : ℚ) else 0)) = if ∀ f ∈ S, ω f = σ then 1 else 0 := by
  classical
  by_cases h : ∀ f ∈ S, ω f = σ
  · rw [if_pos h]
    exact Finset.prod_eq_one (fun f hf => by rw [if_pos (h f hf)])
  · rw [if_neg h]
    push_neg at h
    obtain ⟨f, hf, hne⟩ := h
    exact Finset.prod_eq_zero hf (by rw [if_neg hne])

omit [Fintype V] in
/-- **Idempotencia.**  El producto de los indicadores de dos bloques es el indicador de su
unión. -/
theorem prod_ind_mul (ω : ρ → V) (S T : Finset ρ) (σ : V) :
    (∏ f ∈ S, (if ω f = σ then (1 : ℚ) else 0)) * (∏ f ∈ T, (if ω f = σ then (1 : ℚ) else 0))
      = ∏ f ∈ S ∪ T, (if ω f = σ then (1 : ℚ) else 0) := by
  classical
  rw [prod_ind_eq_if, prod_ind_eq_if, prod_ind_eq_if]
  by_cases hS : ∀ f ∈ S, ω f = σ
  · by_cases hT : ∀ f ∈ T, ω f = σ
    · have hU : ∀ f ∈ S ∪ T, ω f = σ := by
        intro f hf
        rcases Finset.mem_union.1 hf with h | h
        · exact hS f h
        · exact hT f h
      rw [if_pos hS, if_pos hT, if_pos hU, mul_one]
    · have hU : ¬ ∀ f ∈ S ∪ T, ω f = σ :=
        fun hU => hT (fun f hf => hU f (Finset.mem_union_right _ hf))
      rw [if_pos hS, if_neg hT, if_neg hU, mul_zero]
  · have hU : ¬ ∀ f ∈ S ∪ T, ω f = σ :=
      fun hU => hS (fun f hf => hU f (Finset.mem_union_left _ hf))
    rw [if_neg hS, if_neg hU, zero_mul]

/-! ## 2. Media y segundo momento -/

variable (q : ρ → V → ℚ) (hnn : ∀ e j, 0 ≤ q e j) (hsum : ∀ e, ∑ j, q e j = 1)

/-- **La media de un bloque.**  Con moneda uniforme `p` para el valor `σ`, la probabilidad de
que todo el bloque `S` caiga en `σ` es `p^{|S|}`. -/
theorem expect_block {σ : V} {p : ℚ} (hp : ∀ f : ρ, q f σ = p) (S : Finset ρ) :
    (coinSpace q hnn hsum).expect (fun ω => ∏ f ∈ S, (if ω f = σ then (1 : ℚ) else 0))
      = p ^ S.card := by
  rw [expect_indicator q hnn hsum S (fun _ => σ),
    Finset.prod_congr rfl (fun f _ => hp f), Finset.prod_const]

variable {ι : Type*} [DecidableEq ι]

/-- El conteo: cuántos bloques de la familia han caído enteros en `σ`. -/
def blockCount (S : ι → Finset ρ) (σ : V) (T : Finset ι) (ω : ρ → V) : ℚ :=
  ∑ i ∈ T, ∏ f ∈ S i, (if ω f = σ then (1 : ℚ) else 0)

omit [DecidableEq ι] in
/-- **La media del conteo.** -/
theorem expect_count {σ : V} {p : ℚ} (hp : ∀ f : ρ, q f σ = p) (S : ι → Finset ρ)
    (T : Finset ι) :
    (coinSpace q hnn hsum).expect (blockCount S σ T) = ∑ i ∈ T, p ^ (S i).card := by
  unfold blockCount
  rw [(coinSpace q hnn hsum).expect_sum T
    (fun i ω => ∏ f ∈ S i, (if ω f = σ then (1 : ℚ) else 0))]
  exact Finset.sum_congr rfl (fun i _ => expect_block q hnn hsum hp (S i))

omit [DecidableEq ι] in
/-- **El segundo momento del conteo.**  Aquí está la correlación: el término `(i,j)` es
`p^{|S i ∪ S j|}`, que sólo se factoriza cuando los bloques son disjuntos. -/
theorem expect_count_sq {σ : V} {p : ℚ} (hp : ∀ f : ρ, q f σ = p) (S : ι → Finset ρ)
    (T : Finset ι) :
    (coinSpace q hnn hsum).expect (fun ω => (blockCount S σ T ω) ^ 2)
      = ∑ i ∈ T, ∑ j ∈ T, p ^ (S i ∪ S j).card := by
  classical
  have hsq : ∀ ω : ρ → V, (blockCount S σ T ω) ^ 2
      = ∑ i ∈ T, ∑ j ∈ T, ∏ f ∈ S i ∪ S j, (if ω f = σ then (1 : ℚ) else 0) := by
    intro ω
    unfold blockCount
    rw [sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl
      (fun j _ => prod_ind_mul ω (S i) (S j) σ))
  have hfun : (fun ω => (blockCount S σ T ω) ^ 2)
      = fun ω => ∑ i ∈ T, ∑ j ∈ T, ∏ f ∈ S i ∪ S j, (if ω f = σ then (1 : ℚ) else 0) :=
    funext hsq
  rw [hfun, (coinSpace q hnn hsum).expect_sum T
    (fun i ω => ∑ j ∈ T, ∏ f ∈ S i ∪ S j, (if ω f = σ then (1 : ℚ) else 0))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [(coinSpace q hnn hsum).expect_sum T
    (fun j ω => ∏ f ∈ S i ∪ S j, (if ω f = σ then (1 : ℚ) else 0))]
  exact Finset.sum_congr rfl (fun j _ => expect_block q hnn hsum hp (S i ∪ S j))


/-! ## 3. La varianza: sólo cuentan los pares no disjuntos -/

/-- Los pares ordenados de bloques que **comparten** algún recurso. -/
def meetingPairs (S : ι → Finset ρ) (T : Finset ι) : Finset (ι × ι) :=
  (T ×ˢ T).filter (fun x => ¬ Disjoint (S x.1) (S x.2))

omit [DecidableEq ι] in
/-- **La cota de varianza.**  Los pares disjuntos contribuyen exactamente cero; los demás,
a lo sumo `p^k` cada uno. -/
theorem variance_le {σ : V} {p : ℚ} (hp : ∀ f : ρ, q f σ = p) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (S : ι → Finset ρ) (T : Finset ι) {k : ℕ} (hk : ∀ i ∈ T, (S i).card = k) :
    (coinSpace q hnn hsum).expect
        (fun ω => (blockCount S σ T ω - ∑ i ∈ T, p ^ (S i).card) ^ 2)
      ≤ ((meetingPairs S T).card : ℚ) * p ^ k := by
  classical
  set P := coinSpace q hnn hsum with hP
  set μ : ℚ := ∑ i ∈ T, p ^ (S i).card with hμ
  rw [expect_sq_dev P (blockCount S σ T) μ, expect_count q hnn hsum hp S T, ← hμ,
    expect_count_sq q hnn hsum hp S T]
  -- `μ²` es la suma de los términos factorizados
  have hμsq : μ ^ 2 = ∑ i ∈ T, ∑ j ∈ T, p ^ ((S i).card + (S j).card) := by
    rw [hμ, sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => (pow_add p _ _).symm))
  -- la diferencia es una suma sobre pares ordenados
  have hsplit : ∑ x ∈ T ×ˢ T,
        (p ^ (S x.1 ∪ S x.2).card - p ^ ((S x.1).card + (S x.2).card))
      = (∑ i ∈ T, ∑ j ∈ T, p ^ (S i ∪ S j).card) - μ ^ 2 := by
    have h1 : ∑ x ∈ T ×ˢ T, p ^ (S x.1 ∪ S x.2).card
        = ∑ i ∈ T, ∑ j ∈ T, p ^ (S i ∪ S j).card :=
      Finset.sum_product T T (fun x : ι × ι => p ^ (S x.1 ∪ S x.2).card)
    have h2 : ∑ x ∈ T ×ˢ T, p ^ ((S x.1).card + (S x.2).card)
        = ∑ i ∈ T, ∑ j ∈ T, p ^ ((S i).card + (S j).card) :=
      Finset.sum_product T T (fun x : ι × ι => p ^ ((S x.1).card + (S x.2).card))
    rw [Finset.sum_sub_distrib, hμsq, h1, h2]
  -- los pares que se cortan son los únicos que contribuyen
  have hbound : ∀ x ∈ meetingPairs S T,
      p ^ (S x.1 ∪ S x.2).card - p ^ ((S x.1).card + (S x.2).card) ≤ p ^ k := by
    intro x hx
    have hx' := Finset.mem_filter.1 hx
    have hmem := Finset.mem_product.1 hx'.1
    have hk1 : (S x.1).card = k := hk x.1 hmem.1
    have hle : k ≤ (S x.1 ∪ S x.2).card := by
      rw [← hk1]
      exact Finset.card_le_card Finset.subset_union_left
    have h1 : p ^ (S x.1 ∪ S x.2).card ≤ p ^ k := pow_le_pow_of_le_one hp0 hp1 hle
    have h2 : (0 : ℚ) ≤ p ^ ((S x.1).card + (S x.2).card) := by positivity
    linarith
  have hmeet : ∑ x ∈ meetingPairs S T,
      (p ^ (S x.1 ∪ S x.2).card - p ^ ((S x.1).card + (S x.2).card))
      ≤ ((meetingPairs S T).card : ℚ) * p ^ k := by
    calc ∑ x ∈ meetingPairs S T,
          (p ^ (S x.1 ∪ S x.2).card - p ^ ((S x.1).card + (S x.2).card))
        ≤ (meetingPairs S T).card • p ^ k := Finset.sum_le_card_nsmul _ _ _ hbound
      _ = ((meetingPairs S T).card : ℚ) * p ^ k := by rw [nsmul_eq_mul]
  have hpairs : ∑ x ∈ T ×ˢ T,
      (p ^ (S x.1 ∪ S x.2).card - p ^ ((S x.1).card + (S x.2).card))
      ≤ ((meetingPairs S T).card : ℚ) * p ^ k := by
    rw [← Finset.sum_filter_add_sum_filter_not (T ×ˢ T)
      (fun x => ¬ Disjoint (S x.1) (S x.2))]
    have hzero : ∑ x ∈ (T ×ˢ T).filter (fun x => ¬ ¬ Disjoint (S x.1) (S x.2)),
        (p ^ (S x.1 ∪ S x.2).card - p ^ ((S x.1).card + (S x.2).card)) = 0 := by
      refine Finset.sum_eq_zero (fun x hx => ?_)
      have hd : Disjoint (S x.1) (S x.2) := not_not.1 (Finset.mem_filter.1 hx).2
      rw [Finset.card_union_of_disjoint hd, sub_self]
    rw [hzero, add_zero]
    exact hmeet
  rw [hsplit] at hpairs
  have hsqμ : μ * μ = μ ^ 2 := (sq μ).symm
  linarith

/-- **Chebyshev unilateral, por arriba.**  Espejo exacto de `lower_tail`: la misma varianza
sirve para las dos colas.

Es lo que la poda de `OwnerLayerBridge.trimmedLayer` necesita para acotar el número de aristas
de grado excesivo. -/
theorem upper_tail (P : FinProb Ω) (X : Ω → ℚ) (μ v : ℚ) {z : ℚ} (hz : 0 < z)
    (hv : P.expect (fun ω => (X ω - μ) ^ 2) ≤ v) :
    P.prob (univ.filter (fun ω => μ + z < X ω)) ≤ v / z ^ 2 := by
  classical
  have hsub : univ.filter (fun ω => μ + z < X ω)
      ⊆ univ.filter (fun ω => z ^ 2 ≤ (X ω - μ) ^ 2) := by
    intro ω hω
    rw [Finset.mem_filter] at hω ⊢
    refine ⟨Finset.mem_univ ω, ?_⟩
    have h : z < X ω - μ := by linarith [hω.2]
    nlinarith [h, hz]
  calc P.prob (univ.filter (fun ω => μ + z < X ω))
      ≤ P.prob (univ.filter (fun ω => z ^ 2 ≤ (X ω - μ) ^ 2)) := P.prob_mono hsub
    _ ≤ P.expect (fun ω => (X ω - μ) ^ 2) / z ^ 2 :=
        P.markov (fun ω => sq_nonneg _) (by positivity)
    _ ≤ v / z ^ 2 := by
        exact div_le_div_of_nonneg_right hv (by positivity)

end PaperIV.OwnerCoinMoments

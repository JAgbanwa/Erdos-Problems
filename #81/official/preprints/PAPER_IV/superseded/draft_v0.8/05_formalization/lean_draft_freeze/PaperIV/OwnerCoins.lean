import PaperIV.CyclicLayering

/-!
# Monedas por arista y cancelación de densidades (RC01 §15.4 y §16.1)

## §15.4 — el espacio de monedas

> Independientemente para cada arista real `e ∈ E(V_i,V_j)`, elija un propietario activo
> `σ ⊇ {i,j}` con probabilidad `α_σ/d_ij`.  La probabilidad sobrante significa «sin
> propietario».  (15.5) demuestra que la distribución es válida.

Aquí eso es:

* `ownerDist` — la distribución por arista sobre `Option π`, con `none` = «sin propietario»
  recogiendo la masa sobrante.  `ownerDist_sum` demuestra que es válida **usando exactamente
  (15.5)**, la desigualdad `∑_σ α_σ/d_ij ≤ 1`;
* `coinSpace` — el producto sobre las aristas, como `FinProb (ρ → κ)`.  Que los pesos sumen
  `1` es `Finset.prod_univ_sum` con `Fintype.piFinset_univ`.

La advertencia de la fuente —*«no se renormalizan probabilidades después de descartar patrones
ni raíces»*— se respeta por construcción: la masa descartada va a `none`, no se reparte.

## §16.1 — la cancelación

* `expect_indicator` — **la factorización del producto**: la esperanza del producto de
  indicadores sobre un conjunto `S` de aristas es el producto de las probabilidades.  Es la
  independencia, y sale del mismo `prod_univ_sum`;
* `prob_all_owned` — con `q_f(σ) = α/d_f`, la probabilidad de que **todo** el soporte elija
  `σ` es `α^{|S|}/∏_{f∈S} d_f`;
* `cond_all_owned` — dividiendo por la moneda de la raíz, **las densidades se cancelan**:

```
α^{|S|}/∏_{f∈S} d_f  ÷  (α/d_{e₀})  =  α^{|S|−1}/∏_{f ∈ S∖{e₀}} d_f.
```

Ésa es la ecuación (16.2) de la fuente, en su forma algebraica exacta: la esperanza
condicionada del grado es `c'_e` veces esa cantidad, y el factor `∏_{ab≠ij} d_ab` que aparece
en `A_ij` es justo el denominador que queda.
-/

namespace PaperIV.OwnerCoins

open Finset
open PaperIV.EighthMoment

/-! ## 1. La distribución por arista (§15.4) -/

variable {π : Type*} [Fintype π] [DecidableEq π]

/-- La elección de propietario de una arista: los patrones activos con su probabilidad, y
`none` para «sin propietario», que recoge la masa sobrante. -/
def ownerDist (Act : Finset π) (p : π → ℚ) : Option π → ℚ
  | some σ => if σ ∈ Act then p σ else 0
  | none => 1 - ∑ σ ∈ Act, p σ

theorem ownerDist_nonneg {Act : Finset π} {p : π → ℚ} (hp : ∀ σ, 0 ≤ p σ)
    (hle : ∑ σ ∈ Act, p σ ≤ 1) : ∀ j, 0 ≤ ownerDist Act p j := by
  intro j
  cases j with
  | none => simpa [ownerDist] using hle
  | some σ =>
    simp only [ownerDist]
    by_cases h : σ ∈ Act
    · rw [if_pos h]; exact hp σ
    · rw [if_neg h]

/-- **La distribución es válida**, y lo es por (15.5): la masa asignada no pasa de `1`. -/
theorem ownerDist_sum (Act : Finset π) (p : π → ℚ) :
    ∑ j : Option π, ownerDist Act p j = 1 := by
  classical
  rw [Fintype.sum_option]
  have hsome : ∑ σ : π, ownerDist Act p (some σ) = ∑ σ ∈ Act, p σ := by
    simp only [ownerDist]
    rw [← Finset.sum_filter]
    congr 1
    ext σ
    simp
  rw [hsome]
  simp [ownerDist]

/-! ## 2. El espacio producto de monedas -/

variable {ρ κ : Type*} [Fintype ρ] [DecidableEq ρ] [Fintype κ] [DecidableEq κ]

/-- **El espacio de monedas.**  Una elección independiente por arista. -/
noncomputable def coinSpace (q : ρ → κ → ℚ) (hnn : ∀ e j, 0 ≤ q e j)
    (hsum : ∀ e, ∑ j, q e j = 1) : FinProb (ρ → κ) where
  w := fun ω => ∏ e, q e (ω e)
  w_nonneg := fun ω => Finset.prod_nonneg (fun e _ => hnn e (ω e))
  w_total := by
    classical
    have h := Finset.prod_univ_sum (fun _ : ρ => (univ : Finset κ)) (fun e j => q e j)
    rw [Fintype.piFinset_univ] at h
    rw [← h, Finset.prod_congr rfl (fun e _ => hsum e), Finset.prod_const_one]

/-- **La factorización (independencia).**  La esperanza del producto de indicadores sobre un
conjunto `S` de aristas es el producto de las probabilidades correspondientes. -/
theorem expect_indicator (q : ρ → κ → ℚ) (hnn : ∀ e j, 0 ≤ q e j)
    (hsum : ∀ e, ∑ j, q e j = 1) (S : Finset ρ) (c : ρ → κ) :
    (coinSpace q hnn hsum).expect
        (fun ω => ∏ e ∈ S, (if ω e = c e then (1 : ℚ) else 0))
      = ∏ e ∈ S, q e (c e) := by
  classical
  show ∑ ω : ρ → κ, (∏ e, q e (ω e)) * (∏ e ∈ S, (if ω e = c e then (1 : ℚ) else 0)) = _
  have key : ∀ ω : ρ → κ,
      (∏ e, q e (ω e)) * (∏ e ∈ S, (if ω e = c e then (1 : ℚ) else 0))
        = ∏ e, (q e (ω e) * (if e ∈ S then (if ω e = c e then (1 : ℚ) else 0) else 1)) := by
    intro ω
    rw [Finset.prod_mul_distrib]
    congr 1
    rw [← Finset.prod_filter]
    congr 1
    ext e
    simp
  rw [Finset.sum_congr rfl (fun ω _ => key ω)]
  have hps := Finset.prod_univ_sum (fun _ : ρ => (univ : Finset κ))
    (fun e j => q e j * (if e ∈ S then (if j = c e then (1 : ℚ) else 0) else 1))
  rw [Fintype.piFinset_univ] at hps
  rw [← hps]
  · have hrhs : ∏ e ∈ S, q e (c e) = ∏ e : ρ, (if e ∈ S then q e (c e) else 1) := by
      rw [← Finset.prod_filter]
      congr 1
      ext e
      simp
    rw [hrhs]
    refine Finset.prod_congr rfl ?_
    intro e _
    by_cases he : e ∈ S
    · simp only [if_pos he]
      have hterm : ∀ j : κ, q e j * (if j = c e then (1 : ℚ) else 0)
          = (if j = c e then q e j else 0) := by
        intro j
        by_cases h : j = c e <;> simp [h]
      rw [Finset.sum_congr rfl (fun j _ => hterm j)]
      rw [Finset.sum_ite_eq' univ (c e) (fun j => q e j)]
      simp
    · simp only [if_neg he, mul_one]
      exact hsum e

/-! ## 3. La cancelación de densidades (§16.1) -/

/-- **(16.2), primera mitad.**  Con `q_f(σ) = α/d_f`, la probabilidad de que todo el soporte
`S` elija `σ` es `α^{|S|}/∏_{f∈S} d_f`. -/
theorem prob_all_owned (q : ρ → κ → ℚ) (hnn : ∀ e j, 0 ≤ q e j)
    (hsum : ∀ e, ∑ j, q e j = 1) (S : Finset ρ) (σ : κ) (α : ℚ) (dd : ρ → ℚ)
    (hq : ∀ f ∈ S, q f σ = α / dd f) :
    (coinSpace q hnn hsum).expect
        (fun ω => ∏ e ∈ S, (if ω e = σ then (1 : ℚ) else 0))
      = α ^ S.card / ∏ f ∈ S, dd f := by
  classical
  rw [expect_indicator q hnn hsum S (fun _ => σ)]
  rw [Finset.prod_congr rfl hq]
  rw [Finset.prod_div_distrib, Finset.prod_const]

/-- **(16.2), la cancelación.**  Al condicionar en la moneda de la raíz, las densidades
originales se cancelan y queda `α^{ℓ−1}` dividido por las densidades de las parejas
restantes. -/
theorem cond_all_owned (S : Finset ρ) (e₀ : ρ) (he₀ : e₀ ∈ S) (α : ℚ) (dd : ρ → ℚ)
    (hα : α ≠ 0) (hd : ∀ f ∈ S, dd f ≠ 0) :
    (α ^ S.card / ∏ f ∈ S, dd f) / (α / dd e₀)
      = α ^ (S.card - 1) / ∏ f ∈ S.erase e₀, dd f := by
  classical
  have hsplit : ∏ f ∈ S, dd f = dd e₀ * ∏ f ∈ S.erase e₀, dd f :=
    (Finset.mul_prod_erase S dd he₀).symm
  have hprod : ∏ f ∈ S.erase e₀, dd f ≠ 0 :=
    Finset.prod_ne_zero_iff.2 (fun f hf => hd f (Finset.mem_of_mem_erase hf))
  have hd0 : dd e₀ ≠ 0 := hd e₀ he₀
  obtain ⟨m, hm⟩ : ∃ m, S.card = m + 1 :=
    ⟨S.card - 1, by have := Finset.card_pos.2 (⟨e₀, he₀⟩ : S.Nonempty); omega⟩
  rw [hm, Nat.add_sub_cancel, hsplit, pow_succ]
  field_simp

end PaperIV.OwnerCoins

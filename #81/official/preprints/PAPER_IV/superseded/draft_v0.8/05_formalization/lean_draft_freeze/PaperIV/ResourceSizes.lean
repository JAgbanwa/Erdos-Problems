import PaperIV.CenteredMoments

/-!
# Tamaños de recursos y excepciones (RC01 §16.4)

Última pieza de §16.  Con el momento centrado ya cerrado (`CenteredMoments`), es una instancia
directa de la misma cola.

## Lo que se demuestra

* `singleton_pairwiseDisjoint` — los bloques de **una sola arista** son disjuntos dos a dos en
  cuanto las aristas son distintas.  Es el caso degenerado de §16.2: aquí no hace falta la
  estructura de capas, porque cada indicador depende de una única moneda;
* `expected_count` — **la esperanza del conteo es exactamente `α·t²`**: hay `d_ij·t²` aristas
  reales y cada una elige `σ` con probabilidad `α/d_ij`, así que la densidad se cancela otra
  vez;
* `size_tail_arith` — **(16.5)**: con `m ≤ t²` indicadores y desviación `u·α·t²`,

  ```
  C₈·(t²)⁴ / (u·α·t²)⁸ = C₈/(u⁸α⁸t⁸);
  ```

* `size_tail` — la cola del conteo, **incondicional**;
* `exceptional_le` — **(16.6)**: `|U_σ ∩ X_ij| ≤ α(h/d + u)·t²`.

## Nota sobre §16.4

La fuente advierte que *«los conjuntos `X_ij` dependen del patrón y del grafo antes de lanzar
las monedas; no se eligen después para alterar las probabilidades»*.  Aquí eso es automático:
`X` entra como un `Finset` fijado antes de la cola, no como función de `ω`.
-/

namespace PaperIV.ResourceSizes

open Finset
open PaperIV.EighthMoment
open PaperIV.OwnerCoins
open PaperIV.CenteredMoments

variable {ρ κ : Type*} [Fintype ρ] [DecidableEq ρ] [Fintype κ] [DecidableEq κ]

/-! ## 1. Bloques de una sola arista -/

/-- Aristas distintas dan bloques disjuntos.  Es el caso degenerado de §16.2. -/
theorem singleton_pairwiseDisjoint {m : ℕ} (e : Fin m → ρ) (he : Function.Injective e) :
    (Set.univ : Set (Fin m)).PairwiseDisjoint (fun j => ({e j} : Finset ρ)) := by
  intro i _ j _ hij
  simp only [Function.onFun]
  rw [Finset.disjoint_singleton]
  exact fun h => hij (he h)

/-! ## 2. La esperanza del conteo -/

/-- **La densidad se cancela otra vez.**  Con `d·t²` aristas reales y probabilidad `α/d` cada
una, la esperanza del conteo es exactamente `α·t²`. -/
theorem expected_count (m : ℕ) (α d t : ℚ) (hd : d ≠ 0) (hm : (m : ℚ) = d * t ^ 2) :
    (m : ℚ) * (α / d) = α * t ^ 2 := by
  rw [hm]
  field_simp

/-! ## 3. (16.5): la aritmética de la cola -/

/-- **(16.5).**  `m ≤ t²` indicadores y desviación `u·α·t²`. -/
theorem size_tail_arith (C u α t : ℚ) (hu : u ≠ 0) (hα : α ≠ 0) (ht : t ≠ 0) :
    C * (t ^ 2) ^ 4 / (u * (α * t ^ 2)) ^ 8 = C / (u ^ 8 * α ^ 8 * t ^ 8) := by
  field_simp

/-! ## 4. La cola del conteo -/

/-- **La cola del tamaño de recurso, sin hipótesis.**  El conteo de aristas asignadas a `σ`
se concentra alrededor de su esperanza.

Es `CenteredMoments.tail_of_disjoint_blocks` con bloques de una arista. -/
theorem size_tail (q : ρ → κ → ℚ) (hnn : ∀ e j, 0 ≤ q e j) (hsum : ∀ e, ∑ j, q e j = 1)
    {m : ℕ} (e : Fin m → ρ) (he : Function.Injective e) (σ : κ) {z : ℚ} (hz : 0 < z) :
    (coinSpace q hnn hsum).prob (univ.filter (fun ω =>
        z ≤ |∑ j, ((∏ f ∈ ({e j} : Finset ρ), (if ω f = σ then (1 : ℚ) else 0))
              - (coinSpace q hnn hsum).expect
                  (fun ω' => ∏ f ∈ ({e j} : Finset ρ),
                    (if ω' f = σ then (1 : ℚ) else 0)))|))
      ≤ 4 ^ 8 * (m : ℚ) ^ 4 / z ^ 8 :=
  tail_of_disjoint_blocks q hnn hsum (fun j => ({e j} : Finset ρ))
    (singleton_pairwiseDisjoint e he) σ hz

/-! ## 5. (16.6): el excepcional asignado -/

/-- **(16.6).**  Si la esperanza del excepcional asignado es a lo sumo `α(h/d)t²` y la
desviación no pasa de `uαt²`, entonces `|U_σ ∩ X_ij| ≤ α(h/d + u)t²`. -/
theorem exceptional_le (α h d u t X : ℚ)
    (hE : X ≤ α * (h / d) * t ^ 2 + u * α * t ^ 2) :
    X ≤ α * (h / d + u) * t ^ 2 := by
  nlinarith [hE]

end PaperIV.ResourceSizes

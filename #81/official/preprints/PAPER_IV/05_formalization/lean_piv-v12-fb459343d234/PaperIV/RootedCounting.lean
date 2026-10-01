import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Data.Rat.Star
import Mathlib.Tactic.Positivity

/-!
# El conteo enraizado de segundo momento: la reducción exacta

Primera pieza del puente **GAP-RP01** (regularidad + nibble casi perfecto ⟹ transferencia
subcuadrática). Aísla, como identidad algebraica exacta, **qué** tiene que suministrar el
lema de conteo y **cuánto** se puede tolerar de error.

## El enunciado que GAP-RP01 necesita

Fijada una pareja raíz `(V_i, V_j)` de una partición regular y un patrón de `r` partes con
`ℓ = C(r,2)` parejas, para cada arista física `e ∈ E(V_i,V_j)` sea `c e` el número de copias
transversales del patrón que contienen `e`, y sea
```
A = t^(r-2) · ∏_{ab ≠ ij} d_ab
```
la escala esperada. Hace falta
```
∑_{e ∈ E(V_i,V_j)} (c e − A)²  ≤  (error pequeño).
```

## La reducción, que es lo que se demuestra aquí

`second_moment_of_counts`: la desviación de segundo momento se expresa **exactamente**
mediante dos errores de conteo, y los términos principales **se cancelan sin dejar resto**:

```
∑ (c e − A)²  =  E₂ − 2·A·E₁
```
donde
* `E₁ = ∑ c e − A·|E|` es el error del conteo de **copias** del patrón;
* `E₂ = ∑ (c e)² − A²·|E|` es el error del conteo de **pares de copias que comparten la
  arista raíz**.

Esto reduce el lema de conteo enraizado a **dos** estimaciones estándar de conteo —una para
el patrón, otra para el patrón duplicado sobre la raíz— y da la aritmética del error:
```
∑ (c e − A)² ≤ N₂ + 2·|A|·N₁.
```

En GAP-RP01 ambas se obtienen del lema de conteo usual por telescopado de productos de
indicadores, con error total `(4ℓ−1)·δ·t^(2r−2) ≤ 23·δ·t^(2r−2)` para `ℓ ≤ 6`.

## Qué hay ya en Mathlib, y qué no

Mathlib **sí** tiene conteo de triángulos y el lema de eliminación —
`Mathlib/Combinatorics/SimpleGraph/Triangle/Counting.lean` y `Removal.lean`, de Yaël
Dillies y Bhavik Mehta— además de `szemeredi_regularity`. Pero `triangle_counting'` es
```
(1 − 2ε)·ε³·|s|·|t|·|u|  ≤  #{triángulos en s × t × u},
```
es decir **unilateral**, **no enraizado**, con constante `(1−2ε)ε³` en lugar del producto de
densidades, y sólo para `K₃`.

Lo que falta para GAP-RP01 es la versión **bilateral, enraizada y con el producto de
densidades**, para `K₃` **y** `K₄`. La infraestructura de Dillies–Mehta (`IsUniform`,
`edgeDensity`, `badVertices`, el patrón de `triangle_split_helper`) es el andamio natural
sobre el que construirla, y su artículo *Formalising Szemerédi's Regularity Lemma in Lean*
(ITP 2022, citado en el propio fuente de Mathlib como `[srl_itp]`) es la guía de
formalización.

## Corrección de constante en GAP-RP01

La constante `h` de su paso (9) omite un factor `ℓ`: las copias retiradas rebajan el conteo
enraizado de **sus `ℓ` raíces**, no de una. El recuento correcto da
```
h = b·(1 + 36/(u·d⁵))      en lugar de      h = b·(1 + 6/(u·d⁵)),
```
y por tanto la elección de parámetros pasa de `δ ≤ ξu³d¹⁶/3220` a
**`δ ≤ ξu³d¹⁶/19320`**. Verificado numéricamente: con esa `δ` se cumple `h ≤ ξd/20` en todo
el rango de parámetros probado. **No es fatal** —se absorbe con `δ` seis veces menor— pero
hay que rehacer §6 de la prueba con ella.
-/

namespace PaperIV.RootedCounting

open Finset

variable {ρ : Type*} [DecidableEq ρ]

/-- **La identidad de segundo momento.**  Los términos principales se cancelan **sin dejar
resto**: la desviación cuadrática es exactamente el error del conteo de pares menos el doble
del error del conteo simple, escalado por `A`. -/
theorem second_moment_eq (E : Finset ρ) (c : ρ → ℚ) (A : ℚ) :
    ∑ x ∈ E, (c x - A) ^ 2
      = (∑ x ∈ E, (c x) ^ 2 - A ^ 2 * (E.card : ℚ))
        - 2 * A * ((∑ x ∈ E, c x) - A * (E.card : ℚ)) := by
  have hexp : ∀ x, (c x - A) ^ 2 = (c x) ^ 2 - 2 * A * c x + A ^ 2 := by
    intro x; ring
  rw [Finset.sum_congr rfl (fun x _ => hexp x)]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
    nsmul_eq_mul]
  ring

/-- **La reducción.**  Con `N₁` acotando el error del conteo de copias y `N₂` el de pares de
copias que comparten la raíz, el segundo momento queda acotado.

Ésta es la forma en que el lema de conteo enraizado se reduce a **dos** estimaciones
estándar. -/
theorem second_moment_of_counts (E : Finset ρ) (c : ρ → ℚ) (A N₁ N₂ : ℚ)
    (h₁ : |(∑ x ∈ E, c x) - A * (E.card : ℚ)| ≤ N₁)
    (h₂ : |∑ x ∈ E, (c x) ^ 2 - A ^ 2 * (E.card : ℚ)| ≤ N₂) :
    ∑ x ∈ E, (c x - A) ^ 2 ≤ N₂ + 2 * |A| * N₁ := by
  rw [second_moment_eq E c A]
  have hb₁ := abs_le.1 h₁
  have hb₂ := abs_le.1 h₂
  have hsimple : A * ((∑ x ∈ E, c x) - A * (E.card : ℚ)) ≤ |A| * N₁ := by
    calc A * ((∑ x ∈ E, c x) - A * (E.card : ℚ))
        ≤ |A * ((∑ x ∈ E, c x) - A * (E.card : ℚ))| := le_abs_self _
      _ = |A| * |(∑ x ∈ E, c x) - A * (E.card : ℚ)| := abs_mul _ _
      _ ≤ |A| * N₁ := mul_le_mul_of_nonneg_left h₁ (abs_nonneg A)
  have hneg : -(|A| * N₁) ≤ A * ((∑ x ∈ E, c x) - A * (E.card : ℚ)) := by
    have : -|A * ((∑ x ∈ E, c x) - A * (E.card : ℚ))|
        ≤ A * ((∑ x ∈ E, c x) - A * (E.card : ℚ)) := neg_abs_le _
    calc -(|A| * N₁) ≤ -|A * ((∑ x ∈ E, c x) - A * (E.card : ℚ))| := by
          rw [abs_mul]
          exact neg_le_neg (mul_le_mul_of_nonneg_left h₁ (abs_nonneg A))
      _ ≤ _ := this
  linarith [hb₂.2, hneg]

/-- **La cota de mala raíz.**  Si el segundo momento está acotado por `S`, el número de
raíces cuya desviación relativa excede `u` es a lo sumo `S / (u·A)²`.

Es el paso (8) de GAP-RP01: de la cota de segundo momento a la cota de cardinal del conjunto
de raíces malas. -/
theorem card_bad_roots_le (E : Finset ρ) (c : ρ → ℚ) (A u S : ℚ)
    (hu : 0 < u) (hA : 0 < A)
    (hS : ∑ x ∈ E, (c x - A) ^ 2 ≤ S) :
    ((E.filter (fun x => u * A < |c x - A|)).card : ℚ) * (u * A) ^ 2 ≤ S := by
  classical
  have hstep : ∀ x ∈ E.filter (fun x => u * A < |c x - A|), (u * A) ^ 2 ≤ (c x - A) ^ 2 := by
    intro x hx
    rw [Finset.mem_filter] at hx
    have h1 : u * A ≤ |c x - A| := le_of_lt hx.2
    have h2 : (0 : ℚ) ≤ u * A := le_of_lt (mul_pos hu hA)
    calc (u * A) ^ 2 ≤ |c x - A| ^ 2 := by nlinarith
      _ = (c x - A) ^ 2 := sq_abs _
  calc ((E.filter (fun x => u * A < |c x - A|)).card : ℚ) * (u * A) ^ 2
      = ∑ _x ∈ E.filter (fun x => u * A < |c x - A|), (u * A) ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ x ∈ E.filter (fun x => u * A < |c x - A|), (c x - A) ^ 2 :=
        Finset.sum_le_sum hstep
    _ ≤ ∑ x ∈ E, (c x - A) ^ 2 := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
        intro x _ _; positivity
    _ ≤ S := hS

end PaperIV.RootedCounting

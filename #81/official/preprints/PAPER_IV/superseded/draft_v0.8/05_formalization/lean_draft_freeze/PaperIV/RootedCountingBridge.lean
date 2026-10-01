import PaperIV.RootedCounting

/-!
# Los dos momentos son conteos de patrón: una sola estimación basta

Segunda pieza de **GAP-RP01**.  `RootedCounting.second_moment_of_counts` redujo el conteo
enraizado a dos errores, `N₁` (conteo de copias) y `N₂` (conteo de pares de copias con la
misma raíz).  Aquí se demuestra que **ambos son conteos de copias de un patrón**, de modo que
hace falta **un solo** lema de conteo y no dos:

* `sum_fiber_card` — `∑_e c e = #copias`.  El primer momento **es** el conteo del patrón.
* `sum_fiber_card_sq` — `∑_e (c e)² = #{pares ordenados de copias con la misma raíz}`.  El
  segundo momento **es** el conteo del *patrón duplicado sobre la raíz*, un patrón con
  `2r − 2` vértices y `2ℓ − 1` parejas.
* `second_moment_of_pattern_counts` — el enunciado combinado: con una estimación del conteo
  para el patrón y otra para su duplicado, sale la cota de segundo momento.

## Por qué importa

En GAP-RP01 el paso (7) se justifica «por telescopado de productos de indicadores, aplicado
a una clique y a **dos cliques que comparten la arista raíz**».  Lo de aquí lo vuelve
preciso: *dos cliques que comparten la arista raíz* **es** un patrón, luego el paso (7) no
necesita ninguna técnica nueva — necesita el **mismo** lema de conteo, instanciado dos veces.

```
K₃ :  patrón r=3, ℓ=3   →  duplicado: 4 vértices, 5 parejas
K₄ :  patrón r=4, ℓ=6   →  duplicado: 6 vértices, 11 parejas
```

Así que la única obligación externa de esta rama es:

> **Lema de conteo de patrón (pendiente).** Para un patrón fijo `H` sobre partes
> `V_1,…,V_k` de una partición `ε`-regular con densidades `≥ d`,
> ```
> | #copias transversales de H  −  (∏_{ab ∈ H} d_ab) · ∏_a |V_a| |  ≤  C_H · ε · ∏_a |V_a|.
> ```

Mathlib tiene la versión **unilateral, no enraizada y sólo para `K₃`**
(`SimpleGraph.triangle_counting'`, Dillies–Mehta).  La bilateral para patrón general es lo
que falta, y la infraestructura de ese mismo archivo (`IsUniform`, `edgeDensity`,
`badVertices`, `triangle_split_helper`) es el andamio.

## Estado

Lo de aquí está **demostrado**: es combinatoria de fibras, no usa regularidad.  El lema de
conteo de patrón **no** se demuestra aquí; queda enunciado como la única entrada pendiente
de esta rama.
-/

namespace PaperIV.RootedCountingBridge

open Finset

variable {κ ρ : Type*} [DecidableEq κ] [DecidableEq ρ]

/-- La fibra de la raíz `e`: las copias cuya arista raíz es `e`. -/
def fiber (Cs : Finset κ) (root : κ → ρ) (e : ρ) : Finset κ :=
  Cs.filter fun K => root K = e

/-- **Primer momento = conteo de copias.**  Sumar el número de copias sobre las raíces
recupera el total de copias. -/
theorem sum_fiber_card (Cs : Finset κ) (root : κ → ρ) (E : Finset ρ)
    (hroot : ∀ K ∈ Cs, root K ∈ E) :
    ∑ e ∈ E, (fiber Cs root e).card = Cs.card :=
  (Finset.card_eq_sum_card_fiberwise hroot).symm

/-- La fibra del par: los pares ordenados de copias con raíz común `e`. -/
theorem filter_product_eq (Cs : Finset κ) (root : κ → ρ) (e : ρ) :
    ((Cs ×ˢ Cs).filter fun p => root p.1 = root p.2 ∧ root p.1 = e)
      = (fiber Cs root e) ×ˢ (fiber Cs root e) := by
  ext p
  simp only [fiber, Finset.mem_filter, Finset.mem_product]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨⟨h1, h4⟩, ⟨h2, h3 ▸ h4⟩⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨⟨h1, h3⟩, by rw [h2, h4], h2⟩

/-- **Segundo momento = conteo del patrón duplicado.**  La suma de los cuadrados de los
conteos enraizados es exactamente el número de **pares ordenados de copias que comparten la
arista raíz** — es decir, el conteo de copias del patrón duplicado sobre la raíz. -/
theorem sum_fiber_card_sq (Cs : Finset κ) (root : κ → ρ) (E : Finset ρ)
    (hroot : ∀ K ∈ Cs, root K ∈ E) :
    ∑ e ∈ E, (fiber Cs root e).card ^ 2
      = ((Cs ×ˢ Cs).filter fun p => root p.1 = root p.2).card := by
  classical
  have hmem : ∀ p ∈ (Cs ×ˢ Cs).filter (fun p => root p.1 = root p.2), root p.1 ∈ E := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_product] at hp
    exact hroot p.1 hp.1.1
  rw [Finset.card_eq_sum_card_fiberwise hmem]
  refine Finset.sum_congr rfl fun e _ => ?_
  have hset : (((Cs ×ˢ Cs).filter fun p => root p.1 = root p.2).filter fun p => root p.1 = e)
      = (fiber Cs root e) ×ˢ (fiber Cs root e) := by
    rw [Finset.filter_filter]
    exact filter_product_eq Cs root e
  rw [hset, Finset.card_product, sq]

/-- **El enunciado combinado.**  Con una estimación `N₁` del conteo del patrón y otra `N₂`
del conteo del patrón duplicado sobre la raíz, la desviación de segundo momento del conteo
enraizado queda acotada.

Es `RootedCounting.second_moment_of_counts` con las dos entradas ya identificadas como
conteos de patrón. -/
theorem second_moment_of_pattern_counts
    (Cs : Finset κ) (root : κ → ρ) (E : Finset ρ) (A N₁ N₂ : ℚ)
    (hroot : ∀ K ∈ Cs, root K ∈ E)
    (h₁ : |(Cs.card : ℚ) - A * (E.card : ℚ)| ≤ N₁)
    (h₂ : |((((Cs ×ˢ Cs).filter fun p => root p.1 = root p.2).card : ℚ))
            - A ^ 2 * (E.card : ℚ)| ≤ N₂) :
    ∑ e ∈ E, (((fiber Cs root e).card : ℚ) - A) ^ 2 ≤ N₂ + 2 * |A| * N₁ := by
  classical
  refine RootedCounting.second_moment_of_counts E (fun e => ((fiber Cs root e).card : ℚ))
    A N₁ N₂ ?_ ?_
  · have : (∑ e ∈ E, ((fiber Cs root e).card : ℚ)) = (Cs.card : ℚ) := by
      rw [← Nat.cast_sum, sum_fiber_card Cs root E hroot]
    rw [this]; exact h₁
  · have : (∑ e ∈ E, ((fiber Cs root e).card : ℚ) ^ 2)
        = ((((Cs ×ˢ Cs).filter fun p => root p.1 = root p.2).card : ℚ)) := by
      have hnat : ∑ e ∈ E, (fiber Cs root e).card ^ 2
          = ((Cs ×ˢ Cs).filter fun p => root p.1 = root p.2).card :=
        sum_fiber_card_sq Cs root E hroot
      calc (∑ e ∈ E, ((fiber Cs root e).card : ℚ) ^ 2)
          = ((∑ e ∈ E, (fiber Cs root e).card ^ 2 : ℕ) : ℚ) := by push_cast; ring
        _ = _ := by rw [hnat]
    rw [this]; exact h₂

end PaperIV.RootedCountingBridge

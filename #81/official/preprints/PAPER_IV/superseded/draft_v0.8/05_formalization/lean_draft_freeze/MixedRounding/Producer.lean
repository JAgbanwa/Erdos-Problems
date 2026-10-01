import MixedRounding.Lift

/-!
# El transporte de masa (CMR, gate G3)

Segunda pieza de G3: llevar la masa fraccional `x` a pesos sobre el hipergrafo de soportes, y
comprobar cuáles de las hipótesis del nibble salen **gratis**.

## El resultado

El empaquetamiento fraccional **ya es** un matching fraccional del hipergrafo de soportes, y su
carga por vértice —o sea por arista de `G`— es exactamente la carga del LP.  Luego la hipótesis
`carga ≤ 1` del nibble **no hay que demostrarla: es la restricción de capacidad**.

```
∑_{S ∋ e} w S  =  ∑_{K ∋ e} x_K  ≤  1
```

`load_eq` y `load_le_one`.  Y la masa se conserva: `∑_S w S = ∑_K x_K` (`mass_eq`).

El puente entre las dos sumas es `pairs_injOn_items`: sumar sobre soportes y sumar sobre items
es lo mismo porque `pairs` es inyectiva.  Ésa es, otra vez, la propiedad de «no inventamos
cliques», ahora en su forma cuantitativa.

## Qué queda de las hipótesis del nibble

| hipótesis | estado |
|---|---|
| uniformidad `C(k,2)` | **hecha** — `Lift.supportsOfCard_uniform` |
| pesos `≥ 0` | **hecha** — `inducedWeight_nonneg` |
| carga `≤ 1` | **hecha** — `load_le_one`, directa de la capacidad |
| carga `≥ 1−γ` fuera de `Exc` pequeño | **abierta** |
| codegree ponderado `≤ γ` | **abierta** |

Las dos abiertas son las que **no** se siguen del LP: dependen de la partición regular y de la
estructura de patrones.  Son el residuo real de G3, y conviene no disimularlo — un `x`
arbitrario puede tener carga cero en casi toda arista, y entonces la cuarta hipótesis es falsa
sin más.  Lo que la hace cierta es el descarte de §1 más la normalización por patrón, no el
transporte.

## Vértices que no son aristas

El nibble cuantifica sobre **todo** el tipo de vértices, aquí `Sym2 V`, que incluye diagonales
y no-aristas.  Ahí la carga es `0` porque ningún soporte las contiene (`load_eq_zero_of_not_edge`),
así que la hipótesis se cumple trivialmente.  Es un detalle de encaje, pero sin él el puente no
tipa.
-/

namespace MixedRounding

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ## 1. El peso inducido -/

/-- El peso que `x` induce sobre el hipergrafo de soportes: cada soporte hereda el peso de la
clique que determina. -/
noncomputable def inducedWeight (x : FracPacking G) (S : Finset (Sym2 V)) : ℝ :=
  if S ∈ supports G then ((x.weight (cliqueOf S) : ℚ) : ℝ) else 0

theorem inducedWeight_nonneg (x : FracPacking G) (S : Finset (Sym2 V)) :
    0 ≤ inducedWeight x S := by
  rw [inducedWeight]
  split
  · exact_mod_cast x.weight_nonneg _
  · exact le_refl 0

/-- Sobre un soporte real, el peso inducido es el peso de su clique. -/
theorem inducedWeight_pairs (x : FracPacking G) {K : Finset V} (hK : IsItem G K) :
    inducedWeight x (pairs K) = ((x.weight K : ℚ) : ℝ) := by
  have hmem : pairs K ∈ supports G := Finset.mem_image.2 ⟨K, mem_items.2 hK, rfl⟩
  rw [inducedWeight, if_pos hmem, cliqueOf_pairs (two_le_card_of_isItem hK)]

/-! ## 2. Sumar sobre soportes es sumar sobre items -/

/-- Los soportes de `k`-items que contienen una arista dada son la imagen por `pairs` de los
`k`-items que la contienen. -/
theorem filter_supportsOfCard (k : ℕ) (e : Sym2 V) :
    (supportsOfCard G k).filter (fun S => e ∈ S)
      = (((items G).filter (fun K => K.card = k)).filter (fun K => e ∈ pairs K)).image pairs := by
  classical
  ext S
  simp only [supportsOfCard, Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨⟨K, hK, rfl⟩, heS⟩
    exact ⟨K, ⟨hK, heS⟩, rfl⟩
  · rintro ⟨K, ⟨hK, heK⟩, rfl⟩
    exact ⟨⟨K, hK, rfl⟩, heK⟩

/-- **La carga del hipergrafo es la carga del LP.**  Es el puente cuantitativo de «no
inventamos cliques»: `pairs` es inyectiva, luego sumar sobre soportes y sobre items coincide. -/
theorem load_eq (x : FracPacking G) (k : ℕ) (e : Sym2 V) :
    ∑ S ∈ (supportsOfCard G k).filter (fun S => e ∈ S), inducedWeight x S
      = ∑ K ∈ ((items G).filter (fun K => K.card = k)).filter (fun K => e ∈ pairs K),
          ((x.weight K : ℚ) : ℝ) := by
  classical
  rw [filter_supportsOfCard]
  refine Finset.sum_image ?_ |>.trans ?_
  · intro K hK L hL h
    simp only [Finset.mem_coe, Finset.mem_filter] at hK hL
    exact pairs_injOn_items (mem_items.1 hK.1.1) (mem_items.1 hL.1.1) h
  · refine Finset.sum_congr rfl ?_
    intro K hK
    rw [Finset.mem_filter, Finset.mem_filter] at hK
    exact inducedWeight_pairs x (mem_items.1 hK.1.1)

/-! ## 3. La carga `≤ 1` sale de la capacidad -/

/-- Si `e` no es arista de `G`, ningún soporte la contiene. -/
theorem load_eq_zero_of_not_edge (x : FracPacking G) (k : ℕ) {e : Sym2 V}
    (he : e ∉ G.edgeFinset) :
    ∑ S ∈ (supportsOfCard G k).filter (fun S => e ∈ S), inducedWeight x S = 0 := by
  classical
  rw [load_eq]
  refine Finset.sum_eq_zero ?_
  intro K hK
  rw [Finset.mem_filter, Finset.mem_filter] at hK
  exact absurd (pairs_subset_edgeFinset (mem_items.1 hK.1.1) hK.2) (fun h => he h)

/-- **La hipótesis de carga del nibble es la restricción de capacidad del LP.**

No hay nada que demostrar más allá de reordenar la suma: la carga de una arista en el
hipergrafo de soportes es, término a término, la carga que el LP ya acota por `1`. -/
theorem load_le_one (x : FracPacking G) (k : ℕ) (e : Sym2 V) :
    ∑ S ∈ (supportsOfCard G k).filter (fun S => e ∈ S), inducedWeight x S ≤ 1 := by
  classical
  by_cases he : e ∈ G.edgeFinset
  · rw [load_eq]
    -- la capacidad del LP, en la forma filtrada
    have hcap : ∑ K ∈ (items G).filter (fun K => e ∈ pairs K), x.weight K ≤ (1 : ℚ) := by
      rw [Finset.sum_filter]
      exact x.capacity e he
    -- el conjunto doblemente filtrado es menor
    have hQ : ∑ K ∈ ((items G).filter (fun K => K.card = k)).filter (fun K => e ∈ pairs K),
        x.weight K ≤ (1 : ℚ) := by
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_) hcap
      · intro K hK
        rw [Finset.mem_filter, Finset.mem_filter] at hK
        exact Finset.mem_filter.2 ⟨hK.1.1, hK.2⟩
      · intro K _ _
        exact x.weight_nonneg K
    have hcast : ∑ K ∈ ((items G).filter (fun K => K.card = k)).filter (fun K => e ∈ pairs K),
        ((x.weight K : ℚ) : ℝ)
        = ((∑ K ∈ ((items G).filter (fun K => K.card = k)).filter (fun K => e ∈ pairs K),
            x.weight K : ℚ) : ℝ) := by push_cast; ring
    rw [hcast]
    exact_mod_cast hQ
  · rw [load_eq_zero_of_not_edge x k he]; norm_num

/-! ## 4. La masa se conserva -/

/-- **La masa del hipergrafo es la masa del LP** sobre los `k`-items. -/
theorem mass_eq (x : FracPacking G) (k : ℕ) :
    ∑ S ∈ supportsOfCard G k, inducedWeight x S
      = ∑ K ∈ (items G).filter (fun K => K.card = k), ((x.weight K : ℚ) : ℝ) := by
  classical
  rw [supportsOfCard]
  refine Finset.sum_image ?_ |>.trans ?_
  · intro K hK L hL h
    simp only [Finset.mem_coe, Finset.mem_filter] at hK hL
    exact pairs_injOn_items (mem_items.1 hK.1) (mem_items.1 hL.1) h
  · refine Finset.sum_congr rfl ?_
    intro K hK
    rw [Finset.mem_filter] at hK
    exact inducedWeight_pairs x (mem_items.1 hK.1)

end MixedRounding

import PaperIV.SplitCompleteSharpLower

/-!
# BP-03 — el defecto exacto de una partición en cliques de un completo-split

`SplitCompleteSharpLower.cliquePartition_size_ge_baseline_unrestricted` demuestra la desigualdad
`|Q| ≥ k·h − C(k,2)`. Este módulo la **refina a una identidad**: mide exactamente cuánto se pasa
cada partición, pieza por pieza.

Para cada pieza `K` se define

```text
defect K = 1 + |aristas internas del núcleo en K| − |aristas núcleo–anfitrión en K|
```

y entonces

```text
|Q| + C(k,2) = k·h + ∑_{K ∈ Q} defect K.
```

La identidad es contabilidad pura: las piezas **particionan** las aristas, así que las sumas de
recursos internos y cruzados son constantes de la familia (`C(k,2)` y `k·h`). Lo que tiene
contenido es que **`defect K ≥ 0`**, que es la desigualdad por pieza ya demostrada.

## Qué se saca de la identidad

* **La cota inferior vuelve a salir**, ahora como corolario de que el defecto no es negativo.
* **El defecto de cada pieza tiene forma cerrada**: si `K` tiene un anfitrión y `s` vértices de
  núcleo, `defect K = 1 + C(s,2) − s`; si `K` está enteramente dentro del núcleo,
  `defect K = 1 + C(|K|,2) > 0`.
* **Las piezas de defecto cero están clasificadas**: exactamente las que tienen **un** anfitrión y
  **uno o dos** vértices de núcleo, es decir las aristas núcleo–anfitrión y los triángulos de dos
  núcleos con un anfitrión. Cualquier otra pieza paga.
* **Versión cuantitativa**: si una partición se pasa del óptimo en `t`, entonces tiene a lo sumo
  `t` piezas que no sean de esos dos tipos.

## Alcance

Todo esto vive **dentro de la familia completo-split**. No afirma unicidad de la partición óptima
—dos particiones óptimas distintas pueden repartir los mismos tipos de pieza de otra manera— ni
dice nada sobre cordales que no sean completo-split.

El argumento de pesos por pieza es heredado de Paper III (Corolario 10.2a) a través de
`card_crossPart_le_one_add_innerPart`; lo nuevo aquí es la identidad de defecto y su lectura
cuantitativa.
-/

namespace PaperIV.SplitCompleteDefect

open Finset
open PaperIV.Model PaperIV.FarRounding PaperIV.SplitUniformIncidence
open PaperIV.SplitEdgeCount PaperIV.SplitPackingObstruction
open PaperIV.SplitCompleteSharpLower

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- El **defecto** de una pieza: lo que le sobra respecto del canje ideal «una pieza por arista
cruzada». -/
def defect (Core Hosts K : Finset V) : ℕ :=
  1 + (innerPart Core K).card - (crossPart Core Hosts K).card

/-! ## 1. Forma cerrada del defecto -/

/-- Reescritura sin resta: es la desigualdad por pieza, puesta como igualdad. -/
theorem cross_add_defect {Core Hosts K : Finset V} (hd : Disjoint Core Hosts)
    (hclique : (splitGraph Core Hosts).IsClique (K : Set V)) (htwo : 2 ≤ K.card) :
    (crossPart Core Hosts K).card + defect Core Hosts K = 1 + (innerPart Core K).card :=
  Nat.add_sub_cancel' (card_crossPart_le_one_add_innerPart hd hclique htwo)

/-- Una pieza **sin anfitrión** paga al menos uno: está enteramente dentro del núcleo. -/
theorem defect_of_no_host {Core Hosts K : Finset V} (hz : K ∩ Hosts = ∅) :
    defect Core Hosts K = 1 + (K ∩ Core).card.choose 2 := by
  rw [defect, crossPart_eq_empty_of_no_host hz, innerPart_eq, card_pieceEdges]
  simp

/-- Una pieza **con un anfitrión** y `s` vértices de núcleo paga `1 + C(s,2) − s`. -/
theorem defect_of_host {Core Hosts K : Finset V} {z : V} (hd : Disjoint Core Hosts)
    (hz : K ∩ Hosts = {z}) :
    defect Core Hosts K = 1 + (K ∩ Core).card.choose 2 - (K ∩ Core).card := by
  rw [defect, card_crossPart_of_host hd hz, innerPart_eq, card_pieceEdges]

/-! ## 2. La identidad -/

/-- Los recursos cruzados suman el rectángulo completo. -/
private theorem sum_crossPart {Core Hosts : Finset V} (hd : Disjoint Core Hosts)
    (Q : CliquePartition (splitGraph Core Hosts)) :
    ∑ K ∈ Q.pieces, (crossPart Core Hosts K).card = Core.card * Hosts.card := by
  classical
  have hf : (graphEdges (splitGraph Core Hosts)).filter
      (fun e => e ∈ crossEdges Core Hosts) = crossEdges Core Hosts := by
    ext e
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨crossEdges_subset_graphEdges hd h, h⟩⟩
  have h := sum_card_filter_pairs Q (fun e => e ∈ crossEdges Core Hosts)
  change ∑ K ∈ Q.pieces, (crossPart Core Hosts K).card =
    ((graphEdges (splitGraph Core Hosts)).filter
      (fun e => e ∈ crossEdges Core Hosts)).card at h
  rw [hf] at h
  rw [h, PaperIV.SplitEdgeCount.card_crossEdges hd]

/-- Los recursos internos suman las aristas del núcleo. -/
private theorem sum_innerPart {Core Hosts : Finset V} (hd : Disjoint Core Hosts)
    (Q : CliquePartition (splitGraph Core Hosts)) :
    ∑ K ∈ Q.pieces, (innerPart Core K).card = Core.card.choose 2 := by
  classical
  have hf : (graphEdges (splitGraph Core Hosts)).filter
      (fun e => e ∈ pieceEdges Core) = pieceEdges Core := by
    ext e
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨innerEdges_subset_graphEdges hd h, h⟩⟩
  have h := sum_card_filter_pairs Q (fun e => e ∈ pieceEdges Core)
  change ∑ K ∈ Q.pieces, (innerPart Core K).card =
    ((graphEdges (splitGraph Core Hosts)).filter
      (fun e => e ∈ pieceEdges Core)).card at h
  rw [hf] at h
  rw [h, card_pieceEdges]

/-- **BP-03.  La identidad de defecto.**  El exceso de una partición sobre el óptimo es
exactamente la suma de los defectos de sus piezas. -/
theorem size_add_choose_eq_mul_add_sum_defect {Core Hosts : Finset V}
    (hd : Disjoint Core Hosts) (Q : CliquePartition (splitGraph Core Hosts)) :
    Q.size + Core.card.choose 2
      = Core.card * Hosts.card + ∑ K ∈ Q.pieces, defect Core Hosts K := by
  classical
  have hpiece : ∀ K ∈ Q.pieces,
      (crossPart Core Hosts K).card + defect Core Hosts K = 1 + (innerPart Core K).card :=
    fun K hK => cross_add_defect hd (Q.isClique K hK) (Q.two_le_card K hK)
  have hsum : ∑ K ∈ Q.pieces, ((crossPart Core Hosts K).card + defect Core Hosts K)
      = ∑ K ∈ Q.pieces, (1 + (innerPart Core K).card) :=
    Finset.sum_congr rfl hpiece
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const,
    sum_crossPart hd Q, sum_innerPart hd Q] at hsum
  simp only [smul_eq_mul, mul_one] at hsum
  change Q.pieces.card + Core.card.choose 2 = _
  omega

/-- La cota inferior vuelve a salir, ahora como corolario del defecto no negativo. -/
theorem baseline_le_size {Core Hosts : Finset V} (hd : Disjoint Core Hosts)
    (Q : CliquePartition (splitGraph Core Hosts)) :
    Core.card * Hosts.card - Core.card.choose 2 ≤ Q.size := by
  have h := size_add_choose_eq_mul_add_sum_defect hd Q
  omega

/-! ## 3. Las piezas que no pagan -/

/-- **Clasificación de las piezas de defecto cero.**  Son exactamente las que tienen un anfitrión
y uno o dos vértices de núcleo: las aristas núcleo–anfitrión y los triángulos de dos núcleos con
un anfitrión.  Cualquier otra pieza paga al menos uno. -/
theorem defect_eq_zero_iff {Core Hosts K : Finset V} {z : V} (hd : Disjoint Core Hosts)
    (hz : K ∩ Hosts = {z}) :
    defect Core Hosts K = 0 ↔ (K ∩ Core).card = 1 ∨ (K ∩ Core).card = 2 := by
  rw [defect_of_host hd hz]
  set c := (K ∩ Core).card with hc
  have hchoose : 2 * c.choose 2 = c * (c - 1) := (mul_pred_eq_two_mul_choose_two c).symm
  constructor
  · intro h
    by_contra hcc
    push_neg at hcc
    obtain ⟨h1, h2⟩ := hcc
    rcases Nat.lt_or_ge c 3 with hlt | hge
    · -- con `c ≠ 1` y `c ≠ 2` sólo queda `c = 0`, y entonces el defecto vale uno
      have hc0 : c = 0 := by omega
      rw [hc0] at h
      simp at h
    · have hmul : 3 * (c - 1) ≤ c * (c - 1) := Nat.mul_le_mul_right _ hge
      omega
  · rintro (h | h) <;> rw [h] <;> decide

/-- Una pieza sin anfitrión nunca tiene defecto cero. -/
theorem defect_pos_of_no_host {Core Hosts K : Finset V} (hz : K ∩ Hosts = ∅) :
    0 < defect Core Hosts K := by
  rw [defect_of_no_host hz]; omega

/-! ## 4. La versión cuantitativa -/

/-- **Si una partición se pasa en `t`, tiene a lo sumo `t` piezas que pagan.**

Es la forma en que el resultado se usa: acotar el exceso acota el número de piezas «raras», sin
necesidad de identificarlas una por una. -/
theorem card_paying_pieces_le_excess {Core Hosts : Finset V} {t : ℕ}
    (hd : Disjoint Core Hosts) (Q : CliquePartition (splitGraph Core Hosts))
    (hbase : Core.card.choose 2 ≤ Core.card * Hosts.card)
    (hexcess : Q.size ≤ Core.card * Hosts.card - Core.card.choose 2 + t) :
    (Q.pieces.filter fun K => 0 < defect Core Hosts K).card ≤ t := by
  classical
  have hid := size_add_choose_eq_mul_add_sum_defect hd Q
  have hle : (Q.pieces.filter fun K => 0 < defect Core Hosts K).card
      ≤ ∑ K ∈ Q.pieces, defect Core Hosts K := by
    calc (Q.pieces.filter fun K => 0 < defect Core Hosts K).card
        = ∑ _K ∈ Q.pieces.filter fun K => 0 < defect Core Hosts K, 1 := by
          simp
      _ ≤ ∑ K ∈ Q.pieces.filter fun K => 0 < defect Core Hosts K, defect Core Hosts K :=
          Finset.sum_le_sum fun K hK => (Finset.mem_filter.1 hK).2
      _ ≤ ∑ K ∈ Q.pieces, defect Core Hosts K :=
          Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  omega

end PaperIV.SplitCompleteDefect

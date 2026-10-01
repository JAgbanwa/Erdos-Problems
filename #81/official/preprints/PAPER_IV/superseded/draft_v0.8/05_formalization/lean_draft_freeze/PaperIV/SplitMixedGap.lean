import PaperIV.SplitCompleteDefect
import PaperIV.SplitCompleteSharpValue

/-!
# BP-04 — gap mixto cero en la familia completo-split

En `S = K_k ∨ I_h`, el óptimo **fraccional** mixto no supera al **entero**:

```text
W*(S) ≤ 2·C(k,2),
```

y la construcción triangular alcanza ese valor con pesos enteros, de modo que
`W*(S) = W(S) = 2·C(k,2)`.

## Por qué, en una línea

Cada pieza mixta gana a lo sumo el doble de las aristas **internas del núcleo** que consume
(`SplitCompleteExactValue.gainOf_le_two_mul_innerPart_of_piece`). Las aristas del núcleo son un
recurso de capacidad uno y hay `C(k,2)`. Intercambiando las sumas, cualquier empaquetamiento
—fraccional incluido— vale a lo sumo `2·C(k,2)`.

El contenido está en que **la misma desigualdad por pieza sirve en el mundo fraccional**: no hay
que rehacer nada, sólo llevarla a través de la suma y usar la capacidad. Un argumento por conteo
de copias no daría ese paso, porque los pesos son racionales.

## Alcance

Vale **en la familia completo-split**. No dice que el politopo del modelo mixto sea integral, ni
que el gap sea cero para todo cordal o todo split: la demostración usa que las aristas cruzadas no
producen ganancia por sí solas, que es propio de esta familia.
-/

open scoped BigOperators

namespace PaperIV.SplitMixedGap

open Finset
open PaperIV.Model PaperIV.FarRounding PaperIV.SplitUniformIncidence
open PaperIV.SplitEdgeCount PaperIV.SplitPackingObstruction
open PaperIV.SplitCompleteExactValue

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## 1. La desigualdad por pieza, en forma fraccional -/

/-- La cota por pieza pasa al cuerpo ordenado sin cambio: es la entera, casteada. -/
theorem gainF_le_two_mul_innerPart {Core Hosts : Finset V} (hd : Disjoint Core Hosts)
    {K : Finset V} (hK : IsItem (splitGraph Core Hosts) K) :
    gainF ℚ K ≤ 2 * ((innerPart Core K).card : ℚ) := by
  have hpiece : IsPiece (splitGraph Core Hosts) K := by
    refine ⟨hK.1, ?_⟩
    rcases hK.2 with h3 | h4
    · exact ⟨PieceKind.K3, by simpa [PieceKind.size] using h3⟩
    · exact ⟨PieceKind.K4, by simpa [PieceKind.size] using h4⟩
  -- `Model.gainOf` y `FarRounding.gainOf` coinciden en los items (cardinal 3 o 4) y **difieren**
  -- fuera de ellos; el puente hay que hacerlo explícito.
  have hbridge : FarRounding.gainOf K = Model.gainOf K := by
    rcases hK.2 with h3 | h4
    · rw [FarRounding.gainOf_of_card_eq_three h3, Model.gainOf, if_pos h3]
    · rw [FarRounding.gainOf, Model.gainOf, h4]
      decide
  have h := gainOf_le_two_mul_innerPart_of_piece hd hpiece
  rw [gainF_eq_gainOf hK, hbridge]
  exact_mod_cast h

/-- Las aristas internas de una pieza son las del núcleo que la pieza usa. -/
private theorem innerPart_eq_filter (Core K : Finset V) :
    innerPart Core K = (pieceEdges Core).filter fun e => e ∈ pairs K := by
  ext e
  simp only [innerPart, Finset.mem_filter]
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

/-! ## 2. La cota superior fraccional -/

/-- **Ningún empaquetamiento fraccional supera `2·C(k,2)`.**

Se suma la desigualdad por pieza, se intercambian las sumas y se usa la capacidad unidad de cada
arista interna del núcleo. -/
theorem fracPacking_value_le {Core Hosts : Finset V} (hd : Disjoint Core Hosts)
    (x : FracPacking (splitGraph Core Hosts) ℚ) :
    x.value ≤ 2 * (Core.card.choose 2 : ℚ) := by
  classical
  set S := splitGraph Core Hosts with hS
  -- cada pieza, contra las aristas de núcleo que consume
  have key : ∀ K ∈ items S, gainF ℚ K * x.weight K
      ≤ 2 * ∑ e ∈ pieceEdges Core, (if e ∈ pairs K then x.weight K else 0) := by
    intro K hK
    have hb := gainF_le_two_mul_innerPart hd (mem_items.1 hK)
    have hexp : ∑ e ∈ pieceEdges Core, (if e ∈ pairs K then x.weight K else 0)
        = ((innerPart Core K).card : ℚ) * x.weight K := by
      rw [← Finset.sum_filter, Finset.sum_const, innerPart_eq_filter, nsmul_eq_mul]
    rw [hexp]
    calc gainF ℚ K * x.weight K
        ≤ (2 * ((innerPart Core K).card : ℚ)) * x.weight K :=
          mul_le_mul_of_nonneg_right hb (x.weight_nonneg K)
      _ = 2 * (((innerPart Core K).card : ℚ) * x.weight K) := by ring
  calc x.value
      ≤ ∑ K ∈ items S, 2 * ∑ e ∈ pieceEdges Core,
          (if e ∈ pairs K then x.weight K else 0) := Finset.sum_le_sum key
    _ = 2 * ∑ e ∈ pieceEdges Core, ∑ K ∈ items S,
          (if e ∈ pairs K then x.weight K else 0) := by
        rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ 2 * ∑ _e ∈ pieceEdges Core, (1 : ℚ) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun e he => ?_) (by norm_num)
        exact x.capacity e (innerEdges_subset_graphEdges hd he)
    _ = 2 * (Core.card.choose 2 : ℚ) := by
        rw [Finset.sum_const, card_pieceEdges, nsmul_eq_mul, mul_one]

/-! ## 3. Se alcanza con pesos enteros -/

/-- En una partición en cliques, la ganancia total de las piezas es `e(G) − |Q|`. -/
theorem sum_gainOf_add_size {G : SimpleGraph V} [DecidableRel G.Adj] (Q : CliquePartition G) :
    ∑ K ∈ Q.pieces, FarRounding.gainOf K + Q.size = G.edgeFinset.card := by
  classical
  have hcover : ∑ K ∈ Q.pieces, (pairs K).card = G.edgeFinset.card := by
    rw [← Q.covers]
    exact (Finset.card_biUnion fun K hK L hL hne => Q.edgeDisjoint K hK L hL hne).symm
  have hpiece : ∀ K ∈ Q.pieces, FarRounding.gainOf K + 1 = (pairs K).card := by
    intro K hK
    have h2 := Q.two_le_card K hK
    have hcard : (pairs K).card = K.card.choose 2 := card_pieceEdges K
    have hge : 0 < K.card.choose 2 := Nat.choose_pos h2
    rw [FarRounding.gainOf, hcard]; omega
  have : ∑ K ∈ Q.pieces, (FarRounding.gainOf K + 1) = G.edgeFinset.card := by
    rw [Finset.sum_congr rfl hpiece]; exact hcover
  rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one] at this
  exact this

/-- **El valor `2·C(k,2)` se alcanza**: la partición óptima del completo-split deja exactamente
esa ganancia. -/
theorem exists_integral_gain_eq {Core Hosts : Finset V} (hd : Disjoint Core Hosts)
    (hcore : 2 ≤ Core.card) (hhosts : Core.card ≤ Hosts.card) :
    ∃ Q : CliquePartition (splitGraph Core Hosts),
      ∑ K ∈ Q.pieces, FarRounding.gainOf K = 2 * Core.card.choose 2 := by
  classical
  obtain ⟨Q, -, hQsize, -⟩ :=
    PaperIV.SplitCompleteSharpValue.exists_sharp_cliquePartition_allParities hd hcore hhosts
  refine ⟨Q, ?_⟩
  have hsum := sum_gainOf_add_size Q
  have hedges : (splitGraph Core Hosts).edgeFinset.card
      = Core.card.choose 2 + Core.card * Hosts.card :=
    PaperIV.SplitEdgeCount.card_graphEdges_splitGraph hd
  have hle : Core.card.choose 2 ≤ Core.card * Hosts.card := by
    have h2 : 2 * Core.card.choose 2 = Core.card * (Core.card - 1) :=
      (mul_pred_eq_two_mul_choose_two Core.card).symm
    have hmul : Core.card * (Core.card - 1) ≤ Core.card * Hosts.card :=
      Nat.mul_le_mul_left _ (by omega)
    omega
  -- enlaces para `omega`: son el mismo término, pero átomos distintos para el solucionador
  have hsz : Q.size = Q.pieces.card := rfl
  have hge : (graphEdges (splitGraph Core Hosts)).card
      = (splitGraph Core Hosts).edgeFinset.card := rfl
  change Q.pieces.card = _ at hQsize
  omega

/-! ## 4. La forma que el paper cita -/

/-- **BP-04.  Gap mixto cero en el completo-split.**

Ningún empaquetamiento fraccional supera `2·C(k,2)`, y ese valor lo alcanza una partición con
pesos enteros.  Por tanto el óptimo fraccional y el entero coinciden: la relajación no gana nada
en esta familia.

No se afirma integralidad del politopo: se afirma que **el valor óptimo** coincide, que es una
propiedad distinta y más débil. -/
theorem mixed_gap_zero {Core Hosts : Finset V} (hd : Disjoint Core Hosts)
    (hcore : 2 ≤ Core.card) (hhosts : Core.card ≤ Hosts.card) :
    (∀ x : FracPacking (splitGraph Core Hosts) ℚ,
        x.value ≤ 2 * (Core.card.choose 2 : ℚ)) ∧
      ∃ Q : CliquePartition (splitGraph Core Hosts),
        ∑ K ∈ Q.pieces, FarRounding.gainOf K = 2 * Core.card.choose 2 :=
  ⟨fun x => fracPacking_value_le hd x, exists_integral_gain_eq hd hcore hhosts⟩

end PaperIV.SplitMixedGap

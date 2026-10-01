import PaperIV.FarRounding
import PaperIV.SplitUniformIncidence
import ThreeRegime.CentreDefectArithmetic

/-!
# La ruta extrema falla en todo estado completo

La ruta *extrema* transporta la construcción exacta del completo-split
`K_S ∨ I_Z` al grafo real, pagando un arreglo físico de coste a lo sumo la
distancia de edición, y financiándolo con la reserva exacta
`M(centerDefect n |S|)` (identidad de holgura centro-extremos).

Aquí se demuestra que en un **estado completo** `K_n` (que aparece
inevitablemente como hijo de la recursión por separadores, y es cordal y
crítico en el sentido del árbol de cliques) esa financiación nunca existe:

* toda raíz equilibrada `1 ≤ |S| ≤ |Z|` deja el lado independiente `Z` con
  `C(|Z|,2)` aristas que hay que crear, y
* la reserva exacta disponible es estrictamente menor que `C(|Z|,2)`.

No es una limitación de la construcción concreta: es una cota inferior sobre
*cualquier* grafo en el que `Z` sea independiente.
-/

namespace ThreeRegime

open Finset PaperIV PaperIV.FarRounding PaperIV.SplitUniformIncidence SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

instance decidableSplitGraphAdj (Core Hosts : Finset V) :
    DecidableRel (splitGraph Core Hosts).Adj := fun _ _ =>
  decidable_of_iff _ splitGraph_adj_iff.symm

/-- Distancia de edición: número de pares en los que los dos grafos difieren. -/
def editDist (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj] :
    ℕ :=
  ((G.edgeFinset \ H.edgeFinset) ∪ (H.edgeFinset \ G.edgeFinset)).card

/-- **Cota inferior de edición.**  Si un conjunto `Z` es clique en `G` e
independiente en `H`, hay que editar al menos `C(|Z|,2)` pares. -/
theorem choose_two_le_editDist (G H : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] (Z : Finset V)
    (hG : ∀ a ∈ Z, ∀ b ∈ Z, a ≠ b → G.Adj a b)
    (hH : ∀ a ∈ Z, ∀ b ∈ Z, ¬ H.Adj a b) :
    Nat.choose Z.card 2 ≤ editDist G H := by
  have hsub : pairs Z ⊆
      (G.edgeFinset \ H.edgeFinset) ∪ (H.edgeFinset \ G.edgeFinset) := by
    intro e he
    rw [mem_pairs] at he
    obtain ⟨hmem, hdiag⟩ := he
    induction e using Sym2.ind with
    | _ a b =>
      have ha : a ∈ Z := hmem a (Sym2.mem_mk_left a b)
      have hb : b ∈ Z := hmem b (Sym2.mem_mk_right a b)
      have hab : a ≠ b := by simpa [Sym2.isDiag_iff_proj_eq] using hdiag
      refine Finset.mem_union_left _ (Finset.mem_sdiff.2 ⟨?_, ?_⟩)
      · simpa [SimpleGraph.mem_edgeFinset] using hG a ha b hb hab
      · simpa [SimpleGraph.mem_edgeFinset] using hH a ha b hb
  calc Nat.choose Z.card 2 = (pairs Z).card := (card_pairs Z).symm
    _ ≤ _ := Finset.card_le_card hsub

/-- El lado independiente de un completo-split es, en efecto, independiente. -/
theorem splitGraph_outside_independent (Core : Finset V)
    {a b : V} (ha : a ∈ Finset.univ \ Core) (hb : b ∈ Finset.univ \ Core) :
    ¬ (splitGraph Core (Finset.univ \ Core)).Adj a b := by
  intro hadj
  rw [splitGraph_adj_iff] at hadj
  have ha' : a ∉ Core := (Finset.mem_sdiff.1 ha).2
  have hb' : b ∉ Core := (Finset.mem_sdiff.1 hb).2
  rcases hadj.2 with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩
  · exact ha' h
  · exact ha' h
  · exact hb' h

/-- En un estado completo hay que crear todas las aristas del lado
independiente. -/
theorem choose_two_outside_le_editDist_top (Core : Finset V) :
    Nat.choose (Finset.univ \ Core).card 2 ≤
      editDist (⊤ : SimpleGraph V) (splitGraph Core (Finset.univ \ Core)) := by
  refine choose_two_le_editDist _ _ _ (fun a _ b _ hab => by simpa using hab)
    (fun a ha b hb => splitGraph_outside_independent Core ha hb)

theorem card_outside (Core : Finset V) :
    (Finset.univ \ Core).card = Fintype.card V - Core.card := by
  rw [← Finset.compl_eq_univ_sdiff, Finset.card_compl]

/-- **La ruta extrema no cierra en ningún estado completo.**  Para el grafo
completo con `n ≥ 4` vértices y cualquier raíz equilibrada
`1 ≤ |S| ≤ |Z|`, la reserva exacta de defecto central es estrictamente menor
que la distancia de edición al completo-split correspondiente. -/
theorem extreme_route_fails_on_complete (Core : Finset V)
    (hk : 1 ≤ Core.card) (hband : Core.card ≤ (Finset.univ \ Core).card)
    (hn : 4 ≤ Fintype.card V) :
    PaperIV.targetSize (centerDefect (Fintype.card V) Core.card) <
      editDist (⊤ : SimpleGraph V) (splitGraph Core (Finset.univ \ Core)) := by
  have hout := card_outside Core
  rw [hout] at hband
  refine lt_of_lt_of_le
    (reserve_lt_missing (Fintype.card V) Core.card hk hband hn) ?_
  have := choose_two_outside_le_editDist_top (V := V) Core
  rwa [hout] at this

end ThreeRegime

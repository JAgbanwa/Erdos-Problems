import Mathlib
import PaperIV.ChordalCopy
import PaperIV.PaddedEquitableColouring

/-!
# Vocabulario de raíz y exterior

Definiciones elementales para hablar de una clique distinguida `P` (la *raíz*) dentro de un grafo
finito y de su complemento (el *exterior*). Todas son forzadas por el enunciado: no contienen
ningún método.

Este fichero es autocontenido sobre Mathlib a propósito.
-/

open scoped BigOperators

namespace PaperIV.RootVocab

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Raíz y exterior -/

/-- Los vértices que no están en la raíz. -/
def outsideVertices (P : Finset V) : Finset V := Finset.univ \ P

@[simp] theorem mem_outsideVertices {P : Finset V} {v : V} :
    v ∈ outsideVertices P ↔ v ∉ P := by simp [outsideVertices]

/-- Aristas del grafo con los dos extremos fuera de la raíz. -/
noncomputable def outsideEdges (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finset V) : Finset (Sym2 V) := by
  classical
  exact G.edgeFinset.filter fun e => e.toFinset ⊆ outsideVertices P

/-- El grafo inducido en el exterior, visto dentro de `V`. -/
def outsideGraph (G : SimpleGraph V) (P : Finset V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ x ∉ P ∧ y ∉ P
  symm := fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩
  loopless.irrefl x h := G.loopless.irrefl x h.1

noncomputable instance outsideGraphDecidableAdj (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finset V) : DecidableRel (outsideGraph G P).Adj := by
  classical
  intro x y
  exact inferInstanceAs (Decidable (G.Adj x y ∧ x ∉ P ∧ y ∉ P))

/-! ## Paleta ampliada

El tamaño de paleta que el constructor de anfitriones consume.  **Alias** (`export`, no copia)
del canónico de `PaperIV.PaddedEquitableColouring`, que es quien tiene sus lemas. -/

export PaperIV.PaddedEquitableColouring (paddedPaletteSize)

/-! ## Defectos de la raíz -/

/-- Los vértices exteriores **no** adyacentes a un vértice `x` de la raíz. -/
noncomputable def missingColumn (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finset V) (x : V) : Finset V := by
  classical
  exact (outsideVertices P).filter fun y => ¬ G.Adj x y

/-- La columna faltante mayor sobre la raíz. -/
noncomputable def maxMissingColumn (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finset V) : ℕ :=
  P.sup fun x => (missingColumn G P x).card

/-- Número total de incidencias raíz--exterior que **faltan** en el grafo. -/
noncomputable def missingIncidences (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finset V) : ℕ :=
  ∑ x ∈ P, (missingColumn G P x).card


/-! ## Aristas internas de la raíz

`rootEdges` es el conjunto de aristas del grafo con los dos extremos dentro de `P`. Cuando `P` es
una clique son **todas** las parejas de `P`, y de ahí el conteo. -/

/-- Aristas del grafo con los dos extremos en la raíz. -/
noncomputable def rootEdges (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finset V) : Finset (Sym2 V) := by
  classical
  exact G.edgeFinset.filter fun e => e.toFinset ⊆ P

/-- En una clique, las aristas internas son exactamente los subconjuntos de dos elementos,
y por tanto hay `C(|K|, 2)` de ellas.

La biyección es `Sym2.toFinset`: manda cada arista al par de sus extremos.  Es inyectiva sobre
aristas (dos aristas con los mismos extremos son la misma, por `Sym2.ext`) y su imagen es
exactamente `K.powersetCard 2` (aquí es donde se usa que `K` es clique: todo par de vértices
distintos de `K` es realmente una arista). -/
theorem card_rootEdges (G : SimpleGraph V) [DecidableRel G.Adj]
    (K : Finset V) (hK : G.IsClique (K : Set V)) :
    (rootEdges G K).card = Nat.choose K.card 2 := by
  classical
  have hinjective : Set.InjOn Sym2.toFinset (rootEdges G K : Set (Sym2 V)) := by
    intro e _ f _ hef
    refine Sym2.ext fun x => ?_
    rw [← Sym2.mem_toFinset, ← Sym2.mem_toFinset, hef]
  have himage : (rootEdges G K).image Sym2.toFinset = K.powersetCard 2 := by
    ext L
    constructor
    · intro hL
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hL
      obtain ⟨heG, heK⟩ := Finset.mem_filter.mp he
      have hnd : ¬ e.IsDiag :=
        SimpleGraph.not_isDiag_of_mem_edgeSet G (SimpleGraph.mem_edgeFinset.mp heG)
      exact Finset.mem_powersetCard.mpr ⟨heK, Sym2.card_toFinset_of_not_isDiag e hnd⟩
    · intro hL
      obtain ⟨hLK, hLcard⟩ := Finset.mem_powersetCard.mp hL
      obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hLcard
      have hxK : x ∈ K := hLK (by simp)
      have hyK : y ∈ K := hLK (by simp)
      have hxyG : G.Adj x y := hK (Finset.mem_coe.mpr hxK) (Finset.mem_coe.mpr hyK) hxy
      refine Finset.mem_image.mpr ⟨s(x, y), ?_, Sym2.toFinset_mk_eq⟩
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · exact SimpleGraph.mem_edgeFinset.mpr hxyG
      · simpa only [Sym2.toFinset_mk_eq] using hLK
  calc
    (rootEdges G K).card = ((rootEdges G K).image Sym2.toFinset).card :=
      (Finset.card_image_of_injOn hinjective).symm
    _ = (K.powersetCard 2).card := by rw [himage]
    _ = Nat.choose K.card 2 := Finset.card_powersetCard 2 K

/-! ## Reparto de vértices entre raíz y exterior -/

theorem root_disjoint_outside (P : Finset V) : Disjoint P (outsideVertices P) := by
  rw [Finset.disjoint_left]; simp [outsideVertices]

theorem root_union_outside (P : Finset V) : P ∪ outsideVertices P = Finset.univ := by
  simp [outsideVertices]

theorem card_outsideVertices (P : Finset V) :
    (outsideVertices P).card = Fintype.card V - P.card := by
  rw [outsideVertices, Finset.card_sdiff_of_subset (Finset.subset_univ P), Finset.card_univ]

/-- Con el vocabulario propio, la identidad que en otras presentaciones hay que demostrar es
aquí la definición: `missingIncidences` **es** la suma de las columnas faltantes. -/
theorem sum_card_missingColumn (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finset V) :
    ∑ x ∈ P, (missingColumn G P x).card = missingIncidences G P := rfl

end PaperIV.RootVocab

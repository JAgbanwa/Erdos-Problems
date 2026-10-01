import PaperIV.FarRounding

/-!
# Transporte de particiones en cliques a lo largo de una igualdad de grafos

Cuando la estabilidad con déficit nulo identifica el grafo con un completo-split concreto,
hace falta mover particiones en cliques de un lado al otro de esa identificación.  La
estructura `CliquePartition` sólo depende del grafo a través de la relación de adyacencia y
del conjunto de aristas, así que el transporte es literal: las mismas piezas sirven.

Se hace explícito para no depender de que las dos instancias de `DecidableRel` que aparecen
—la del grafo dado y la sintetizada para el completo-split— sean la misma.
-/

namespace PaperIV.CliquePartitionTransport

open PaperIV.FarRounding

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- Grafos con la misma adyacencia tienen el mismo conjunto de aristas, cualesquiera que
sean las instancias de decidibilidad. -/
theorem edgeFinset_congr {G H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj]
    (h : ∀ x y, G.Adj x y ↔ H.Adj x y) : G.edgeFinset = H.edgeFinset := by
  ext e
  induction e using Sym2.ind with
  | _ x y => simp [h x y]

/-- Transporte de una partición en cliques a lo largo de una igualdad de adyacencias. -/
def transport {G H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj]
    (h : ∀ x y, G.Adj x y ↔ H.Adj x y) (Q : CliquePartition G) : CliquePartition H where
  pieces := Q.pieces
  isClique := fun K hK a ha b hb hab => (h a b).mp (Q.isClique K hK a ha b hb hab)
  two_le_card := Q.two_le_card
  edgeDisjoint := Q.edgeDisjoint
  covers := by rw [Q.covers, edgeFinset_congr h]

@[simp] theorem transport_size {G H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj]
    (h : ∀ x y, G.Adj x y ↔ H.Adj x y) (Q : CliquePartition G) :
    (transport h Q).size = Q.size := rfl

theorem transport_orderAtMost {G H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj]
    (h : ∀ x y, G.Adj x y ↔ H.Adj x y) (Q : CliquePartition G) {r : ℕ}
    (hQ : Q.OrderAtMost r) : (transport h Q).OrderAtMost r := hQ

end PaperIV.CliquePartitionTransport

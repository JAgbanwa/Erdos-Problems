import PaperIV.FarRounding
import ThreeRegime.CentreDefectArithmetic

/-!
# La ruta del centro en estados completos pequeños

En un estado completo con a lo sumo cuatro vértices la ruta del centro cierra
trivialmente: el propio `K_n` es una sola pieza física de orden `≤ 4`, y
`1 ≤ M(n)` en cuanto `n ≥ 2`.

Junto con `CompleteStateExtreme` y `CompleteStateSeparator`, esto da el cuadro
completo de `K₄`: la única de las tres rutas que cierra es el centro.  Para
`n ≥ 5` el centro deja de ser gratis y es exactamente donde se concentra la
obligación pendiente (descomposiciones casi-triangulares de `K_n`).
-/

namespace ThreeRegime

open Finset PaperIV PaperIV.FarRounding SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem pairs_univ_eq_edgeFinset :
    pairs (Finset.univ : Finset V) = (⊤ : SimpleGraph V).edgeFinset := by
  ext e
  rw [mem_pairs]
  induction e using Sym2.ind with
  | _ a b =>
    simp [Sym2.isDiag_iff_proj_eq]

/-- El grafo completo es una sola pieza física. -/
def singlePiecePartition (h2 : 2 ≤ Fintype.card V) :
    CliquePartition (⊤ : SimpleGraph V) where
  pieces := {Finset.univ}
  isClique := by
    intro K hK a _ b _ hab
    simpa using hab
  two_le_card := by
    intro K hK
    rw [Finset.mem_singleton] at hK
    subst hK
    simpa [Finset.card_univ] using h2
  edgeDisjoint := by
    intro K hK L hL hKL
    rw [Finset.mem_singleton] at hK hL
    exact absurd (hK.trans hL.symm) hKL
  covers := by
    simp [pairs_univ_eq_edgeFinset]

theorem singlePiecePartition_size (h2 : 2 ≤ Fintype.card V) :
    (singlePiecePartition h2).size = 1 := by
  simp [singlePiecePartition, CliquePartition.size]

theorem singlePiecePartition_orderAtMost (h2 : 2 ≤ Fintype.card V) :
    (singlePiecePartition h2).OrderAtMost (Fintype.card V) := by
  intro K hK
  rw [singlePiecePartition, Finset.mem_singleton] at hK
  simp [hK, Finset.card_univ]

/-- **La ruta del centro cierra en los estados completos de orden `≤ 4`.**
El certificado es una única pieza `K_n` de orden `n ≤ 4` y coste `1`, que cabe
en el presupuesto agudo. -/
theorem centre_route_closes_on_small_complete
    (h2 : 2 ≤ Fintype.card V) (h4 : Fintype.card V ≤ 4) :
    ∃ Q : CliquePartition (⊤ : SimpleGraph V),
      Q.OrderAtMost 4 ∧ Q.size ≤ PaperIV.targetSize (Fintype.card V) := by
  refine ⟨singlePiecePartition h2, ?_, ?_⟩
  · exact fun K hK => (singlePiecePartition_orderAtMost h2 K hK).trans h4
  · rw [singlePiecePartition_size h2]
    have : 1 ≤ PaperIV.targetSize (Fintype.card V) := by
      have := targetSize_mono h2
      simpa [PaperIV.targetSize] using this
    exact this

end ThreeRegime

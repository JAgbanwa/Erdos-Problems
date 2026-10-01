import PaperIV.RegularizedRootGoal
import PaperIV.NearH1RootRegularization

/-!
# Puente: la regularización propia alimenta la interfaz de la rama cercana

`PaperIV.RootRegularization.exists_regularizedRoot` demuestra la regularización estricta de la
raíz **sin ningún desarrollo externo**: la raíz es `(P \ strays) ∪ hubs`, los strays y los hubs
son pocos por un argumento de promedio contra el presupuesto cuadrático, y la cordalidad —usada
una sola vez, como «no hay cuadrados inducidos»— garantiza que los hubs forman clique y que todo
vértice de `P` no adyacente a un hub es un stray.

La rama cercana consume la estructura `NearH1RootRegularization.RegularizedRoot`. Este módulo
comprueba que las dos presentaciones del vocabulario de raíz coinciden y transporta la
conclusión.

## La única diferencia real

* **`missingIncidences`.** El vocabulario propio lo define como `∑ x ∈ P, |missingColumn x|`; el
  otra, como el cardinal de las interaristas del complemento. Son iguales, y aquí la igualdad ya
  lo tenía probado (`sum_card_missingColumn`).

El resto del vocabulario coincide por definición.
-/

namespace PaperIV.RootRegularizationBridge

open PaperIV.RootVocab

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## 1. Los dos vocabularios coinciden -/

theorem outsideVertices_eq (P : Finset V) :
    PaperIV.RootVocab.outsideVertices P = PaperIV.RootVocab.outsideVertices P := rfl

theorem missingColumn_eq (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finset V) (x : V) :
    PaperIV.RootVocab.missingColumn G P x = PaperIV.RootVocab.missingColumn G P x := rfl

theorem maxMissingColumn_eq (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finset V) :
    PaperIV.RootVocab.maxMissingColumn G P = PaperIV.RootVocab.maxMissingColumn G P := rfl

theorem outsideEdges_eq (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finset V) :
    PaperIV.RootVocab.outsideEdges G P = PaperIV.RootVocab.outsideEdges G P := rfl

theorem outsideGraph_eq (G : SimpleGraph V) (P : Finset V) :
    PaperIV.RootVocab.outsideGraph G P = PaperIV.RootVocab.outsideGraph G P := rfl

theorem paddedPaletteSize_eq (G : SimpleGraph V) [DecidableRel G.Adj] (p : ℕ) :
    PaperIV.RootVocab.paddedPaletteSize G p
      = PaperIV.PaddedEquitableColouring.paddedPaletteSize G p := rfl

/-- La única diferencia de formulación: suma de columnas frente a interaristas del complemento.
Con el vocabulario propio las dos presentaciones coinciden por definición; el enunciado se
conserva porque es el que consume la interfaz de la rama cercana. -/
theorem missingIncidences_eq (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finset V) :
    PaperIV.RootVocab.missingIncidences G P = PaperIV.RootVocab.missingIncidences G P :=
  PaperIV.RootVocab.sum_card_missingColumn G P

/-! ## 3. La conclusión, en la interfaz que la rama cercana consume

Mismo enunciado que `NearH1RootRegularization.exists_regularizedRoot`, pero demostrado desde la
construcción propia: sin motor de optimización y sin la promoción por minimización de energía. -/

open PaperIV.RootRegularization in
theorem exists_regularizedRoot_engineFree
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hchordal : PaperIV.IsChordal G) (P : Finset V)
    (hP : G.IsClique (P : Set V))
    (hp : 1024 ≤ P.card)
    (hbalanceLower : 127 * P.card ≤ 64 * (outsideVertices P).card)
    (hbalanceUpper : 64 * (outsideVertices P).card ≤ 129 * P.card)
    (hdefect : 65536 *
      ((outsideEdges G P).card + missingIncidences G P) ≤ P.card * P.card) :
    Nonempty (PaperIV.NearH1RootRegularization.RegularizedRoot G) := by
  classical
  have hp1 : 1 ≤ P.card := by omega
  -- El enunciado esta en el vocabulario que recibe la rama cercana;
  -- las cotas de la construccion propia estan en `PaperIV.RootVocab`.  `outsideVertices` y
  -- `outsideEdges` coinciden por definicion, asi que basta traducir `missingIncidences`.
  have hdefect' : 65536 *
      ((PaperIV.RootVocab.outsideEdges G P).card
        + PaperIV.RootVocab.missingIncidences G P) ≤ P.card * P.card := by
    rw [missingIncidences_eq]
    exact hdefect
  -- Enlaces sobre `P` (los de la raiz regularizada van mas abajo).  Sin ellos `omega`
  -- trata `outsideVertices P` y `RootVocab.outsideVertices P` como atomos distintos
  -- aunque sean el mismo termino.
  have p1 : (PaperIV.RootVocab.outsideVertices P).card
      = (PaperIV.RootVocab.outsideVertices P).card := rfl
  have p2 : (PaperIV.RootVocab.outsideEdges G P).card
      = (PaperIV.RootVocab.outsideEdges G P).card := rfl
  have p3 : PaperIV.RootVocab.missingIncidences G P
      = PaperIV.RootVocab.missingIncidences G P := (missingIncidences_eq G P).symm
  -- Cotas de tamaño de strays y hubs (Markov contra el presupuesto de `hdefect`).
  have hX := PaperIV.RootVocab.card_strays_le (G := G) (P := P) hp1 hdefect'
  have hH := PaperIV.RootVocab.card_hubs_le (G := G) (P := P) hp1 hdefect'
  -- Recuento de vértices.
  have hr := PaperIV.RootVocab.card_regularizedRootSet (G := G) (P := P)
  have hm := PaperIV.RootVocab.card_outsideVertices_regularizedRootSet (G := G) (P := P)
  have hn := PaperIV.RootVocab.card_add_card_outsideVertices (V := V) P
  have hnp : 64 * Fintype.card V ≤ 193 * P.card := by omega
  -- Las cotas estructurales.
  have hclique := PaperIV.RootVocab.regularizedRootSet_isClique hchordal hp hP hbalanceUpper hdefect'
  have hmaxmiss := PaperIV.RootVocab.maxMissingColumn_reg_le hP hp hbalanceUpper hdefect'
  have hEle := PaperIV.RootVocab.card_outsideEdges_reg_le (G := G) (P := P)
  have hMIle := PaperIV.RootVocab.missingIncidences_reg_le (G := G) (P := P) hP
  have hdeg := PaperIV.RootVocab.maxDegree_outsideGraph_reg_le (G := G) (P := P) hbalanceUpper
  have hcn := PaperIV.RootVocab.cliqueNum_outsideGraph_reg_le (G := G) (P := P) hdefect'
  -- Los dos productos que hacen falta para la aritmética cuadrática.
  have hXn : 1048576 * ((PaperIV.RootVocab.strays G P).card * Fintype.card V)
      ≤ 193 * (P.card * P.card) := by
    have hmul := Nat.mul_le_mul hX hnp
    calc 1048576 * ((PaperIV.RootVocab.strays G P).card * Fintype.card V)
        = (16384 * (PaperIV.RootVocab.strays G P).card) * (64 * Fintype.card V) := by ring
      _ ≤ P.card * (193 * P.card) := hmul
      _ = 193 * (P.card * P.card) := by ring
  have hHn : 3670016 * ((PaperIV.RootVocab.hubs G P).card * Fintype.card V)
      ≤ 193 * (P.card * P.card) := by
    have hmul := Nat.mul_le_mul hH hnp
    calc 3670016 * ((PaperIV.RootVocab.hubs G P).card * Fintype.card V)
        = (57344 * (PaperIV.RootVocab.hubs G P).card) * (64 * Fintype.card V) := by ring
      _ ≤ P.card * (193 * P.card) := hmul
      _ = 193 * (P.card * P.card) := by ring
  have hEbudget : 65536 * (PaperIV.RootVocab.outsideEdges G P).card ≤ P.card * P.card :=
    le_trans (by omega) hdefect'
  have hMIbudget :
      65536 * PaperIV.RootVocab.missingIncidences G P ≤ P.card * P.card :=
    le_trans (by omega) hdefect'
  have hE' : 1048576 *
        (PaperIV.RootVocab.outsideEdges G (PaperIV.RootVocab.regularizedRootSet G P)).card
      ≤ 209 * (P.card * P.card) :=
    PaperIV.RootVocab.arith_outsideEdges_bound hEle hEbudget hXn
  have hMI' : 3670016 *
        PaperIV.RootVocab.missingIncidences G (PaperIV.RootVocab.regularizedRootSet G P)
      ≤ 249 * (P.card * P.card) :=
    PaperIV.RootVocab.arith_missingIncidences_bound hMIle hMIbudget hHn
  have hQpos : 0 < P.card * P.card := Nat.mul_pos hp1 hp1
  -- Enlazar los dos vocabularios para que `omega` no los vea como atomos distintos.
  set R := PaperIV.RootVocab.regularizedRootSet G P with hR
  have e1 : (PaperIV.RootVocab.outsideVertices R).card
      = (PaperIV.RootVocab.outsideVertices R).card := rfl
  have e2 : (PaperIV.RootVocab.outsideEdges G R).card
      = (PaperIV.RootVocab.outsideEdges G R).card := rfl
  have e3 : PaperIV.RootVocab.maxMissingColumn G R
      = PaperIV.RootVocab.maxMissingColumn G R := rfl
  have e4 : PaperIV.RootVocab.missingIncidences G R
      = PaperIV.RootVocab.missingIncidences G R := (missingIncidences_eq G R).symm
  have e5 : (PaperIV.RootVocab.outsideGraph G R).cliqueNum
      = (PaperIV.RootVocab.outsideGraph G R).cliqueNum := rfl
  have e6 : PaperIV.PaddedEquitableColouring.paddedPaletteSize
        (PaperIV.RootVocab.outsideGraph G R) R.card
      = PaperIV.RootVocab.paddedPaletteSize (PaperIV.RootVocab.outsideGraph G R) R.card := rfl
  refine ⟨{ reference := P
            root := R
            isClique := hclique
            reference_large := hp
            card_ge := by omega
            root_le_outside := by omega
            outside_two := by omega
            root_lower_ratio := by omega
            root_ratio := by omega
            outside_ratio := by omega
            slack_ratio := by omega
            maxMissing_ratio := hmaxmiss
            outside_edges_small := ?_
            mass_envelope := ?_
            palette := ?_
            width := by omega }⟩
  · rw [pow_two]
    exact PaperIV.RootVocab.arith_outside_edges_small hE' hQpos
  · rw [pow_two, e4]
    exact PaperIV.RootVocab.arith_mass_envelope hMI' hE'
  · rw [e6, PaperIV.RootVocab.paddedPaletteSize]
    rcases max_choice R.card ((PaperIV.RootVocab.outsideGraph G R).maxDegree + 1) with h | h <;>
      rw [h] <;> omega


end PaperIV.RootRegularizationBridge

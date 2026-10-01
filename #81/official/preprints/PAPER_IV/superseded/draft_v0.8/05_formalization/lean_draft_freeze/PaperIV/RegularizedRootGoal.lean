import PaperIV.RegularizationBounds

/-!
# El objetivo: regularización estricta de la raíz

Este fichero contiene **un solo teorema por demostrar**, `exists_regularizedRoot`, y nada más.

## Qué se pide

Partiendo de una clique `P` de un grafo cordal cuyo tamaño y cuyos defectos ya están
calibrados —la hipótesis `hdefect` dice que el grafo está muy cerca de un grafo split completo
con esa clique—, construir una clique **regularizada** `root` que cumpla a la vez las trece
condiciones de `RegularizedRoot`.

Las dos que cuestan son:

* `width` — el exterior tiene número de clique pequeño frente a la raíz;
* `palette` — la paleta ampliada del exterior cabe en `73/40` veces la raíz, lo que en particular
  acota el grado máximo del exterior.

El resto son cuentas de tamaño que se siguen de mover pocos vértices.

## La idea que sugiere el encargo (no obligatoria)

`hdefect` da un presupuesto cuadrático de edición: `65536 · (aristas exteriores + incidencias
faltantes) ≤ |P|²`. Una desigualdad de Markov sobre ese presupuesto muestra que **muy pocos**
vértices son malos:

* los `x ∈ P` con `64 · |missingColumn x| > |P|` son a lo sumo `|P| / 1024`;
* los vértices exteriores con grado exterior grande son igual de escasos.

Quitar esos pocos de la raíz preserva la cliqueidad trivialmente. La parte delicada es recuperar
las cotas de `width` y `palette` después de quitarlos, porque el exterior crece.

Cualquier otra demostración es igual de bienvenida; la idea anterior es una pista, no un guion.

## Restricciones del encargo

1. **No importar ni reproducir ningún desarrollo externo de Erdős #81.** Este proyecto depende de
   Mathlib y de nada más, y así debe quedar. En particular no deben aparecer `RootOptimization`,
   `RootDemotion`, `RootedGraph`, `AdmissibleRoot`, `optimizedRoot`, ni promoción por minimización
   de energía.
2. **Sin `sorry`, sin `admit`, sin `axiom` propio, sin `native_decide`.** El resultado tiene que
   depender sólo de `propext`, `Classical.choice` y `Quot.sound`.
3. **No cambiar el enunciado**: ni los campos de `RegularizedRoot`, ni las constantes, ni las
   hipótesis de `exists_regularizedRoot`. Si alguna constante resulta inalcanzable, decirlo y
   explicar cuál es el obstáculo, en vez de ajustarla.
4. Se pueden añadir los módulos auxiliares que hagan falta, siempre bajo el espacio de nombres
   `PaperIV`.
-/

open scoped BigOperators

open PaperIV.RootVocab

namespace PaperIV.RootRegularization

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Una raíz **regularizada** de `G`, relativa a una clique de referencia. -/
structure RegularizedRoot (G : SimpleGraph V) [DecidableRel G.Adj] where
  /-- La clique de referencia de la que se parte. -/
  reference : Finset V
  /-- La clique regularizada. -/
  root : Finset V
  isClique : G.IsClique (root : Set V)
  reference_large : 1024 ≤ reference.card
  card_ge : 1000 ≤ root.card
  root_le_outside : root.card ≤ (outsideVertices root).card
  outside_two : 2 ≤ (outsideVertices root).card
  root_lower_ratio : 99 * reference.card ≤ 100 * root.card
  root_ratio : 100 * root.card ≤ 101 * reference.card
  outside_ratio : 87947 * reference.card ≤ 44352 * (outsideVertices root).card
  slack_ratio : 48 * (2 * root.card - (outsideVertices root).card) ≤ reference.card
  maxMissing_ratio : 3 * maxMissingColumn G root ≤ reference.card
  outside_edges_small : 400 * (outsideEdges G root).card < reference.card ^ 2
  mass_envelope : 2000 * (missingIncidences G root +
    2 * (outsideEdges G root).card) ≤ 11 * reference.card ^ 2
  palette : 40 * paddedPaletteSize (outsideGraph G root) root.card ≤ 73 * root.card
  width : 40 * ((outsideGraph G root).cliqueNum - 1) ≤ 3 * root.card

/-- **EL OBJETIVO.**  Regularización estricta de la raíz a partir de una clique calibrada. -/
theorem exists_regularizedRoot
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hchordal : PaperIV.IsChordal G) (P : Finset V)
    (hP : G.IsClique (P : Set V))
    (hp : 1024 ≤ P.card)
    (hbalanceLower : 127 * P.card ≤ 64 * (outsideVertices P).card)
    (hbalanceUpper : 64 * (outsideVertices P).card ≤ 129 * P.card)
    (hdefect : 65536 *
      ((outsideEdges G P).card + missingIncidences G P) ≤ P.card * P.card) :
    Nonempty (RegularizedRoot G) := by
  classical
  have hp1 : 1 ≤ P.card := by omega
  -- Cotas de tamaño de strays y hubs (Markov contra el presupuesto de `hdefect`).
  have hX := PaperIV.RootVocab.card_strays_le (G := G) (P := P) hp1 hdefect
  have hH := PaperIV.RootVocab.card_hubs_le (G := G) (P := P) hp1 hdefect
  -- Recuento de vértices.
  have hr := PaperIV.RootVocab.card_regularizedRootSet (G := G) (P := P)
  have hm := PaperIV.RootVocab.card_outsideVertices_regularizedRootSet (G := G) (P := P)
  have hn := PaperIV.RootVocab.card_add_card_outsideVertices (V := V) P
  have hnp : 64 * Fintype.card V ≤ 193 * P.card := by omega
  -- Las cotas estructurales.
  have hclique := PaperIV.RootVocab.regularizedRootSet_isClique hchordal hp hP hbalanceUpper hdefect
  have hmaxmiss := PaperIV.RootVocab.maxMissingColumn_reg_le hP hp hbalanceUpper hdefect
  have hEle := PaperIV.RootVocab.card_outsideEdges_reg_le (G := G) (P := P)
  have hMIle := PaperIV.RootVocab.missingIncidences_reg_le (G := G) (P := P) hP
  have hdeg := PaperIV.RootVocab.maxDegree_outsideGraph_reg_le (G := G) (P := P) hbalanceUpper
  have hcn := PaperIV.RootVocab.cliqueNum_outsideGraph_reg_le (G := G) (P := P) hdefect
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
  have hEbudget : 65536 * (outsideEdges G P).card ≤ P.card * P.card :=
    le_trans (by omega) hdefect
  have hMIbudget : 65536 * missingIncidences G P ≤ P.card * P.card :=
    le_trans (by omega) hdefect
  have hE' : 1048576 * (outsideEdges G (PaperIV.RootVocab.regularizedRootSet G P)).card
      ≤ 209 * (P.card * P.card) :=
    PaperIV.RootVocab.arith_outsideEdges_bound hEle hEbudget hXn
  have hMI' : 3670016 * missingIncidences G (PaperIV.RootVocab.regularizedRootSet G P)
      ≤ 249 * (P.card * P.card) :=
    PaperIV.RootVocab.arith_missingIncidences_bound hMIle hMIbudget hHn
  have hQpos : 0 < P.card * P.card := Nat.mul_pos hp1 hp1
  refine ⟨{ reference := P
            root := PaperIV.RootVocab.regularizedRootSet G P
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
  · rw [pow_two]
    exact PaperIV.RootVocab.arith_mass_envelope hMI' hE'
  · rw [PaperIV.RootVocab.paddedPaletteSize]
    rcases max_choice (PaperIV.RootVocab.regularizedRootSet G P).card
        ((PaperIV.RootVocab.outsideGraph G (PaperIV.RootVocab.regularizedRootSet G P)).maxDegree + 1) with h | h <;>
      rw [h] <;> omega

end PaperIV.RootRegularization

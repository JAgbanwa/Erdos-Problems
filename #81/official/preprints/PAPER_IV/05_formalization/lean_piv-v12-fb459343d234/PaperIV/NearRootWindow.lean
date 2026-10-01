import PaperIV.NearH1StructureWitness
import PaperIV.ReserveIdentity

/-!
# Ventanas cuantitativas de la raíz y del núcleo en el régimen cercano

El paquete estructural del régimen cercano (`NearStructureWitness`) ya contiene
toda la información necesaria para decir **dónde** está la raíz, pero los
consumidores actuales sólo extraían la ventana grosera `n/4 ≤ |R| ≤ n/2`.  Este
módulo aísla las ventanas óptimas que los datos ya soportan:

* **la raíz regularizada** cumple `|3|R| − n| ≤ n/50`, es decir `|R| = n/3` con
  un error relativo inferior al 1 %.  Sale sólo de tres campos de
  `RegularizedRoot` (`reference_order_lower`, `root_lower_ratio`, `slack_ratio`)
  y de `|R| + |exterior| = n`; es aritmética entera pura, sin hipótesis
  numéricas sobre `n`;
* **el núcleo comparador** cumple `|6|C| − 2n − 1| ≤ n/10^4`, o sea
  `|C| = n/3` con error relativo `3·10^{-5}`.  Esto usa el cuadrado residual
  calibrado y el umbral `n ≥ 4·10^12`;
* en consecuencia raíz y núcleo tienen **el mismo tamaño** salvo `n/100`.

La lectura en términos de la identidad de reserva es directa: por
`PaperIV.ReserveIdentity.residual_sq_le_iff`, el cuadrado residual calibrado
dice exactamente que la reserva `Mq(n − 3|C|)` generada por salirse del centro
no supera el defecto certificado `deltaCal n`.  Las ventanas de este módulo son
la forma métrica de ese enunciado.

Ninguna de estas afirmaciones debilita nada: todas son consecuencias de datos ya
demostrados, y se añaden como resultados nuevos.
-/

namespace PaperIV.NearRootWindow

open PaperIV.RootVocab
open PaperIV.NearH1StructureWitness
open PaperIV.NearH1RootRegularization

/-! ## 1. La ventana de la raíz es aritmética entera -/

/-- **Ventana aritmética de la raíz.**  Las tres proporciones de regularización
—el núcleo de referencia ocupa al menos `33/100` del orden, la raíz retiene al
menos `99/100` de la referencia, y la holgura `48·(2|R| − |exterior|) ≤ |ref|`—
encierran la raíz en la ventana `3267/10000 ≤ |R|/n ≤ 1188/3539`.

La resta `2 * root - out` es la resta truncada de `ℕ`; el enunciado es correcto
en las dos ramas, porque cuando se trunca ya se tiene `3|R| < n`. -/
theorem root_card_window_of_ratios {n ref root out : ℕ}
    (hcard : root + out = n)
    (href : 33 * n ≤ 100 * ref)
    (hlow : 99 * ref ≤ 100 * root)
    (hslack : 48 * (2 * root - out) ≤ ref) :
    3267 * n ≤ 10000 * root ∧ 3539 * root ≤ 1188 * n := by
  omega

/-- La ventana entera, leída como una desviación relativa del centro `n/3`. -/
theorem abs_three_mul_sub_le_of_window {n root : ℚ} (h0 : 0 ≤ n)
    (hlo : 3267 * n ≤ 10000 * root) (hhi : 3539 * root ≤ 1188 * n) :
    |3 * root - n| ≤ n / 50 := by
  rw [abs_le]
  constructor <;> linarith

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **La raíz regularizada tiene tamaño crítico.**  Versión entera. -/
theorem regularizedRoot_card_window {G : SimpleGraph V} [DecidableRel G.Adj]
    (R : RegularizedRoot G) :
    3267 * Fintype.card V ≤ 10000 * R.root.card ∧
      3539 * R.root.card ≤ 1188 * Fintype.card V := by
  have hcard : R.root.card + (outsideVertices R.root).card = Fintype.card V := by
    rw [card_outsideVertices]
    have hle : R.root.card ≤ Fintype.card V := by
      simpa [Finset.card_univ] using Finset.card_le_univ R.root
    omega
  exact root_card_window_of_ratios hcard R.reference_order_lower R.root_lower_ratio
    R.slack_ratio

/-- **La raíz regularizada tiene tamaño crítico.**  `|R| = n/3` con error
relativo menor que el 1 %.  No hay hipótesis numérica sobre `n`. -/
theorem regularizedRoot_card_near_third {G : SimpleGraph V} [DecidableRel G.Adj]
    (R : RegularizedRoot G) :
    |3 * (R.root.card : ℚ) - (Fintype.card V : ℚ)| ≤ (Fintype.card V : ℚ) / 50 := by
  obtain ⟨hlo, hhi⟩ := regularizedRoot_card_window R
  have hlo' : 3267 * (Fintype.card V : ℚ) ≤ 10000 * (R.root.card : ℚ) := by
    exact_mod_cast hlo
  have hhi' : 3539 * (R.root.card : ℚ) ≤ 1188 * (Fintype.card V : ℚ) := by
    exact_mod_cast hhi
  exact abs_three_mul_sub_le_of_window (by positivity) hlo' hhi'

/-! ## 2. La ventana del núcleo comparador -/

/-- El cuadrado residual calibrado acota el residuo en valor absoluto por
`n/10^4`.  Es la forma métrica de `deltaCal n ≤ (61/10)·eps·n²`. -/
theorem abs_residual_le_of_deltaCal {n r : ℚ} (hn : 4 * (10 : ℚ) ^ 12 ≤ n)
    (h : r ^ 2 ≤ 24 * PaperIV.NearH1SplitComparator.deltaCal n) :
    |r| ≤ n / 10000 := by
  have hd := PaperIV.NearH1Calibration.delta_small hn
    (PaperIV.NearH1SplitComparator.deltaCal_le n)
  dsimp [PaperIV.NearH1Calibration.eps] at hd
  have hn0 : (0 : ℚ) ≤ n := by linarith
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · nlinarith [sq_nonneg (r + n / 10000)]
  · nlinarith [sq_nonneg (r - n / 10000)]

/-- **El núcleo comparador tiene tamaño crítico.**  El residuo `6|C| − 2n − 1`
del núcleo de un testigo estructural cercano es a lo sumo `n/10^4`. -/
theorem core_residual_window {G : SimpleGraph V} [DecidableRel G.Adj] [LinearOrder V]
    (W : NearStructureWitness G) (hn : 4 * (10 : ℚ) ^ 12 ≤ (Fintype.card V : ℚ)) :
    |6 * (W.core.card : ℚ) - 2 * (Fintype.card V : ℚ) - 1| ≤
      (Fintype.card V : ℚ) / 10000 :=
  abs_residual_le_of_deltaCal hn W.core_residual_sq_le

/-- La misma ventana, centrada: `|C| = n/3` con error relativo `3·10^{-5}`. -/
theorem core_card_near_third {G : SimpleGraph V} [DecidableRel G.Adj] [LinearOrder V]
    (W : NearStructureWitness G) (hn : 4 * (10 : ℚ) ^ 12 ≤ (Fintype.card V : ℚ)) :
    |3 * (W.core.card : ℚ) - (Fintype.card V : ℚ)| ≤ (Fintype.card V : ℚ) / 10000 := by
  have h := core_residual_window W hn
  rw [abs_le] at h ⊢
  constructor <;> linarith [h.1, h.2]

/-- **Lectura por la identidad de reserva.**  El cuadrado residual calibrado del
núcleo dice exactamente que la reserva racional que genera salirse del centro no
supera el defecto terminal calibrado. -/
theorem core_reserve_le_deltaCal {G : SimpleGraph V} [DecidableRel G.Adj] [LinearOrder V]
    (W : NearStructureWitness G) :
    PaperIV.ReserveIdentity.Mq
        ((Fintype.card V : ℚ) - 3 * (W.core.card : ℚ)) + 1 / 24 ≤
      PaperIV.NearH1SplitComparator.deltaCal (Fintype.card V : ℚ) :=
  (PaperIV.ReserveIdentity.residual_sq_le_iff _ _ _).1 W.core_residual_sq_le

/-! ## 3. Raíz y núcleo tienen el mismo tamaño -/

/-- **Coincidencia raíz/núcleo.**  En un testigo estructural cercano, la raíz
regularizada y el núcleo comparador difieren en a lo sumo `n/100` vértices,
aunque se construyen por caminos distintos. -/
theorem root_sub_core_le {G : SimpleGraph V} [DecidableRel G.Adj] [LinearOrder V]
    (W : NearStructureWitness G) (hn : 4 * (10 : ℚ) ^ 12 ≤ (Fintype.card V : ℚ)) :
    |(W.regularized.root.card : ℚ) - (W.core.card : ℚ)| ≤ (Fintype.card V : ℚ) / 100 := by
  have hR := regularizedRoot_card_near_third W.regularized
  have hC := core_card_near_third W hn
  rw [abs_le] at hR hC ⊢
  constructor <;> linarith [hR.1, hR.2, hC.1, hC.2]

/-- **El tamaño del núcleo es canónico.**  Dos testigos estructurales cercanos
del mismo grafo —o de dos grafos del mismo orden— tienen núcleos del mismo
tamaño salvo `n/15000`.  La ruta cercana no elige, pues, el tamaño del núcleo:
lo encuentra. -/
theorem core_card_sub_core_card_le {G G' : SimpleGraph V} [DecidableRel G.Adj]
    [DecidableRel G'.Adj] [LinearOrder V]
    (W : NearStructureWitness G) (W' : NearStructureWitness G')
    (hn : 4 * (10 : ℚ) ^ 12 ≤ (Fintype.card V : ℚ)) :
    |(W.core.card : ℚ) - (W'.core.card : ℚ)| ≤ (Fintype.card V : ℚ) / 15000 := by
  have h1 := core_card_near_third W hn
  have h2 := core_card_near_third W' hn
  rw [abs_le] at h1 h2 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

end PaperIV.NearRootWindow

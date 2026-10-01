import PaperIV.FarRoundingBatchBridge

/-!
# El régimen lejano por asignación de aristas a bolsas

Reformulación de `FarRounding.FarRoundingAt` que sustituye el redondeo global
(la transferencia uniforme de Rohatgi–Urschel–Wellens, vía nibble) por un
enunciado **constructivo** sobre asignaciones de aristas.

La observación estructural que la sostiene es la cordalidad: todo `K₃` y todo `K₄`
de un grafo cordal vive dentro de una bolsa maximal del árbol de cliques.  Por
tanto, si se reparten las aristas entre bolsas, cada ítem queda disponible en a lo
sumo una bolsa, y los packings por bolsa se ensamblan sin interferencia.

## Contenido

* `exists_packing_of_edgeAssignment` — **ensamblaje por asignación**: si los
  conjuntos de aristas asignados a bolsas distintas son disjuntos y cada bolsa
  aporta un packing soportado en sus aristas, la unión es un `Packing` literal de
  `G` cuya ganancia es la suma exacta.  Es la versión utilizable de
  `FarRoundingBatchBridge.exists_packing_of_batches`.

* `AssignmentLossAt ζ` — la hipótesis combinatoria que reemplaza al nibble: para
  todo cordal grande y todo óptimo fraccional certificado existe una asignación de
  aristas y packings por bolsa cuya ganancia total dista a lo sumo `ζ n²` del
  óptimo fraccional.

* `farRoundingAt_of_assignmentLoss` — **el teorema**: `AssignmentLossAt (η/2)`
  implica `FarRoundingAt η`.

## Estado

`AssignmentLossAt` **no se demuestra aquí**: es una hipótesis explícita, igual que
`UniformTransferAt`.  Lo que aporta este módulo es cambiar la *forma* de la entrada
externa, de un teorema de redondeo probabilístico a una afirmación de existencia de
asignación, que es donde la ruta ya tiene maquinaria (coloración equilibrada,
constructor de dos fases, factorización del núcleo).

Evidencia computacional registrada en `E01_BRIDGE_STATUS.md`: con la asignación
canónica hacia la raíz la pérdida crece como `Θ(n²)` en la familia split, mientras
que con la asignación balanceada por factores es exactamente `0` en todas las
familias split probadas, y entre `0` y `2` en dos cliques pegadas por un separador
(`n ≤ 12`).  Nada de eso prueba `AssignmentLossAt`.
-/

namespace PaperIV.FarRoundingFromAssignment

open Finset
open PaperIV.FarRounding
open PaperIV.FarRoundingBatchBridge

/-! ## 1. Ensamblaje por asignación de aristas -/

section Assembly

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable {β : Type*} [DecidableEq β]

/-- **Ensamblaje por asignación.**  Bolsas con conjuntos de aristas disjuntos dos a
dos, cada una con un packing soportado en sus propias aristas, se unen en un
`Packing` literal de `G` de ganancia igual a la suma. -/
theorem exists_packing_of_edgeAssignment
    (Bs : Finset β) (part : β → Finset (Sym2 V))
    (hdisj : ∀ b ∈ Bs, ∀ b' ∈ Bs, b ≠ b' → Disjoint (part b) (part b'))
    (P : β → Packing G)
    (hsupp : ∀ b ∈ Bs, ∀ K ∈ (P b).pieces, pairs K ⊆ part b) :
    ∃ Q : Packing G, Q.gain = ∑ b ∈ Bs, (P b).gain := by
  classical
  obtain ⟨Q, -, hQgain⟩ :=
    exists_packing_of_batches (G := G) Bs (fun b => (P b).pieces)
      (fun b _ K hK => (P b).isItem K hK)
      (fun b _ K hK L hL hKL => (P b).edgeDisjoint K hK L hL hKL)
      (fun b hb b' hb' hbb K hK L hL =>
        Finset.disjoint_of_subset_left (hsupp b hb K hK)
          (Finset.disjoint_of_subset_right (hsupp b' hb' L hL) (hdisj b hb b' hb' hbb)))
  exact ⟨Q, hQgain⟩

end Assembly

/-! ## 2. La hipótesis de asignación y el teorema -/

/-- **La entrada combinatoria que reemplaza al nibble.**  Para todo cordal
suficientemente grande y todo óptimo fraccional certificado existe un reparto de
aristas entre bolsas, con packings por bolsa, cuya ganancia total dista a lo sumo
`ζ n²` del óptimo fraccional.

Es una `Prop`-valued **definición**, nunca demostrada en este módulo. -/
def AssignmentLossAt (ζ : ℚ) : Prop :=
  ∃ T : ℕ, ∀ n : ℕ, T ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    IsChordal G → ∀ w : ℚ, CertifiedFractionalOptimum G w →
      ∃ (Bs : Finset ℕ) (part : ℕ → Finset (Sym2 (Fin n))) (P : ℕ → Packing G),
        (∀ b ∈ Bs, ∀ b' ∈ Bs, b ≠ b' → Disjoint (part b) (part b')) ∧
        (∀ b ∈ Bs, ∀ K ∈ (P b).pieces, pairs K ⊆ part b) ∧
        w - (∑ b ∈ Bs, ((P b).gain : ℚ)) ≤ ζ * (n : ℚ) ^ 2

/-- **El teorema.**  La existencia de asignaciones con pérdida `η/2 · n²` implica el
redondeo lejano `FarRoundingAt η`.  La cordalidad no se usa en la prueba: se arrastra
como restricción desde la hipótesis, exactamente igual que en
`farRoundingAt_of_uniformTransferAt`. -/
theorem farRoundingAt_of_assignmentLoss {η : ℚ} (h : AssignmentLossAt (η / 2)) :
    FarRoundingAt η := by
  obtain ⟨T, hT⟩ := h
  refine ⟨T, ?_⟩
  intro n hn G _ hchord w hw _
  obtain ⟨Bs, part, P, hdisj, hsupp, hloss⟩ := hT n hn G hchord w hw
  obtain ⟨Q, hQ⟩ := exists_packing_of_edgeAssignment Bs part hdisj P hsupp
  refine ⟨Q, ?_⟩
  have hcast : (Q.gain : ℚ) = ∑ b ∈ Bs, ((P b).gain : ℚ) := by
    rw [hQ]; push_cast; ring
  rw [hcast]
  linarith [hloss]

end PaperIV.FarRoundingFromAssignment

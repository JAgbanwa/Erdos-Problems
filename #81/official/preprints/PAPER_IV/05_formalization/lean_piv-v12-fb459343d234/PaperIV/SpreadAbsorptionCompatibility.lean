import PaperIV.SpreadLedgerAbsorption
import PaperIV.PackingUnion

/-!
# El absorbedor spread es **compatible** con el packing que ya existe

`SpreadLedgerAbsorption.exists_spread_absorber_count_add_cost_le_baseline` demuestra dos cosas:
que el absorbedor es un packing, y que su coste cabe bajo el baseline. Pero lo demuestra **por
separado** del packing físico que la ruta ya había construido. Dicho de otro modo: prueba que el
absorbedor existe y que se paga, no que se pueda **usar**.

Este módulo cierra esa distancia. La conclusión es un **único** packing:

```text
IsPacking G (P ∪ physicalTriangleAbsorber C z)
```

y el recuento se suma exactamente, sin reserva escondida.

## La hipótesis, y por qué es la honesta

Hace falta que `P` no haya tocado ya las aristas que el absorbedor quiere usar. Eso se escribe
como `hfree`: **ninguna arista cubierta por `P` tiene sus dos extremos dentro de `insert z N`**.

Es una hipótesis sobre datos, no una suposición sobre el problema: en la ruta principal, `N`, el
concentrador `z` y su libertad los produce el constructor del régimen cercano. Dejarla visible es
justo lo que impide presentar spread como un cierre universal: fuera de donde el constructor la
garantiza, no hay absorbedor.

## Por qué no se fusiona con `completion`

`completion G P` ya cubre **todas** las aristas del grafo — es una compleción. Unir el absorbedor
a ella es imposible por construcción. El orden correcto es el contrario: absorber sobre el packing
parcial `P`, y completar después. Por eso el enunciado habla de `P`, no de `completion G P`.
-/

open scoped BigOperators

namespace PaperIV.SpreadAbsorptionCompatibility

open PaperIV.Model PaperIV.SpreadAbsorption PaperIV.ExteriorTriangleLift

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ## 1. El absorbedor vive dentro de `insert z N` -/

/-- Toda pieza del absorbedor está contenida en `insert z N`: es el triángulo formado por el
concentrador y una arista del emparejamiento, cuyos extremos están en `N`. -/
theorem absorber_piece_subset {N : Finset V} (C : Certificate G N) (z : V)
    {s : Finset V} (hs : s ∈ physicalTriangleAbsorber C z) :
    s ⊆ insert z N := by
  classical
  obtain ⟨e, he, rfl⟩ := mem_liftedPacking.1 hs
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 he
  intro v hv
  rcases mem_triangle.1 hv with rfl | hv'
  · exact Finset.mem_insert_self _ _
  · refine Finset.mem_insert_of_mem ?_
    rcases Sym2.mem_iff.1 hv' with rfl | rfl
    · exact hy
    · exact C.mapsTo _ hy

/-- Y por tanto toda arista que el absorbedor cubre tiene sus dos extremos ahí. -/
theorem absorber_coveredEdges_subset {N : Finset V} (C : Certificate G N) (z : V)
    {e : Sym2 V} (he : e ∈ coveredEdges (physicalTriangleAbsorber C z)) :
    ∀ v ∈ e, v ∈ insert z N := by
  classical
  obtain ⟨s, hs, hes⟩ := mem_coveredEdges.1 he
  intro v hv
  exact absorber_piece_subset C z hs ((mem_pieceEdges.1 hes).1 v hv)

/-! ## 2. La unión es un solo packing -/

/-- **El absorbedor se une al packing existente.**

La hipótesis `hfree` dice que `P` no ha gastado ninguna arista interna a `insert z N`.  Bajo ella
los dos recursos son disjuntos y `PackingUnion.isPacking_union_of_disjoint_covered` cierra. -/
theorem isPacking_union_absorber {P : Finset (Finset V)} {N : Finset V}
    (C : Certificate G N) {z : V}
    (hP : IsPacking G P) (hz : ∀ a ∈ N, G.Adj z a)
    (hfree : ∀ e ∈ coveredEdges P, ¬ (∀ v ∈ e, v ∈ insert z N)) :
    IsPacking G (P ∪ physicalTriangleAbsorber C z) := by
  classical
  refine PaperIV.PackingUnion.isPacking_union_of_disjoint_covered hP
    (physical_triangle_absorber C hz) ?_
  rw [Finset.disjoint_left]
  intro e heP heA
  exact hfree e heP (absorber_coveredEdges_subset C z heA)

/-- Las dos familias de piezas son disjuntas como conjuntos de piezas, luego la ganancia suma. -/
theorem totalGain_union_absorber {P : Finset (Finset V)} {N : Finset V}
    (C : Certificate G N) {z : V} (hz : ∀ a ∈ N, G.Adj z a)
    (hNne : N.Nonempty)
    (hfree : ∀ e ∈ coveredEdges P, ¬ (∀ v ∈ e, v ∈ insert z N)) :
    totalGain (P ∪ physicalTriangleAbsorber C z)
      = totalGain P + totalGain (physicalTriangleAbsorber C z) := by
  classical
  refine PaperIV.PackingUnion.totalGain_union ?_
  rw [Finset.disjoint_left]
  intro s hsP hsA
  -- una pieza común daría una arista común, y `hfree` lo prohíbe
  obtain ⟨e, he, rfl⟩ := mem_liftedPacking.1 hsA
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 he
  have hne : y ≠ C.partner y := (C.ne y hy).symm
  have hzy : z ≠ y := (hz y hy).ne
  have hmem : s(y, C.partner y) ∈ pieceEdges (triangle z s(y, C.partner y)) := by
    refine mem_pieceEdges_mk.2 ⟨?_, ?_, hne⟩
    · exact mem_triangle.2 (Or.inr (Sym2.mem_mk_left _ _))
    · exact mem_triangle.2 (Or.inr (Sym2.mem_mk_right _ _))
  refine hfree s(y, C.partner y) (mem_coveredEdges.2 ⟨_, hsP, hmem⟩) ?_
  intro v hv
  rcases Sym2.mem_iff.1 hv with rfl | rfl
  · exact Finset.mem_insert_of_mem hy
  · exact Finset.mem_insert_of_mem (C.mapsTo _ hy)

/-! ## 3. La forma que el paper cita -/

/-- **Absorción spread compatible.**  Bajo la condición de grado de Dirac con holgura, un
concentrador común y la libertad de recursos `hfree`, existe un certificado cuyo absorbedor
**se une** al packing existente formando un solo packing, y cuya ganancia se suma exactamente.

Comparado con `exists_spread_absorber_count_add_cost_le_baseline`, lo nuevo es el `IsPacking` de
la **unión**: antes el absorbedor era un objeto aparte cuyo coste cabía en el presupuesto; ahora
es una pieza del mismo packing. -/
theorem exists_compatible_spread_absorber {P : Finset (Finset V)} {N : Finset V} {t : ℕ}
    (hP : IsPacking G P)
    (heven : Even N.card)
    (hdeg : ∀ v ∈ N, N.card / 2 + t ≤ (N.filter fun z => G.Adj v z).card)
    {z : V} (hz : ∀ a ∈ N, G.Adj z a)
    (hNne : N.Nonempty)
    (hfree : ∀ e ∈ coveredEdges P, ¬ (∀ v ∈ e, v ∈ insert z N)) :
    ∃ C : Certificate G N,
      IsPacking G (P ∪ physicalTriangleAbsorber C z) ∧
      totalGain (P ∪ physicalTriangleAbsorber C z) = totalGain P + N.card := by
  classical
  obtain ⟨C, -⟩ := exists_certificate (G := G) (N := N) heven hdeg
  refine ⟨C, isPacking_union_absorber C hP hz hfree, ?_⟩
  rw [totalGain_union_absorber C hz hNne hfree,
    totalGain_physical_triangle_absorber C hz]

/-! ## 4. BP-07 — un solo certificado: presupuestado **y** compatible

`exists_compatible_spread_absorber` elige el certificado con `exists_certificate`, que ignora el
coste; `SpreadAbsorption.exists_budgeted_physical_triangle_absorber` elige uno de coste acotado,
pero no dice nada de compatibilidad. Combinar los dos enunciados **no** da un solo certificado:
son dos existenciales independientes y nada obliga a que el testigo sea el mismo.

La forma correcta es la del contrato: **primero** se elige el certificado presupuestado, y
**después** se le aplican los lemas de unión, que valen para cualquier certificado. Así el mismo
`C` cumple las tres cosas. -/

/-- **BP-07.  Un mismo certificado presupuestado y compatible.**

Con las hipótesis de §3.2 —incluida `hfree`— más la cota de masa de conflicto, existe **un**
certificado `C` tal que el absorbedor se une al packing previo formando un solo packing, la
ganancia suma exactamente, y el coste seleccionado cabe en el presupuesto.

El coste conserva la convención de suma sobre vértices: `∑ y ∈ N, bad y (C.partner y)`. No se
identifica con un conteo de pares no orientados ni con piezas retiradas. -/
theorem exists_budgeted_compatible_spread_absorber {P : Finset (Finset V)} {N : Finset V} {t : ℕ}
    (hP : IsPacking G P)
    (heven : Even N.card)
    (hdeg : ∀ v ∈ N, N.card / 2 + t ≤ (N.filter fun z => G.Adj v z).card)
    (bad : V → V → ℝ) (hbad : ∀ y z, 0 ≤ bad y z) (budget : ℝ)
    (hmass : ∑ y ∈ N, ∑ x ∈ N, bad y x ≤ ((t : ℝ) + 1) * budget)
    {z : V} (hz : ∀ a ∈ N, G.Adj z a)
    (hNne : N.Nonempty)
    (hfree : ∀ e ∈ coveredEdges P, ¬ (∀ v ∈ e, v ∈ insert z N)) :
    ∃ C : Certificate G N,
      IsPacking G (P ∪ physicalTriangleAbsorber C z) ∧
      totalGain (P ∪ physicalTriangleAbsorber C z) = totalGain P + N.card ∧
      ∑ y ∈ N, bad y (C.partner y) ≤ budget := by
  classical
  -- **Primero** el certificado presupuestado; el mismo `C` viaja al resto.
  obtain ⟨C, -, -, hcost⟩ :=
    exists_budgeted_physical_triangle_absorber heven hdeg bad hbad budget hmass hz
  refine ⟨C, isPacking_union_absorber C hP hz hfree, ?_, hcost⟩
  rw [totalGain_union_absorber C hz hNne hfree, totalGain_physical_triangle_absorber C hz]

end PaperIV.SpreadAbsorptionCompatibility

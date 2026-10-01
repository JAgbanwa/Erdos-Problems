import PaperIV.MultiHostTriangleLift
import PaperIV.Vizing

/-!
# BP-06 — remate con cuatro anfitriones

El residuo que deja el empaquetamiento suma-cero tiene grado máximo tres. Este módulo demuestra
que **cuatro anfitriones exteriores universales bastan** para absorberlo entero: se colorea el
residuo con cuatro colores por Vizing, cada clase de color es un emparejamiento, y cada
emparejamiento se levanta sobre su propio anfitrión.

## La pieza que faltaba

`PaperIV.MultiHostTriangleLift` ya entrega el levantamiento multi-anfitrión con su libro de
cuentas —`card = ∑ᵢ |Eᵢ|`, `totalGain = 2·∑ᵢ |Eᵢ|`, y disyunción de recursos **entre**
anfitriones—, y `PaperIV.Vizing` ya entrega el coloreo propio de aristas. Lo que no existía es el
puente: que las **clases de color sean emparejamientos literales** en el sentido de
`IsLiteralMatching`, es decir, disyunción de los conjuntos de extremos y no sólo de las aristas.
Sale de `col_proper`, y es lo que permite instanciar `IsMultiExteriorHub`.

## Alcance

El enunciado toma los cuatro anfitriones **como dato**, con sus tres condiciones explícitas:
distintos entre sí, adyacentes a todo extremo de toda arista del residuo, y exteriores al
residuo. No se afirma que tales anfitriones existan en todo cordal; eso depende de la raíz que
entregue la fase anterior. Lo que se demuestra es que, disponibles, el residuo se cierra con
`|E(H)|` triángulos y ganancia `2·|E(H)|`.

El grado máximo tres es la hipótesis que usa el conteo: con `Δ ≤ 3` bastan cuatro colores. Con
`Δ ≤ k` bastarían `k+1` anfitriones, y la demostración es la misma.
-/

namespace PaperIV.FourHostClosure

open Finset PaperIV.Model PaperIV.ExteriorTriangleLift PaperIV.MultiHostTriangleLift

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## 1. Las clases de color son emparejamientos literales -/

/-- **El puente.** En un coloreo propio total, dos aristas distintas del mismo color no comparten
ningún extremo. Es `col_proper` leído en la forma que pide `IsExteriorHub`. -/
theorem colourClass_isLiteralMatching {C : Type*} [DecidableEq C] [Inhabited C]
    {H : SimpleGraph V} [DecidableRel H.Adj] (c : Vizing.PEC H C)
    (htot : ∀ u v, H.Adj u v → c.col u v ≠ none) (γ : C) :
    IsLiteralMatching (H.edgeFinset.filter fun e => c.edgeColor e = γ) := by
  classical
  intro e he f hf hef
  rw [Finset.disjoint_left]
  intro a hae haf
  obtain ⟨heE, hec⟩ := Finset.mem_filter.1 he
  obtain ⟨hfE, hfc⟩ := Finset.mem_filter.1 hf
  obtain ⟨u, rfl⟩ := Sym2.mem_iff_exists.1 (Sym2.mem_toFinset.1 hae)
  obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.1 (Sym2.mem_toFinset.1 haf)
  have hadje : H.Adj a u := by
    rwa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at heE
  have hadjf : H.Adj a w := by
    rwa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at hfE
  obtain ⟨γ₁, h1⟩ := Option.ne_none_iff_exists'.1 (htot a u hadje)
  obtain ⟨γ₂, h2⟩ := Option.ne_none_iff_exists'.1 (htot a w hadjf)
  rw [Vizing.PEC.edgeColor_mk, h1, Option.getD_some] at hec
  rw [Vizing.PEC.edgeColor_mk, h2, Option.getD_some] at hfc
  subst hec
  subst hfc
  exact hef (by rw [c.col_proper h1 h2])

/-! ## 2. Las cuatro clases parten el residuo -/

private theorem sum_card_colourClass {C : Type*} [Fintype C] [DecidableEq C] [Inhabited C]
    {H : SimpleGraph V} [DecidableRel H.Adj] (c : Vizing.PEC H C) :
    ∑ γ : C, (H.edgeFinset.filter fun e => c.edgeColor e = γ).card = H.edgeFinset.card :=
  (Finset.card_eq_sum_card_fiberwise fun e _ => Finset.mem_univ (c.edgeColor e)).symm

/-! ## 3. BP-06 -/

/-- **BP-06.  Remate con cuatro anfitriones.**

Un residuo `H` de grado máximo tres, con cuatro anfitriones exteriores universales, se absorbe
entero: existe un empaquetamiento literal de `G` con exactamente `|E(H)|` triángulos, ganancia
`2·|E(H)|`, que cubre todas las aristas del residuo.

Las tres condiciones sobre los anfitriones son hipótesis del enunciado, no se suponen
disponibles. -/
theorem exists_fourHost_packing {G : SimpleGraph V} [DecidableRel G.Adj]
    (H : SimpleGraph V) [DecidableRel H.Adj] (hdeg : H.maxDegree ≤ 3)
    (hsub : ∀ e ∈ H.edgeFinset, e ∈ graphEdges G)
    (z : Fin 4 → V) (hinj : Function.Injective z)
    (hhub : ∀ i : Fin 4, ∀ e ∈ H.edgeFinset, ∀ a ∈ e, G.Adj (z i) a)
    (hext : ∀ j : Fin 4, ∀ e ∈ H.edgeFinset, ∀ a ∈ e, a ≠ z j) :
    ∃ P : Finset (Finset V),
      IsPacking G P ∧
      P.card = H.edgeFinset.card ∧
      totalGain P = 2 * H.edgeFinset.card ∧
      H.edgeFinset ⊆ coveredEdges P := by
  classical
  have hcard : H.maxDegree < Fintype.card (Fin 4) := by
    simp only [Fintype.card_fin]
    omega
  obtain ⟨c, htot⟩ := Vizing.PEC.exists_total (G := H) (C := Fin 4) hcard
  set E : Fin 4 → Finset (Sym2 V) :=
    fun i => H.edgeFinset.filter fun e => c.edgeColor e = i with hE
  have hmemE : ∀ i, ∀ e ∈ E i, e ∈ H.edgeFinset := fun i e he => (Finset.mem_filter.1 he).1
  have hhubs : IsMultiExteriorHub G z E := by
    refine ⟨fun i => ⟨?_, ?_, ?_⟩, hinj, ?_, ?_⟩
    · exact fun e he => hsub e (hmemE i e he)
    · exact colourClass_isLiteralMatching c htot i
    · exact fun e he a ha => hhub i e (hmemE i e he) a ha
    · exact fun i j e he a ha => hext j e (hmemE i e he) a ha
    · intro i j hij
      rw [Finset.disjoint_left]
      intro e hei hej
      exact hij (((Finset.mem_filter.1 hei).2).symm.trans (Finset.mem_filter.1 hej).2)
  have hsum : ∑ i : Fin 4, (E i).card = H.edgeFinset.card := sum_card_colourClass c
  refine ⟨multiLiftedPacking z E, isPacking_multiLiftedPacking hhubs, ?_, ?_, ?_⟩
  · rw [card_multiLiftedPacking hhubs, hsum]
  · rw [totalGain_multiLiftedPacking hhubs, hsum]
  · refine Finset.Subset.trans ?_ (biUnion_base_subset_coveredEdges hhubs)
    intro e he
    exact Finset.mem_biUnion.2 ⟨c.edgeColor e, Finset.mem_univ _,
      Finset.mem_filter.2 ⟨he, rfl⟩⟩

/-- Forma de conteo: el residuo cuesta a lo sumo `|E(H)|` piezas y devuelve ganancia `2·|E(H)|`,
de modo que cubrirlo con triángulos ahorra exactamente `|E(H)|` piezas frente a cubrirlo con
aristas sueltas. -/
theorem fourHost_saving {G : SimpleGraph V} [DecidableRel G.Adj]
    (H : SimpleGraph V) [DecidableRel H.Adj] (hdeg : H.maxDegree ≤ 3)
    (hsub : ∀ e ∈ H.edgeFinset, e ∈ graphEdges G)
    (z : Fin 4 → V) (hinj : Function.Injective z)
    (hhub : ∀ i : Fin 4, ∀ e ∈ H.edgeFinset, ∀ a ∈ e, G.Adj (z i) a)
    (hext : ∀ j : Fin 4, ∀ e ∈ H.edgeFinset, ∀ a ∈ e, a ≠ z j) :
    ∃ P : Finset (Finset V), IsPacking G P ∧
      totalGain P = 2 * P.card ∧ P.card = H.edgeFinset.card := by
  obtain ⟨P, hpack, hcard, hgain, -⟩ :=
    exists_fourHost_packing H hdeg hsub z hinj hhub hext
  exact ⟨P, hpack, by rw [hgain, hcard], hcard⟩

end PaperIV.FourHostClosure

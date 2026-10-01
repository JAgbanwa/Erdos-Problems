import PaperIV.RD09SplitEditAccount
import PaperIV.GraphFamilyDistance

/-!
# La distancia de edición a un completo-split con núcleo clique, exactamente

`PaperIV.RD09SplitEditAccount` acota el defecto RD09 `m + A` por la distancia de edición
más un término de incidencias del núcleo del comparador.  Cuando la raíz `R` es **ella
misma** una clique de `G` y el comparador es el completo-split sobre `R`, esa desigualdad
es de hecho una **igualdad**, y no queda término residual:

```text
d_E(G, S_R) = m + A,     m = |outsideEdges G R|,   A = missingIncidences G R .
```

La razón es elemental.  Una arista del defecto simétrico `E(G) ∆ E(S_R)` es de un solo tipo:

* está en `G` y no en `S_R`: entonces sus dos extremos caen fuera de `R`, porque `S_R` une
  todo par con algún extremo en `R`.  Es una arista de `outsideEdges G R`;
* está en `S_R` y no en `G`: sus dos extremos no pueden estar ambos en `R` —`R` es clique
  de `G`—, luego es un radio raíz–exterior ausente, es decir un elemento de
  `missingSpokeEdges G R`.

Las dos familias son disjuntas (`outsideEdges_disjoint_missingSpokeEdges`), de modo que el
cardinal se parte.  Este es el puente que convierte la cuenta física `m/20 + A/2 ≤ δ` en
una cota de distancia `d_E ≤ 20 δ`.

La hipótesis «`R` es clique de `G`» es imprescindible y se deja visible: sin ella el
defecto simétrico contiene además los pares internos de `R` ausentes en `G`.
-/

namespace PaperIV.SplitEditIdentity

open Finset
open scoped symmDiff
open PaperIV.EditMetric PaperIV.RootVocab PaperIV.SplitUniformIncidence
open PaperIV.RD09SplitEditAccount PaperIV.GraphFamilyDistance

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Adyacencia del completo-split cuyo lado anfitrión es exactamente el complemento del
núcleo: dos vértices distintos son adyacentes si y sólo si alguno está en el núcleo. -/
theorem splitGraph_compl_adj_iff (R : Finset V) (x y : V) :
    (splitGraph R (Finset.univ \ R)).Adj x y ↔ x ≠ y ∧ (x ∈ R ∨ y ∈ R) := by
  constructor
  · rintro ⟨hne, h⟩
    refine ⟨hne, ?_⟩
    rcases h with ⟨hx, -⟩ | ⟨hx, -⟩ | ⟨-, hy⟩
    · exact Or.inl hx
    · exact Or.inl hx
    · exact Or.inr hy
  · rintro ⟨hne, hx | hy⟩
    · by_cases hyR : y ∈ R
      · exact ⟨hne, Or.inl ⟨hx, hyR⟩⟩
      · exact ⟨hne, Or.inr (Or.inl ⟨hx, by simp [hyR]⟩)⟩
    · by_cases hxR : x ∈ R
      · exact ⟨hne, Or.inl ⟨hxR, hy⟩⟩
      · exact ⟨hne, Or.inr (Or.inr ⟨by simp [hxR], hy⟩)⟩

/-- **El defecto simétrico es exactamente el defecto RD09.**  Para una raíz que ya es
clique del grafo, la diferencia simétrica de los soportes de aristas coincide con la unión
disjunta de aristas exteriores y radios ausentes. -/
theorem symmDiff_eq_defectEdges (G : SimpleGraph V) [DecidableRel G.Adj]
    {R : Finset V} (hR : G.IsClique (R : Set V)) :
    G.edgeFinset ∆ graphEdgeSupport (splitGraph R (Finset.univ \ R))
      = defectEdges G R := by
  classical
  have hsupp : ∀ e : Sym2 V,
      e ∈ graphEdgeSupport (splitGraph R (Finset.univ \ R)) ↔
        e ∈ (splitGraph R (Finset.univ \ R)).edgeSet := by
    intro e
    simp [graphEdgeSupport]
  ext e
  induction e using Sym2.ind with
  | _ x y =>
    constructor
    · intro he
      rcases Finset.mem_symmDiff.mp he with ⟨hG, hS⟩ | ⟨hS, hG⟩
      · -- arista de `G` ausente del split: ambos extremos fuera de `R`
        have hGadj : G.Adj x y := by
          simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hG
        have hSadj : ¬ (splitGraph R (Finset.univ \ R)).Adj x y := by
          intro h
          exact hS ((hsupp _).mpr (by simpa only [SimpleGraph.mem_edgeSet] using h))
        have hno := (splitGraph_compl_adj_iff R x y).not.mp hSadj
        have hxy : x ≠ y := hGadj.ne
        have hxR : x ∉ R := by
          intro hx; exact hno ⟨hxy, Or.inl hx⟩
        have hyR : y ∉ R := by
          intro hy; exact hno ⟨hxy, Or.inr hy⟩
        refine Finset.mem_union.mpr (Or.inl ?_)
        refine Finset.mem_filter.mpr ⟨hG, ?_⟩
        intro v hv
        have hv' : v = x ∨ v = y := by
          simpa using (Sym2.mem_toFinset.mp hv)
        rcases hv' with rfl | rfl
        · simpa using hxR
        · simpa using hyR
      · -- arista del split ausente de `G`: radio raíz–exterior ausente
        have hSadj : (splitGraph R (Finset.univ \ R)).Adj x y := by
          simpa only [SimpleGraph.mem_edgeSet] using (hsupp _).mp hS
        have hGadj : ¬ G.Adj x y := by
          intro h
          exact hG (by simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using h)
        obtain ⟨hxy, hor⟩ := (splitGraph_compl_adj_iff R x y).mp hSadj
        refine Finset.mem_union.mpr (Or.inr ?_)
        have hnotboth : ¬ (x ∈ R ∧ y ∈ R) := by
          rintro ⟨hx, hy⟩
          exact hGadj (hR (by simpa using hx) (by simpa using hy) hxy)
        rcases hor with hx | hy
        · have hyR : y ∉ R := fun hy => hnotboth ⟨hx, hy⟩
          refine Finset.mem_image.mpr ⟨(x, y), ?_, rfl⟩
          refine Rel.mem_interedges_iff.mpr ⟨hx, by simpa using hyR, ?_⟩
          simp only [SimpleGraph.compl_adj]
          exact ⟨hxy, hGadj⟩
        · have hxR : x ∉ R := fun hx => hnotboth ⟨hx, hy⟩
          refine Finset.mem_image.mpr ⟨(y, x), ?_, Sym2.eq_swap⟩
          refine Rel.mem_interedges_iff.mpr ⟨hy, by simpa using hxR, ?_⟩
          simp only [SimpleGraph.compl_adj]
          exact ⟨hxy.symm, fun h => hGadj h.symm⟩
    · intro he
      rcases Finset.mem_union.mp he with hout | hmiss
      · obtain ⟨hG, hsub⟩ := Finset.mem_filter.mp hout
        have hxR : x ∉ R := by
          have := hsub (Sym2.mem_toFinset.mpr (Sym2.mem_mk_left x y))
          simpa using this
        have hyR : y ∉ R := by
          have := hsub (Sym2.mem_toFinset.mpr (Sym2.mem_mk_right x y))
          simpa using this
        refine Finset.mem_symmDiff.mpr (Or.inl ⟨hG, ?_⟩)
        intro hS
        have hSadj : (splitGraph R (Finset.univ \ R)).Adj x y := by
          simpa only [SimpleGraph.mem_edgeSet] using (hsupp _).mp hS
        rcases ((splitGraph_compl_adj_iff R x y).mp hSadj).2 with hx | hy
        · exact hxR hx
        · exact hyR hy
      · obtain ⟨⟨a, b⟩, hab, hEq⟩ := Finset.mem_image.mp hmiss
        obtain ⟨haR, hbOut, hcadj⟩ := Rel.mem_interedges_iff.mp hab
        have hbR : b ∉ R := by simpa using hbOut
        have hne : a ≠ b := by
          simp only [SimpleGraph.compl_adj] at hcadj
          exact hcadj.1
        have hnadj : ¬ G.Adj a b := by
          simp only [SimpleGraph.compl_adj] at hcadj
          exact hcadj.2
        have hSab : (splitGraph R (Finset.univ \ R)).Adj a b :=
          (splitGraph_compl_adj_iff R a b).mpr ⟨hne, Or.inl haR⟩
        have hmemS : s(a, b) ∈ graphEdgeSupport (splitGraph R (Finset.univ \ R)) :=
          (hsupp _).mpr (by simpa only [SimpleGraph.mem_edgeSet] using hSab)
        have hnotG : s(a, b) ∉ G.edgeFinset := by
          simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hnadj
        have : s(a, b) ∈ G.edgeFinset ∆ graphEdgeSupport (splitGraph R (Finset.univ \ R)) :=
          Finset.mem_symmDiff.mpr (Or.inr ⟨hmemS, hnotG⟩)
        rwa [hEq] at this

/-- **La identidad de edición.**  Si la raíz `R` es una clique de `G`, la distancia de
edición entre `G` y el completo-split de núcleo `R` es exactamente `m + A`. -/
theorem editDist_split_eq (G : SimpleGraph V) [DecidableRel G.Adj]
    {R : Finset V} (hR : G.IsClique (R : Set V)) :
    editDist G.edgeFinset (graphEdgeSupport (splitGraph R (Finset.univ \ R)))
      = (outsideEdges G R).card + missingIncidences G R := by
  rw [editDist, symmDiff_eq_defectEdges G hR, card_defectEdges]

/-- Distancia de edición nula: el grafo **es** el completo-split de núcleo `R`. -/
theorem eq_splitGraph_of_editDist_eq_zero (G : SimpleGraph V) [DecidableRel G.Adj]
    {R : Finset V}
    (h : editDist G.edgeFinset (graphEdgeSupport (splitGraph R (Finset.univ \ R))) = 0) :
    G = splitGraph R (Finset.univ \ R) := by
  classical
  have hsets : G.edgeFinset = graphEdgeSupport (splitGraph R (Finset.univ \ R)) :=
    editDist_eq_zero_iff.mp h
  ext x y
  constructor
  · intro hxy
    have hmem : s(x, y) ∈ G.edgeFinset := by
      simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hxy
    rw [hsets] at hmem
    have : s(x, y) ∈ (splitGraph R (Finset.univ \ R)).edgeSet := by
      simpa [graphEdgeSupport] using hmem
    simpa only [SimpleGraph.mem_edgeSet] using this
  · intro hxy
    have hmem : s(x, y) ∈ graphEdgeSupport (splitGraph R (Finset.univ \ R)) := by
      simpa [graphEdgeSupport] using hxy
    rw [← hsets] at hmem
    simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hmem

end PaperIV.SplitEditIdentity

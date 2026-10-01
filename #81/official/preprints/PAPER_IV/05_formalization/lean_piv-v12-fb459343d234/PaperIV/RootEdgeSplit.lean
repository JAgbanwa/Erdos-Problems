import PaperIV.RootVocabulary
import Mathlib.Combinatorics.SimpleGraph.Density

/-!
# El reparto de aristas relativo a una raíz

Fijada una raíz `P`, cada arista del grafo es de exactamente uno de tres tipos: **interna**
(los dos extremos en `P`), **exterior** (los dos fuera) o **cruzada** (uno y uno). Este módulo
demuestra ese reparto y lo combina con el conteo de incidencias faltantes.

El resultado que se consume aguas arriba es `card_edgeFinset_add_missingIncidences`:

```text
|E(G)| + (incidencias raíz–exterior que faltan)
    = |aristas internas| + |aristas exteriores| + |P| · |exterior|
```

Dicho en palabras: contar las aristas del grafo y sumarle lo que falta para que la raíz vea a
todo el exterior es lo mismo que contar las aristas internas, las exteriores, y **todas** las
incidencias raíz–exterior como si estuvieran presentes. Es la identidad que convierte una cota
sobre el defecto en una cota sobre el número de aristas.

Todo está escrito sobre el vocabulario de `PaperIV.RootVocabulary`.
-/

open scoped BigOperators

namespace PaperIV.RootVocab

variable {V : Type*} [Fintype V] [DecidableEq V]

@[simp] theorem mem_missingColumn {G : SimpleGraph V} [DecidableRel G.Adj]
    {P : Finset V} {x y : V} :
    y ∈ missingColumn G P x ↔ y ∉ P ∧ ¬ G.Adj x y := by
  simp [missingColumn]

/-! ## 1. Las columnas presentes -/

/-- Los vértices exteriores que **sí** son adyacentes a un vértice `x` de la raíz.  Es la
columna complementaria de `missingColumn`. -/
noncomputable def presentColumn (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finset V) (x : V) : Finset V :=
  (outsideVertices P).filter fun y => G.Adj x y

@[simp] theorem mem_presentColumn {G : SimpleGraph V} [DecidableRel G.Adj]
    {P : Finset V} {x y : V} :
    y ∈ presentColumn G P x ↔ y ∉ P ∧ G.Adj x y := by
  simp [presentColumn]

/-- Cada vértice exterior está en exactamente una de las dos columnas. -/
theorem card_presentColumn_add_card_missingColumn (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finset V) (x : V) :
    (presentColumn G P x).card + (missingColumn G P x).card
      = (outsideVertices P).card := by
  classical
  simpa [presentColumn, missingColumn] using
    Finset.filter_card_add_filter_neg_card_eq_card
      (s := outsideVertices P) (p := fun y => G.Adj x y)

/-! ## 2. Los pares cruzados -/

/-- Los pares `(x, y)` con `x` en la raíz, `y` fuera y `x y` una arista. -/
noncomputable def crossingPairs (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finset V) : Finset (V × V) :=
  P.biUnion fun x => (presentColumn G P x).image fun y => (x, y)

theorem mem_crossingPairs {G : SimpleGraph V} [DecidableRel G.Adj]
    {P : Finset V} {p : V × V} :
    p ∈ crossingPairs G P ↔ p.1 ∈ P ∧ p.2 ∉ P ∧ G.Adj p.1 p.2 := by
  classical
  constructor
  · intro h
    obtain ⟨x, hx, hp⟩ := Finset.mem_biUnion.1 h
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hp
    exact ⟨hx, (mem_presentColumn.1 hy).1, (mem_presentColumn.1 hy).2⟩
  · rintro ⟨h1, h2, h3⟩
    refine Finset.mem_biUnion.2 ⟨p.1, h1, Finset.mem_image.2 ⟨p.2, ?_, rfl⟩⟩
    exact mem_presentColumn.2 ⟨h2, h3⟩

/-- Hay tantos pares cruzados como incidencias raíz--exterior presentes. -/
theorem card_crossingPairs (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finset V) :
    (crossingPairs G P).card = ∑ x ∈ P, (presentColumn G P x).card := by
  classical
  rw [crossingPairs, Finset.card_biUnion]
  · exact Finset.sum_congr rfl fun x _ =>
      Finset.card_image_of_injective _ fun a b hab => (Prod.mk.injEq _ _ _ _ ▸ hab).2
  · intro x _ y _ hxy
    refine Finset.disjoint_left.2 fun p hp hq => hxy ?_
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hp
    obtain ⟨b, -, hb⟩ := Finset.mem_image.1 hq
    exact ((Prod.mk.injEq _ _ _ _ ▸ hb).1).symm

/-- **Los pares cruzados y las incidencias faltantes suman el rectángulo completo.** -/
theorem card_crossingPairs_add_missingIncidences (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finset V) :
    (crossingPairs G P).card + missingIncidences G P
      = P.card * (outsideVertices P).card := by
  classical
  rw [card_crossingPairs, missingIncidences, ← Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl fun x _ => card_presentColumn_add_card_missingColumn G P x,
    Finset.sum_const, smul_eq_mul]

/-- Los pares cruzados son las interaristas raíz--exterior.  Este es el puente con la forma
`interedges` de Mathlib, que es la que usan los módulos de contabilidad. -/
theorem crossingPairs_eq_interedges (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finset V) :
    crossingPairs G P = G.interedges P (outsideVertices P) := by
  classical
  ext p
  rw [SimpleGraph.mem_interedges_iff, mem_crossingPairs, mem_outsideVertices]

/-- Sobre la raíz, la columna presente del complemento es la columna faltante del grafo. -/
theorem presentColumn_compl_eq_missingColumn (G : SimpleGraph V) [DecidableRel G.Adj]
    {P : Finset V} {x : V} (hx : x ∈ P) :
    presentColumn Gᶜ P x = missingColumn G P x := by
  classical
  ext y
  by_cases hy : y ∈ P
  · simp [presentColumn, missingColumn, hy]
  · have hxy : x ≠ y := by rintro rfl; exact hy hx
    simp [presentColumn, missingColumn, SimpleGraph.compl_adj, hxy, hy]

/-- Y por tanto las incidencias faltantes son los pares cruzados del complemento. -/
theorem card_crossingPairs_compl (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finset V) :
    (crossingPairs Gᶜ P).card = missingIncidences G P := by
  classical
  rw [card_crossingPairs, missingIncidences]
  exact Finset.sum_congr rfl fun x hx => by
    rw [presentColumn_compl_eq_missingColumn G hx]

/-- La forma `interedges` de las incidencias faltantes. -/
theorem missingIncidences_eq_card_interedges (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finset V) :
    missingIncidences G P = (Gᶜ.interedges P (outsideVertices P)).card := by
  classical
  rw [← card_crossingPairs_compl G P, crossingPairs_eq_interedges]

/-! ## 3. Las aristas cruzadas -/

/-- Las aristas con exactamente un extremo en la raíz. -/
noncomputable def crossingEdges (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finset V) : Finset (Sym2 V) :=
  (crossingPairs G P).image fun p => s(p.1, p.2)

/-- La correspondencia par cruzado ↦ arista es inyectiva: el extremo de la raíz y el de fuera
no se pueden confundir. -/
theorem crossingPairs_edge_injOn (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finset V) :
    Set.InjOn (fun p : V × V => s(p.1, p.2)) (crossingPairs G P : Set (V × V)) := by
  classical
  rintro ⟨x, u⟩ hxu ⟨y, v⟩ hyv hEq
  obtain ⟨hxP, huP, -⟩ := mem_crossingPairs.1 hxu
  obtain ⟨hyP, hvP, -⟩ := mem_crossingPairs.1 hyv
  rcases Sym2.eq_iff.1 hEq with ⟨h1, h2⟩ | ⟨h1, -⟩
  · subst h1; subst h2; rfl
  · exact absurd (h1 ▸ hxP) hvP

theorem card_crossingEdges (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finset V) :
    (crossingEdges G P).card = (crossingPairs G P).card :=
  Finset.card_image_of_injOn (crossingPairs_edge_injOn G P)

/-! ## 4. El reparto en tres bloques -/

private theorem mem_rootEdges_iff {G : SimpleGraph V} [DecidableRel G.Adj]
    {P : Finset V} {x y : V} (hadj : G.Adj x y) :
    s(x, y) ∈ rootEdges G P ↔ x ∈ P ∧ y ∈ P := by
  classical
  simp [rootEdges, SimpleGraph.mem_edgeFinset, hadj, Sym2.toFinset_mk_eq,
    Finset.insert_subset_iff]

private theorem mem_outsideEdges_iff {G : SimpleGraph V} [DecidableRel G.Adj]
    {P : Finset V} {x y : V} (hadj : G.Adj x y) :
    s(x, y) ∈ outsideEdges G P ↔ x ∉ P ∧ y ∉ P := by
  classical
  simp [outsideEdges, SimpleGraph.mem_edgeFinset, hadj, Sym2.toFinset_mk_eq,
    Finset.insert_subset_iff]

private theorem mem_crossingEdges_iff {G : SimpleGraph V} [DecidableRel G.Adj]
    {P : Finset V} {x y : V} (hadj : G.Adj x y) :
    s(x, y) ∈ crossingEdges G P ↔ (x ∈ P ∧ y ∉ P) ∨ (x ∉ P ∧ y ∈ P) := by
  classical
  constructor
  · intro h
    obtain ⟨⟨a, b⟩, hab, heq⟩ := Finset.mem_image.1 h
    obtain ⟨haP, hbP, -⟩ := mem_crossingPairs.1 hab
    rcases Sym2.eq_iff.1 heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨haP, hbP⟩
    · exact Or.inr ⟨hbP, haP⟩
  · intro h
    refine Finset.mem_image.2 ?_
    rcases h with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · exact ⟨(x, y), mem_crossingPairs.2 ⟨hx, hy, hadj⟩, rfl⟩
    · exact ⟨(y, x), mem_crossingPairs.2 ⟨hy, hx, hadj.symm⟩, Sym2.eq_swap⟩

/-- **Cada arista es de exactamente un tipo.** -/
theorem edgeFinset_eq_three_parts (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finset V) :
    G.edgeFinset = rootEdges G P ∪ outsideEdges G P ∪ crossingEdges G P := by
  classical
  ext e
  induction e with
  | _ x y =>
    constructor
    · intro he
      have hadj : G.Adj x y := by simpa using he
      by_cases hx : x ∈ P <;> by_cases hy : y ∈ P
      · exact Finset.mem_union_left _ (Finset.mem_union_left _
          ((mem_rootEdges_iff hadj).2 ⟨hx, hy⟩))
      · exact Finset.mem_union_right _ ((mem_crossingEdges_iff hadj).2 (Or.inl ⟨hx, hy⟩))
      · exact Finset.mem_union_right _ ((mem_crossingEdges_iff hadj).2 (Or.inr ⟨hx, hy⟩))
      · exact Finset.mem_union_left _ (Finset.mem_union_right _
          ((mem_outsideEdges_iff hadj).2 ⟨hx, hy⟩))
    · intro he
      rcases Finset.mem_union.1 he with h | h
      · rcases Finset.mem_union.1 h with h | h
        · exact (Finset.mem_filter.1 h).1
        · exact (Finset.mem_filter.1 h).1
      · obtain ⟨⟨a, b⟩, hab, heq⟩ := Finset.mem_image.1 h
        obtain ⟨-, -, hadj⟩ := mem_crossingPairs.1 hab
        rw [← heq]
        simpa using hadj

private theorem three_parts_disjoint (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finset V) :
    Disjoint (rootEdges G P) (outsideEdges G P) ∧
      Disjoint (rootEdges G P ∪ outsideEdges G P) (crossingEdges G P) := by
  classical
  refine ⟨Finset.disjoint_left.2 (Sym2.ind ?_), Finset.disjoint_left.2 (Sym2.ind ?_)⟩
  · intro x y he hf
    have hadj : G.Adj x y := by simpa using (Finset.mem_filter.1 he).1
    exact ((mem_outsideEdges_iff hadj).1 hf).1 ((mem_rootEdges_iff hadj).1 he).1
  · intro x y he hf
    have hadj : G.Adj x y := by
      rcases Finset.mem_union.1 he with h | h <;>
        simpa using (Finset.mem_filter.1 h).1
    rcases (mem_crossingEdges_iff hadj).1 hf with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;>
      rcases Finset.mem_union.1 he with h | h
    · exact hy ((mem_rootEdges_iff hadj).1 h).2
    · exact ((mem_outsideEdges_iff hadj).1 h).1 hx
    · exact hx ((mem_rootEdges_iff hadj).1 h).1
    · exact ((mem_outsideEdges_iff hadj).1 h).2 hy

theorem card_edgeFinset_eq_three_parts (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finset V) :
    G.edgeFinset.card = (rootEdges G P).card + (outsideEdges G P).card
      + (crossingEdges G P).card := by
  classical
  obtain ⟨h1, h2⟩ := three_parts_disjoint G P
  rw [edgeFinset_eq_three_parts G P, Finset.card_union_of_disjoint h2,
    Finset.card_union_of_disjoint h1]

/-! ## 5. La identidad que se consume -/

/-- **Aristas más defecto es igual a bloques más rectángulo completo.** -/
theorem card_edgeFinset_add_missingIncidences (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finset V) :
    G.edgeFinset.card + missingIncidences G P
      = (rootEdges G P).card + (outsideEdges G P).card
        + P.card * (outsideVertices P).card := by
  have h1 := card_edgeFinset_eq_three_parts G P
  have h2 := card_crossingPairs_add_missingIncidences G P
  have h3 := card_crossingEdges G P
  omega

/-- Toda columna faltante está acotada por la mayor. -/
theorem card_missingColumn_le_max (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finset V) {x : V} (hx : x ∈ P) :
    (missingColumn G P x).card ≤ maxMissingColumn G P :=
  Finset.le_sup (f := fun x => (missingColumn G P x).card) hx

end PaperIV.RootVocab

import PaperIV.NearRootWindow
import PaperIV.SplitEdgeCount

set_option maxHeartbeats 1000000

/-!
# La densidad de aristas del régimen cercano

El testigo estructural cercano dice dos cosas cuantitativas sobre el grafo: que
está a distancia de edición `≤ eps·n²` de un grafo completo-split con núcleo `C`,
y —por `PaperIV.NearRootWindow`— que `|C| = n/3` salvo `n/(3·10^4)`.  Juntas
determinan el número de aristas: el grafo completo-split con núcleo `n/3` tiene

```text
C(|C|,2) + |C|·(n − |C|) = 5n²/18 + O(n),
```

y la edición mueve como mucho `eps·n²` aristas.  Luego **todo grafo cordal
grande del régimen cercano tiene `5n²/18` aristas salvo `n²/10^4`**, es decir
densidad `5/9` respecto del máximo `n²/2`.

Esto no estaba disponible antes: el testigo daba la cercanía a la familia
completo-split, pero no el tamaño del núcleo, y sin el tamaño del núcleo la
familia contiene grafos con cualquier densidad entre `0` y `1/2`.
-/

namespace PaperIV.NearEdgeDensity

open PaperIV.NearH1StructureWitness
open PaperIV.GraphFamilyDistance
open PaperIV.SplitUniformIncidence
open PaperIV.Model
open PaperIV.SplitEdgeCount

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## 1. La edición mueve pocos cardinales -/

omit [Fintype V] in
/-- La distancia de edición controla la diferencia de cardinales. -/
theorem abs_sub_card_le_editDist (A B : Finset V) :
    |(A.card : ℚ) - (B.card : ℚ)| ≤ (PaperIV.EditMetric.editDist A B : ℚ) := by
  classical
  have hsymm : PaperIV.EditMetric.editDist A B = (symmDiff A B).card := rfl
  have hAB : A.card ≤ (symmDiff A B).card + B.card := by
    have hsub : A ⊆ (A \ B) ∪ B := by
      intro x hx
      by_cases hxB : x ∈ B
      · exact Finset.mem_union_right _ hxB
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.2 ⟨hx, hxB⟩)
    have h1 : A.card ≤ (A \ B).card + B.card :=
      le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
    have h2 : (A \ B).card ≤ (symmDiff A B).card :=
      Finset.card_le_card (fun x hx => Finset.mem_union_left _ hx)
    omega
  have hBA : B.card ≤ (symmDiff A B).card + A.card := by
    have hsub : B ⊆ (B \ A) ∪ A := by
      intro x hx
      by_cases hxA : x ∈ A
      · exact Finset.mem_union_right _ hxA
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.2 ⟨hx, hxA⟩)
    have h1 : B.card ≤ (B \ A).card + A.card :=
      le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
    have h2 : (B \ A).card ≤ (symmDiff A B).card :=
      Finset.card_le_card (fun x hx => Finset.mem_union_right _ hx)
    omega
  have hAB' : (A.card : ℚ) ≤ ((symmDiff A B).card : ℚ) + (B.card : ℚ) := by exact_mod_cast hAB
  have hBA' : (B.card : ℚ) ≤ ((symmDiff A B).card : ℚ) + (A.card : ℚ) := by exact_mod_cast hBA
  rw [abs_sub_le_iff, hsymm]
  constructor <;> linarith

/-! ## 2. El número de aristas del grafo completo-split -/

/-- El soporte de aristas del grafo completo-split con núcleo `C` y anfitriones
`univ \ C` tiene `C(|C|,2) + |C|·(n − |C|)` elementos. -/
theorem card_graphEdgeSupport_splitGraph (C : Finset V) :
    (graphEdgeSupport (splitGraph C (Finset.univ \ C))).card
      = C.card.choose 2 + C.card * (Fintype.card V - C.card) := by
  classical
  have hd : Disjoint C (Finset.univ \ C) := Finset.disjoint_sdiff
  have hcard : (Finset.univ \ C).card = Fintype.card V - C.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ C), Finset.card_univ]
  have h := card_graphEdges_splitGraph (Core := C) (Hosts := Finset.univ \ C) hd
  rw [hcard] at h
  rw [← h]
  congr 1
  ext e
  simp [graphEdges, graphEdgeSupport]

/-! ## 3. La cuenta escalar -/

/-- **La cuenta, sin grafos.**  Un núcleo de tamaño crítico y una edición
cuadrática pequeña fijan el número de aristas en `5n²/18`. -/
theorem abs_sub_five_eighteenths_le {n k e s : ℚ}
    (hn : 4 * (10 : ℚ) ^ 12 ≤ n) (hk0 : 0 ≤ k)
    (hwin : |3 * k - n| ≤ n / 10000)
    (hs : s = k * (k - 1) / 2 + k * (n - k))
    (he : |e - s| ≤ n ^ 2 / 10 ^ 12) :
    |e - 5 * n ^ 2 / 18| ≤ n ^ 2 / 10000 := by
  rw [abs_le] at hwin he ⊢
  obtain ⟨hw1, hw2⟩ := hwin
  obtain ⟨he1, he2⟩ := he
  subst hs
  constructor <;> nlinarith [sq_nonneg (3 * k - n), sq_nonneg n]

/-! ## 4. La densidad -/

/-- **Densidad de aristas del régimen cercano.**  Un testigo estructural cercano
fuerza `e(G) = 5n²/18` salvo `n²/10^4`; es decir, la densidad de aristas es `5/9`
del máximo, con error relativo `2·10^{-4}`. -/
theorem card_edgeFinset_near_five_eighteenths {G : SimpleGraph V} [DecidableRel G.Adj]
    [LinearOrder V] (W : NearStructureWitness G)
    (hn : 4 * (10 : ℚ) ^ 12 ≤ (Fintype.card V : ℚ)) :
    |(G.edgeFinset.card : ℚ) - 5 * (Fintype.card V : ℚ) ^ 2 / 18| ≤
      (Fintype.card V : ℚ) ^ 2 / 10000 := by
  classical
  have hkle : W.core.card ≤ Fintype.card V := by
    simpa [Finset.card_univ] using Finset.card_le_univ W.core
  have hcardSQ : ((graphEdgeSupport (splitGraph W.core (Finset.univ \ W.core))).card : ℚ)
      = (W.core.card : ℚ) * ((W.core.card : ℚ) - 1) / 2 +
        (W.core.card : ℚ) * ((Fintype.card V : ℚ) - (W.core.card : ℚ)) := by
    rw [card_graphEdgeSupport_splitGraph]
    push_cast [Nat.cast_sub hkle, Nat.cast_choose_two]
    ring
  have hdiff := abs_sub_card_le_editDist (V := Sym2 V) G.edgeFinset
    (graphEdgeSupport (splitGraph W.core (Finset.univ \ W.core)))
  have heditQ := W.core_edit_le
  dsimp [PaperIV.NearH1Calibration.eps] at heditQ
  refine abs_sub_five_eighteenths_le hn (by positivity)
    (PaperIV.NearRootWindow.core_card_near_third W hn) hcardSQ ?_
  calc |(G.edgeFinset.card : ℚ) -
        ((graphEdgeSupport (splitGraph W.core (Finset.univ \ W.core))).card : ℚ)|
      ≤ (PaperIV.EditMetric.editDist G.edgeFinset
          (graphEdgeSupport (splitGraph W.core (Finset.univ \ W.core))) : ℚ) := hdiff
    _ ≤ (Fintype.card V : ℚ) ^ 2 / 10 ^ 12 := by linarith

end PaperIV.NearEdgeDensity

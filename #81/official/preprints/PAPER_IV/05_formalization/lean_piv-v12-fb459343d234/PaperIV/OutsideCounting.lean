import PaperIV.RootVocabulary

/-!
# Conteos elementales en el exterior

Herramientas de conteo sobre el exterior de una raíz: grados exteriores, la desigualdad de
apretón de manos restringida a un subconjunto, y la cota de tamaño para cliques exteriores.
-/

open scoped BigOperators

namespace PaperIV.RootVocab

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Los vecinos de `y` que están fuera de la raíz `P`. -/
noncomputable def outNbrs (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finset V) (y : V) :
    Finset V := by
  classical
  exact (outsideVertices P).filter fun z => G.Adj y z

@[simp] theorem mem_outNbrs {G : SimpleGraph V} [DecidableRel G.Adj] {P : Finset V} {y z : V} :
    z ∈ outNbrs G P y ↔ z ∉ P ∧ G.Adj y z := by
  simp [outNbrs]

/-- Grado exterior y columna faltante son complementarios dentro del exterior. -/
theorem card_outNbrs_add_card_missingColumn (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finset V) (y : V) :
    (outNbrs G P y).card + (missingColumn G P y).card = (outsideVertices P).card := by
  classical
  rw [outNbrs, missingColumn, Finset.card_filter_add_card_filter_not]

/-- El número de pares ordenados adyacentes con la primera coordenada en `T ⊆ exterior` está
acotado por el doble del número de aristas exteriores. -/
theorem card_adj_pairs_le (G : SimpleGraph V) [DecidableRel G.Adj] (P T : Finset V)
    (hT : T ⊆ outsideVertices P) :
    ((T ×ˢ outsideVertices P).filter fun q => G.Adj q.1 q.2).card
      ≤ 2 * (outsideEdges G P).card := by
  classical
  set s := (T ×ˢ outsideVertices P).filter fun q : V × V => G.Adj q.1 q.2 with hs
  set f : V × V → Sym2 V := fun q => s(q.1, q.2) with hf
  have himg : Finset.image f s ⊆ outsideEdges G P := by
    intro b hb
    simp only [Finset.mem_image, hs, Finset.mem_filter, Finset.mem_product] at hb
    obtain ⟨q, ⟨⟨hq1, hq2⟩, hadj⟩, rfl⟩ := hb
    simp only [outsideEdges, Finset.mem_filter, SimpleGraph.mem_edgeFinset, hf]
    refine ⟨hadj, ?_⟩
    intro z hz
    rw [Sym2.mem_toFinset] at hz
    simp only [Sym2.mem_iff] at hz
    rcases hz with rfl | rfl
    · exact hT hq1
    · exact hq2
  have hfib : ∀ b ∈ Finset.image f s, {a ∈ s | f a = b}.card ≤ 2 := by
    intro b _
    induction b with
    | h x y =>
      have hsub : {a ∈ s | f a = s(x, y)} ⊆ ({(x, y), (y, x)} : Finset (V × V)) := by
        intro a ha
        simp only [Finset.mem_filter, hf] at ha
        have := ha.2
        rw [Sym2.eq_iff] at this
        rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · simp [Prod.ext_iff, h1, h2]
        · simp [Prod.ext_iff, h1, h2]
      calc {a ∈ s | f a = s(x, y)}.card ≤ ({(x, y), (y, x)} : Finset (V × V)).card :=
            Finset.card_le_card hsub
        _ ≤ 2 := Finset.card_insert_le _ _ |>.trans (by simp)
  calc s.card ≤ 2 * (Finset.image f s).card := Finset.card_le_mul_card_image s 2 hfib
    _ ≤ 2 * (outsideEdges G P).card := by
        exact Nat.mul_le_mul_left 2 (Finset.card_le_card himg)

/-- Apretón de manos restringido: la suma de grados exteriores sobre un subconjunto del
exterior no pasa del doble del número de aristas exteriores. -/
theorem sum_card_outNbrs_le (G : SimpleGraph V) [DecidableRel G.Adj] (P T : Finset V)
    (hT : T ⊆ outsideVertices P) :
    ∑ y ∈ T, (outNbrs G P y).card ≤ 2 * (outsideEdges G P).card := by
  classical
  have hsum : ∑ y ∈ T, (outNbrs G P y).card
      = ((T ×ˢ outsideVertices P).filter fun q => G.Adj q.1 q.2).card := by
    rw [Finset.card_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [outNbrs, Finset.card_filter]
  rw [hsum]
  exact card_adj_pairs_le G P T hT

/-- Un clique contenido en el exterior tiene a lo sumo `2·(aristas exteriores)` pares
ordenados, lo que acota su tamaño. -/
theorem clique_outside_card_mul_le (G : SimpleGraph V) [DecidableRel G.Adj] (P K : Finset V)
    (hK : K ⊆ outsideVertices P) (hclq : G.IsClique (K : Set V)) :
    K.card * (K.card - 1) ≤ 2 * (outsideEdges G P).card := by
  classical
  have hlow : ∀ y ∈ K, K.card - 1 ≤ (outNbrs G P y).card := by
    intro y hy
    have hsub : K.erase y ⊆ outNbrs G P y := by
      intro z hz
      have hz' : z ∈ K := Finset.mem_of_mem_erase hz
      have hne : z ≠ y := Finset.ne_of_mem_erase hz
      have hadj : G.Adj y z := hclq (by exact_mod_cast hy) (by exact_mod_cast hz') (Ne.symm hne)
      exact mem_outNbrs.2 ⟨by simpa using hK hz', hadj⟩
    calc K.card - 1 = (K.erase y).card := by rw [Finset.card_erase_of_mem hy]
      _ ≤ (outNbrs G P y).card := Finset.card_le_card hsub
  calc K.card * (K.card - 1) = ∑ _y ∈ K, (K.card - 1) := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ y ∈ K, (outNbrs G P y).card := Finset.sum_le_sum hlow
    _ ≤ 2 * (outsideEdges G P).card := sum_card_outNbrs_le G P K hK

end PaperIV.RootVocab

import A4S1.IndepHostingTools

/-!
# E14: the physical ledger of the three triangle families

* `exists_partition_of_three_families`: three families of triangles of `G` (absorption,
  phase I, phase II), each internally edge-disjoint and pairwise edge-disjoint across families,
  complete to an order-four clique partition with `|Q| + 2(|A| + |B| + |C|) = e(G)`.
  Every lost edge is a single `K₂` piece; every triangle pays two edges.
* `absorptionTriangles W M`: the triangles `{w, a, h}`, `(a, h) ∈ M w`, with their ledger
  (`card_absorptionTriangles = Σ_w |M w|`), cliques and edge-disjointness.
-/

namespace A4S1.Indep

open Finset A4S1.TerminalPacking PaperIV.FarRounding

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- **Ledger of three triangle families.** -/
theorem exists_partition_of_three_families (A B C : Finset (Finset V))
    (hA : ∀ K ∈ A, (∀ a ∈ K, ∀ b ∈ K, a ≠ b → G.Adj a b) ∧ K.card = 3)
    (hB : ∀ K ∈ B, (∀ a ∈ K, ∀ b ∈ K, a ≠ b → G.Adj a b) ∧ K.card = 3)
    (hC : ∀ K ∈ C, (∀ a ∈ K, ∀ b ∈ K, a ≠ b → G.Adj a b) ∧ K.card = 3)
    (hAA : ∀ K ∈ A, ∀ L ∈ A, K ≠ L → (K ∩ L).card ≤ 1)
    (hBB : ∀ K ∈ B, ∀ L ∈ B, K ≠ L → (K ∩ L).card ≤ 1)
    (hCC : ∀ K ∈ C, ∀ L ∈ C, K ≠ L → (K ∩ L).card ≤ 1)
    (hAB : ∀ K ∈ A, ∀ L ∈ B, (K ∩ L).card ≤ 1)
    (hAC : ∀ K ∈ A, ∀ L ∈ C, (K ∩ L).card ≤ 1)
    (hBC : ∀ K ∈ B, ∀ L ∈ C, (K ∩ L).card ≤ 1) :
    ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧
      Q.size + 2 * (A.card + B.card + C.card) = G.edgeFinset.card := by
  have hself : ∀ K : Finset V, K.card = 3 → (K ∩ K).card ≤ 1 → False := by
    intro K hK h; rw [inter_self, hK] at h; omega
  have dAB : Disjoint A B := disjoint_left.2 fun K hKA hKB =>
    hself K (hA K hKA).2 (hAB K hKA K hKB)
  have dAC : Disjoint A C := disjoint_left.2 fun K hKA hKC =>
    hself K (hA K hKA).2 (hAC K hKA K hKC)
  have dBC : Disjoint B C := disjoint_left.2 fun K hKB hKC =>
    hself K (hB K hKB).2 (hBC K hKB K hKC)
  have hcard : (A ∪ B ∪ C).card = A.card + B.card + C.card := by
    rw [card_union_of_disjoint (disjoint_union_left.2 ⟨dAC, dBC⟩),
      card_union_of_disjoint dAB]
  have hmem : ∀ K ∈ A ∪ B ∪ C, K ∈ A ∨ K ∈ B ∨ K ∈ C := by
    intro K hK
    simp only [mem_union] at hK
    tauto
  obtain ⟨Q, hQ4, hQ⟩ := exists_partition_of_triangles (G := G) (A ∪ B ∪ C)
    (fun K hK a ha b hb hab => by
      rcases hmem K hK with h | h | h
      · exact (hA K h).1 a ha b hb hab
      · exact (hB K h).1 a ha b hb hab
      · exact (hC K h).1 a ha b hb hab)
    (fun K hK => by
      rcases hmem K hK with h | h | h
      · exact (hA K h).2
      · exact (hB K h).2
      · exact (hC K h).2)
    (fun K hK L hL hKL => by
      rcases hmem K hK with h | h | h <;> rcases hmem L hL with h' | h' | h'
      · exact hAA K h L h' hKL
      · exact hAB K h L h'
      · exact hAC K h L h'
      · rw [inter_comm]; exact hAB L h' K h
      · exact hBB K h L h' hKL
      · exact hBC K h L h'
      · rw [inter_comm]; exact hAC L h' K h
      · rw [inter_comm]; exact hBC L h' K h
      · exact hCC K h L h' hKL)
  exact ⟨Q, hQ4, by rw [← hcard]; exact hQ⟩

/-- The absorption triangles `{w, a, h}`, `(a, h) ∈ M w`, `w ∈ W`. -/
def absorptionTriangles (W : Finset V) (M : V → Finset (V × V)) : Finset (Finset V) :=
  W.biUnion fun w => (M w).image fun p => ({w, p.1, p.2} : Finset V)

omit [Fintype V] in
theorem mem_absorptionTriangles {W : Finset V} {M : V → Finset (V × V)} {K : Finset V} :
    K ∈ absorptionTriangles W M ↔ ∃ w ∈ W, ∃ p ∈ M w, K = {w, p.1, p.2} := by
  simp only [absorptionTriangles, mem_biUnion, mem_image]
  constructor
  · rintro ⟨w, hw, p, hp, rfl⟩; exact ⟨w, hw, p, hp, rfl⟩
  · rintro ⟨w, hw, p, hp, rfl⟩; exact ⟨w, hw, p, hp, rfl⟩

section Absorption

variable (S H W : Finset V) (hSH : Disjoint S H) (hSW : Disjoint S W) (hHW : Disjoint H W)
  (M : V → Finset (V × V))
  (hM1 : ∀ w ∈ W, ∀ p ∈ M w, p.1 ∈ S ∧ p.2 ∈ H ∧ G.Adj w p.1 ∧ G.Adj w p.2 ∧ G.Adj p.1 p.2)
  (hM2 : ∀ w ∈ W, ∀ p ∈ M w, ∀ p' ∈ M w, (p.1 = p'.1 ∨ p.2 = p'.2) → p = p')
  (hM3 : ∀ w ∈ W, ∀ w' ∈ W, w ≠ w' → Disjoint (M w) (M w'))

include hSH hSW hHW hM1 in
omit [Fintype V] [DecidableRel G.Adj] in
theorem absorptionTriangles_clique :
    ∀ K ∈ absorptionTriangles W M, (∀ a ∈ K, ∀ b ∈ K, a ≠ b → G.Adj a b) ∧ K.card = 3 := by
  intro K hK
  obtain ⟨w, hw, p, hp, rfl⟩ := mem_absorptionTriangles.1 hK
  obtain ⟨h1, h2, h3, h4, h5⟩ := hM1 w hw p hp
  have hwa : w ≠ p.1 := fun e => disjoint_left.1 hSW h1 (e ▸ hw)
  have hwh : w ≠ p.2 := fun e => disjoint_left.1 hHW h2 (e ▸ hw)
  have hah : p.1 ≠ p.2 := fun e => disjoint_left.1 hSH h1 (e ▸ h2)
  refine ⟨?_, ?_⟩
  · intro a ha b hb hab
    simp only [mem_insert, mem_singleton] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
    all_goals first
      | exact absurd rfl hab
      | assumption
      | exact h3.symm
      | exact h4.symm
      | exact h5.symm
  · rw [card_insert_of_notMem (by simp [hwa, hwh]), card_pair hah]

include hSH hSW hHW hM1 hM2 hM3 in
omit [Fintype V] [DecidableRel G.Adj] in
theorem absorptionTriangles_inter :
    ∀ K ∈ absorptionTriangles W M, ∀ L ∈ absorptionTriangles W M, K ≠ L →
      (K ∩ L).card ≤ 1 := by
  intro K hK L hL hKL
  obtain ⟨w, hw, p, hp, rfl⟩ := mem_absorptionTriangles.1 hK
  obtain ⟨w', hw', p', hp', rfl⟩ := mem_absorptionTriangles.1 hL
  obtain ⟨h1, h2, -⟩ := hM1 w hw p hp
  obtain ⟨h1', h2', -⟩ := hM1 w' hw' p' hp'
  refine abs_inter_abs S H W hSH hw hw' hSW hHW h1 h2 h1' h2' ?_ ?_ hKL
  · rintro rfl hor
    have := hM2 w hw p hp p' hp' hor
    rw [this]; exact ⟨rfl, rfl⟩
  · intro hww e1 e2
    have hpp : p = p' := Prod.ext e1 e2
    exact disjoint_left.1 (hM3 w hw w' hw' hww) hp (hpp ▸ hp')

include hSH hSW hHW hM1 in
omit [Fintype V] [DecidableRel G.Adj] in
theorem card_absorptionTriangles :
    (absorptionTriangles W M).card = ∑ w ∈ W, (M w).card := by
  unfold absorptionTriangles
  rw [card_biUnion]
  · refine sum_congr rfl fun w hw => ?_
    apply card_image_of_injOn
    intro p hp p' hp' hpp
    obtain ⟨h1, h2, -⟩ := hM1 w hw p hp
    obtain ⟨h1', h2', -⟩ := hM1 w hw p' hp'
    have hmem1 : p.1 ∈ ({w, p'.1, p'.2} : Finset V) := by
      have : p.1 ∈ ({w, p.1, p.2} : Finset V) := by simp
      simpa only [hpp] using this
    have hmem2 : p.2 ∈ ({w, p'.1, p'.2} : Finset V) := by
      have : p.2 ∈ ({w, p.1, p.2} : Finset V) := by simp
      simpa only [hpp] using this
    simp only [mem_insert, mem_singleton] at hmem1 hmem2
    have e1 : p.1 = p'.1 := by
      rcases hmem1 with h | h | h
      · exact absurd (h ▸ hw) (disjoint_left.1 hSW h1)
      · exact h
      · exact absurd (h ▸ h2') (disjoint_left.1 hSH h1)
    have e2 : p.2 = p'.2 := by
      rcases hmem2 with h | h | h
      · exact absurd (h ▸ hw) (disjoint_left.1 hHW h2)
      · exact absurd (h ▸ h1') (disjoint_right.1 hSH h2)
      · exact h
    exact Prod.ext e1 e2
  · intro w hw w' hw' hww
    rw [Function.onFun, disjoint_left]
    intro K hK hK'
    obtain ⟨p, hp, rfl⟩ := mem_image.1 hK
    obtain ⟨p', hp', hpp⟩ := mem_image.1 hK'
    obtain ⟨h1', h2', -⟩ := hM1 w' hw' p' hp'
    have : w ∈ ({w', p'.1, p'.2} : Finset V) := by rw [hpp]; simp
    simp only [mem_insert, mem_singleton] at this
    rcases this with h | h | h
    · exact hww h
    · exact disjoint_left.1 hSW h1' (h ▸ hw)
    · exact disjoint_left.1 hHW h2' (h ▸ hw)

end Absorption

end A4S1.Indep

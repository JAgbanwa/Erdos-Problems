/-
  Part B (Phase 2) — existence of an octahedron under high min-degree.

  The corrected atomic absorber is the octahedron flex unit (`FlexGadget`). Here we show that
  a graph with large enough min-degree actually *contains* an octahedron `K_{2,2,2}`: six
  vertices in three pairs with all twelve cross edges present. Greedy construction via common
  neighbourhoods, reusing `card_common_neighbors_ge`.
-/
import Ax2.PartB.BKLO.Gadget

namespace Ax2.BKLO

open SimpleGraph Finset Ax2

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Inclusion–exclusion lower bound on an intersection. -/
theorem card_inter_ge (A B : Finset V) :
    A.card + B.card - Fintype.card V ≤ (A ∩ B).card := by
  have hunion : (A ∪ B).card ≤ Fintype.card V := by
    rw [← Finset.card_univ]; exact Finset.card_le_card (Finset.subset_univ _)
  have := Finset.card_union_add_card_inter A B
  omega

/-- **Octahedron existence.** If `3n + 2 ≤ 4·δ(G)`, then `G` contains an octahedron: six
distinct vertices `a₁,a₂,b₁,b₂,c₁,c₂` with all twelve cross edges between the three pairs. -/
theorem exists_octahedron (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : 3 * Fintype.card V + 2 ≤ 4 * G.minDegree) :
    ∃ a₁ a₂ b₁ b₂ c₁ c₂ : V,
      a₁ ≠ a₂ ∧ b₁ ≠ b₂ ∧ c₁ ≠ c₂ ∧
      a₁ ≠ b₁ ∧ a₁ ≠ b₂ ∧ a₂ ≠ b₁ ∧ a₂ ≠ b₂ ∧
      a₁ ≠ c₁ ∧ a₁ ≠ c₂ ∧ a₂ ≠ c₁ ∧ a₂ ≠ c₂ ∧
      b₁ ≠ c₁ ∧ b₁ ≠ c₂ ∧ b₂ ≠ c₁ ∧ b₂ ≠ c₂ ∧
      G.Adj a₁ b₁ ∧ G.Adj a₁ b₂ ∧ G.Adj a₂ b₁ ∧ G.Adj a₂ b₂ ∧
      G.Adj a₁ c₁ ∧ G.Adj a₁ c₂ ∧ G.Adj a₂ c₁ ∧ G.Adj a₂ c₂ ∧
      G.Adj b₁ c₁ ∧ G.Adj b₁ c₂ ∧ G.Adj b₂ c₁ ∧ G.Adj b₂ c₂ := by
  classical
  -- min-degree ≤ n, so 4n ≥ 3n+2, giving n ≥ 2
  have hmd : G.minDegree ≤ Fintype.card V := by
    rcases isEmpty_or_nonempty V with he | hne
    · haveI := he
      simp only [Fintype.card_eq_zero, Nat.le_zero]
      unfold SimpleGraph.minDegree
      simp [Finset.univ_eq_empty]
    · haveI := hne
      obtain ⟨v, hv⟩ := G.exists_minimal_degree_vertex
      rw [hv, ← G.card_neighborFinset_eq_degree v, ← Finset.card_univ]
      exact Finset.card_le_card (Finset.subset_univ _)
  have hn2 : 2 ≤ Fintype.card V := by omega
  -- pick a₁ ≠ a₂
  obtain ⟨a₁, -, a₂, -, ha⟩ := Finset.one_lt_card.mp
    (show 1 < (Finset.univ : Finset V).card by rw [Finset.card_univ]; omega)
  -- W = common neighbours of a₁, a₂
  set W := G.neighborFinset a₁ ∩ G.neighborFinset a₂ with hWdef
  have hWcard : 2 * G.minDegree - Fintype.card V ≤ W.card := by
    rw [hWdef]
    have hcn := card_common_neighbors_ge G a₁ a₂
    have h1 := G.minDegree_le_degree a₁
    have h2 := G.minDegree_le_degree a₂
    omega
  obtain ⟨b₁, hb₁, b₂, hb₂, hbne⟩ := Finset.one_lt_card.mp (show 1 < W.card by omega)
  -- U = common neighbours of b₁, b₂ inside W
  set U := (G.neighborFinset b₁ ∩ G.neighborFinset b₂) ∩ W with hUdef
  have hUcard : 4 * G.minDegree - 3 * Fintype.card V ≤ U.card := by
    rw [hUdef]
    have hbb := card_common_neighbors_ge G b₁ b₂
    have h1 := G.minDegree_le_degree b₁
    have h2 := G.minDegree_le_degree b₂
    have hint := card_inter_ge (G.neighborFinset b₁ ∩ G.neighborFinset b₂) W
    omega
  obtain ⟨c₁, hc₁, c₂, hc₂, hcne⟩ := Finset.one_lt_card.mp (show 1 < U.card by omega)
  -- unpack memberships
  have hbW : ∀ {b}, b ∈ W → G.Adj a₁ b ∧ G.Adj a₂ b := by
    intro b hb
    rw [hWdef, Finset.mem_inter, G.mem_neighborFinset, G.mem_neighborFinset] at hb
    exact ⟨hb.1, hb.2⟩
  have hcU : ∀ {c}, c ∈ U → G.Adj b₁ c ∧ G.Adj b₂ c ∧ c ∈ W := by
    intro c hc
    rw [hUdef, Finset.mem_inter, Finset.mem_inter, G.mem_neighborFinset, G.mem_neighborFinset] at hc
    exact ⟨hc.1.1, hc.1.2, hc.2⟩
  obtain ⟨hab₁1, hab₁2⟩ := hbW hb₁
  obtain ⟨hab₂1, hab₂2⟩ := hbW hb₂
  obtain ⟨hbc₁1, hbc₁2, hc₁W⟩ := hcU hc₁
  obtain ⟨hbc₂1, hbc₂2, hc₂W⟩ := hcU hc₂
  obtain ⟨hac₁1, hac₁2⟩ := hbW hc₁W
  obtain ⟨hac₂1, hac₂2⟩ := hbW hc₂W
  refine ⟨a₁, a₂, b₁, b₂, c₁, c₂, ha, hbne, hcne, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, hab₁1, hab₂1, hab₁2, hab₂2, hac₁1, hac₂1, hac₁2, hac₂2,
    hbc₁1, hbc₂1, hbc₁2, hbc₂2⟩
  -- distinctness from irreflexivity of the adjacencies
  · exact hab₁1.ne          -- a₁ ≠ b₁
  · exact hab₂1.ne          -- a₁ ≠ b₂
  · exact hab₁2.ne          -- a₂ ≠ b₁
  · exact hab₂2.ne          -- a₂ ≠ b₂
  · exact hac₁1.ne          -- a₁ ≠ c₁
  · exact hac₂1.ne          -- a₁ ≠ c₂
  · exact hac₁2.ne          -- a₂ ≠ c₁
  · exact hac₂2.ne          -- a₂ ≠ c₂
  · exact hbc₁1.ne          -- b₁ ≠ c₁
  · exact hbc₂1.ne          -- b₁ ≠ c₂
  · exact hbc₁2.ne          -- b₂ ≠ c₁
  · exact hbc₂2.ne          -- b₂ ≠ c₂

/-- **Octahedron existence avoiding a set `S`.** With `|S|` extra min-degree slack
(`3n + 2 + |S| ≤ 4·δ(G)`), the octahedron can be chosen with all six vertices outside `S`. Mirrors
`exists_octahedron`, picking each vertex from the `S`-free part of the relevant common
neighbourhood. -/
theorem exists_octahedron_avoiding (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)
    (h : 3 * Fintype.card V + 2 + S.card ≤ 4 * G.minDegree) :
    ∃ a₁ a₂ b₁ b₂ c₁ c₂ : V,
      a₁ ≠ a₂ ∧ b₁ ≠ b₂ ∧ c₁ ≠ c₂ ∧
      a₁ ≠ b₁ ∧ a₁ ≠ b₂ ∧ a₂ ≠ b₁ ∧ a₂ ≠ b₂ ∧
      a₁ ≠ c₁ ∧ a₁ ≠ c₂ ∧ a₂ ≠ c₁ ∧ a₂ ≠ c₂ ∧
      b₁ ≠ c₁ ∧ b₁ ≠ c₂ ∧ b₂ ≠ c₁ ∧ b₂ ≠ c₂ ∧
      G.Adj a₁ b₁ ∧ G.Adj a₁ b₂ ∧ G.Adj a₂ b₁ ∧ G.Adj a₂ b₂ ∧
      G.Adj a₁ c₁ ∧ G.Adj a₁ c₂ ∧ G.Adj a₂ c₁ ∧ G.Adj a₂ c₂ ∧
      G.Adj b₁ c₁ ∧ G.Adj b₁ c₂ ∧ G.Adj b₂ c₁ ∧ G.Adj b₂ c₂ ∧
      a₁ ∉ S ∧ a₂ ∉ S ∧ b₁ ∉ S ∧ b₂ ∉ S ∧ c₁ ∉ S ∧ c₂ ∉ S := by
  classical
  have hmd : G.minDegree ≤ Fintype.card V := by
    rcases isEmpty_or_nonempty V with he | hne
    · haveI := he
      simp only [Fintype.card_eq_zero, Nat.le_zero]
      unfold SimpleGraph.minDegree; simp [Finset.univ_eq_empty]
    · haveI := hne
      obtain ⟨v, hv⟩ := G.exists_minimal_degree_vertex
      rw [hv, ← G.card_neighborFinset_eq_degree v, ← Finset.card_univ]
      exact Finset.card_le_card (Finset.subset_univ _)
  -- generic `\S` lower bound
  have hsd : ∀ s : Finset V, s.card - S.card ≤ (s \ S).card := fun s => by
    have h1 : (s ∩ S).card ≤ S.card := Finset.card_le_card Finset.inter_subset_right
    have h2 : (s \ S).card + (s ∩ S).card = s.card := Finset.card_sdiff_add_card_inter s S
    omega
  -- pick a₁ ≠ a₂ in univ \ S
  have hunivS : Fintype.card V - S.card ≤ ((Finset.univ : Finset V) \ S).card := by
    have := hsd Finset.univ; rwa [Finset.card_univ] at this
  obtain ⟨a₁, ha₁, a₂, ha₂, ha⟩ := Finset.one_lt_card.mp
    (show 1 < ((Finset.univ : Finset V) \ S).card by omega)
  have ha₁S : a₁ ∉ S := (Finset.mem_sdiff.mp ha₁).2
  have ha₂S : a₂ ∉ S := (Finset.mem_sdiff.mp ha₂).2
  set W := G.neighborFinset a₁ ∩ G.neighborFinset a₂ with hWdef
  have hWcard : 2 * G.minDegree - Fintype.card V ≤ W.card := by
    rw [hWdef]
    have hcn := card_common_neighbors_ge G a₁ a₂
    have h1 := G.minDegree_le_degree a₁
    have h2 := G.minDegree_le_degree a₂
    omega
  have hWScard : W.card - S.card ≤ (W \ S).card := by
    exact hsd W
  obtain ⟨b₁, hb₁, b₂, hb₂, hbne⟩ := Finset.one_lt_card.mp (show 1 < (W \ S).card by omega)
  have hb₁S : b₁ ∉ S := (Finset.mem_sdiff.mp hb₁).2
  have hb₂S : b₂ ∉ S := (Finset.mem_sdiff.mp hb₂).2
  have hb₁W : b₁ ∈ W := (Finset.mem_sdiff.mp hb₁).1
  have hb₂W : b₂ ∈ W := (Finset.mem_sdiff.mp hb₂).1
  set U := (G.neighborFinset b₁ ∩ G.neighborFinset b₂) ∩ W with hUdef
  have hUcard : 4 * G.minDegree - 3 * Fintype.card V ≤ U.card := by
    rw [hUdef]
    have hbb := card_common_neighbors_ge G b₁ b₂
    have h1 := G.minDegree_le_degree b₁
    have h2 := G.minDegree_le_degree b₂
    have hint := card_inter_ge (G.neighborFinset b₁ ∩ G.neighborFinset b₂) W
    omega
  have hUScard : U.card - S.card ≤ (U \ S).card := by
    exact hsd U
  obtain ⟨c₁, hc₁, c₂, hc₂, hcne⟩ := Finset.one_lt_card.mp (show 1 < (U \ S).card by omega)
  have hc₁S : c₁ ∉ S := (Finset.mem_sdiff.mp hc₁).2
  have hc₂S : c₂ ∉ S := (Finset.mem_sdiff.mp hc₂).2
  have hc₁U : c₁ ∈ U := (Finset.mem_sdiff.mp hc₁).1
  have hc₂U : c₂ ∈ U := (Finset.mem_sdiff.mp hc₂).1
  have hbW : ∀ {b}, b ∈ W → G.Adj a₁ b ∧ G.Adj a₂ b := by
    intro b hb
    rw [hWdef, Finset.mem_inter, G.mem_neighborFinset, G.mem_neighborFinset] at hb
    exact ⟨hb.1, hb.2⟩
  have hcU : ∀ {c}, c ∈ U → G.Adj b₁ c ∧ G.Adj b₂ c ∧ c ∈ W := by
    intro c hc
    rw [hUdef, Finset.mem_inter, Finset.mem_inter, G.mem_neighborFinset, G.mem_neighborFinset] at hc
    exact ⟨hc.1.1, hc.1.2, hc.2⟩
  obtain ⟨hab₁1, hab₁2⟩ := hbW hb₁W
  obtain ⟨hab₂1, hab₂2⟩ := hbW hb₂W
  obtain ⟨hbc₁1, hbc₁2, hc₁W⟩ := hcU hc₁U
  obtain ⟨hbc₂1, hbc₂2, hc₂W⟩ := hcU hc₂U
  obtain ⟨hac₁1, hac₁2⟩ := hbW hc₁W
  obtain ⟨hac₂1, hac₂2⟩ := hbW hc₂W
  exact ⟨a₁, a₂, b₁, b₂, c₁, c₂, ha, hbne, hcne,
    hab₁1.ne, hab₂1.ne, hab₁2.ne, hab₂2.ne, hac₁1.ne, hac₂1.ne, hac₁2.ne, hac₂2.ne,
    hbc₁1.ne, hbc₂1.ne, hbc₁2.ne, hbc₂2.ne,
    hab₁1, hab₂1, hab₁2, hab₂2, hac₁1, hac₂1, hac₁2, hac₂2, hbc₁1, hbc₂1, hbc₁2, hbc₂2,
    ha₁S, ha₂S, hb₁S, hb₂S, hc₁S, hc₂S⟩

end Ax2.BKLO

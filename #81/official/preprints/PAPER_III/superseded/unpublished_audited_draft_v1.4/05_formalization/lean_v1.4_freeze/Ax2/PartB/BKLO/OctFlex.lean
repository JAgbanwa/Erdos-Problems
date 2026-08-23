/-
  Part B (Phase 2) — the octahedron in `G` is a flex unit (capstone).

  Connects `exists_octahedron` to the corrected gadget model: the twelve octahedron edges carry
  two distinct edge-disjoint triangle decompositions, each a family of `G`-3-cliques. So a dense
  `G` contains a `FlexUnit` realised by actual triangles of `G`. Proof by Aristotle.
-/
import Ax2.PartB.BKLO.FlexGadget
import Ax2.PartB.BKLO.OctExists

namespace Ax2.BKLO

open SimpleGraph Finset Ax2

variable {V : Type*} [Fintype V] [DecidableEq V]

set_option maxHeartbeats 1000000 in
theorem octahedron_flexUnit (G : SimpleGraph V) [DecidableRel G.Adj]
    (a₁ a₂ b₁ b₂ c₁ c₂ : V) (haa : a₁ ≠ a₂) (hbb : b₁ ≠ b₂) (hcc : c₁ ≠ c₂)
    (hab₁₁ : G.Adj a₁ b₁) (hab₂₁ : G.Adj a₁ b₂) (hab₁₂ : G.Adj a₂ b₁) (hab₂₂ : G.Adj a₂ b₂)
    (hac₁₁ : G.Adj a₁ c₁) (hac₂₁ : G.Adj a₁ c₂) (hac₁₂ : G.Adj a₂ c₁) (hac₂₂ : G.Adj a₂ c₂)
    (hbc₁₁ : G.Adj b₁ c₁) (hbc₂₁ : G.Adj b₁ c₂) (hbc₁₂ : G.Adj b₂ c₁) (hbc₂₂ : G.Adj b₂ c₂) :
    ∃ F : FlexUnit V, (∀ t ∈ F.dec1, G.IsNClique 3 t) ∧ (∀ t ∈ F.dec2, G.IsNClique 3 t) := by
  have htri (a b c : V) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
      triEdges {a, b, c} = {s(a,b), s(a,c), s(b,c)} := by
    ext e
    simp only [triEdges, mem_filter, mem_sym2_iff]
    induction e using Sym2.inductionOn with | _ x y =>
      simp only [Sym2.mk_isDiag_iff]
      simp
      aesop
  have hab11 : a₁ ≠ b₁ := hab₁₁.ne
  have hab12 : a₁ ≠ b₂ := hab₂₁.ne
  have hab21 : a₂ ≠ b₁ := hab₁₂.ne
  have hab22 : a₂ ≠ b₂ := hab₂₂.ne
  have hac11 : a₁ ≠ c₁ := hac₁₁.ne
  have hac12 : a₁ ≠ c₂ := hac₂₁.ne
  have hac21 : a₂ ≠ c₁ := hac₁₂.ne
  have hac22 : a₂ ≠ c₂ := hac₂₂.ne
  have hbc11 : b₁ ≠ c₁ := hbc₁₁.ne
  have hbc12 : b₁ ≠ c₂ := hbc₂₁.ne
  have hbc21 : b₂ ≠ c₁ := hbc₁₂.ne
  have hbc22 : b₂ ≠ c₂ := hbc₂₂.ne
  have hba11 : b₁ ≠ a₁ := hab₁₁.ne'
  have hba12 : b₂ ≠ a₁ := hab₂₁.ne'
  have hba21 : b₁ ≠ a₂ := hab₁₂.ne'
  have hba22 : b₂ ≠ a₂ := hab₂₂.ne'
  have hca11 : c₁ ≠ a₁ := hac₁₁.ne'
  have hca12 : c₂ ≠ a₁ := hac₂₁.ne'
  have hca21 : c₁ ≠ a₂ := hac₁₂.ne'
  have hca22 : c₂ ≠ a₂ := hac₂₂.ne'
  have hcb11 : c₁ ≠ b₁ := hbc₁₁.ne'
  have hcb12 : c₂ ≠ b₁ := hbc₂₁.ne'
  have hcb21 : c₁ ≠ b₂ := hbc₁₂.ne'
  have hcb22 : c₂ ≠ b₂ := hbc₂₂.ne'
  have haa' : a₂ ≠ a₁ := Ne.symm haa
  have hbb' : b₂ ≠ b₁ := Ne.symm hbb
  have hcc' : c₂ ≠ c₁ := Ne.symm hcc
  have ht111 := htri a₁ b₁ c₁ hab11 hac11 hbc11
  have ht112 := htri a₁ b₁ c₂ hab11 hac12 hbc12
  have ht121 := htri a₁ b₂ c₁ hab12 hac11 hbc21
  have ht122 := htri a₁ b₂ c₂ hab12 hac12 hbc22
  have ht211 := htri a₂ b₁ c₁ hab21 hac21 hbc11
  have ht212 := htri a₂ b₁ c₂ hab21 hac22 hbc12
  have ht221 := htri a₂ b₂ c₁ hab22 hac21 hbc21
  have ht222 := htri a₂ b₂ c₂ hab22 hac22 hbc22
  let D₁ : Finset (Finset V) :=
    { {a₁, b₁, c₁}, {a₁, b₂, c₂}, {a₂, b₁, c₂}, {a₂, b₂, c₁} }
  let D₂ : Finset (Finset V) :=
    { {a₁, b₁, c₂}, {a₁, b₂, c₁}, {a₂, b₁, c₁}, {a₂, b₂, c₂} }
  let F : FlexUnit V := {
    edges := coveredEdges D₁
    dec1 := D₁
    dec2 := D₂
    card1 := by simp [D₁, hab11, hab12, hab21, hab22, hac11, hac12, hac21, hac22,
      hbc11, hbc12, hbc21, hbc22]
    card2 := by simp [D₂, hab11, hab12, hab21, hab22, hac11, hac12, hac21, hac22,
      hbc11, hbc12, hbc21, hbc22]
    disj1 := by
      simp only [EdgeDisjoint, D₁, mem_insert, mem_singleton]
      intro t₁ ht₁ t₂ ht₂ hn
      rcases ht₁ with rfl | rfl | rfl | rfl <;> rcases ht₂ with rfl | rfl | rfl | rfl
      all_goals simp_all [ht111, ht112, ht121, ht122, ht211, ht212, ht221, ht222, Finset.disjoint_left, Sym2.eq_iff]
    disj2 := by
      simp only [EdgeDisjoint, D₂, mem_insert, mem_singleton]
      intro t₁ ht₁ t₂ ht₂ hn
      rcases ht₁ with rfl | rfl | rfl | rfl <;> rcases ht₂ with rfl | rfl | rfl | rfl
      all_goals simp_all [ht111, ht112, ht121, ht122, ht211, ht212, ht221, ht222, Finset.disjoint_left, Sym2.eq_iff]
    cover1 := rfl
    cover2 := by
      simp only [coveredEdges, D₁, D₂, biUnion_insert, singleton_biUnion]
      rw [htri a₁ b₁ c₂ hab11 hac12 hbc12, htri a₁ b₂ c₁ hab12 hac11 hbc21,
        htri a₂ b₁ c₁ hab21 hac21 hbc11, htri a₂ b₂ c₂ hab22 hac22 hbc22,
        htri a₁ b₁ c₁ hab11 hac11 hbc11, htri a₁ b₂ c₂ hab12 hac12 hbc22,
        htri a₂ b₁ c₂ hab21 hac22 hbc12, htri a₂ b₂ c₁ hab22 hac21 hbc21]
      ext e
      simp only [mem_union, mem_insert, mem_singleton]
      tauto
    distinct := by
      intro heq
      have hm : {a₁, b₁, c₁} ∈ D₂ := by
        rw [← heq]
        simp [D₁]
      simp only [D₂, mem_insert, mem_singleton] at hm
      rcases hm with h | h | h | h
      · have hx : c₁ ∈ ({a₁, b₁, c₂} : Finset V) := by rw [← h]; simp
        simp_all
      · have hx : b₁ ∈ ({a₁, b₂, c₁} : Finset V) := by rw [← h]; simp
        simp_all
      · have hx : a₁ ∈ ({a₂, b₁, c₁} : Finset V) := by rw [← h]; simp
        simp_all
      · have hx : a₁ ∈ ({a₂, b₂, c₂} : Finset V) := by rw [← h]; simp
        simp_all }
  refine ⟨F, ?_, ?_⟩
  · intro t ht
    simp only [F, D₁, mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl
    all_goals constructor
    all_goals simp_all [SimpleGraph.IsClique]
  · intro t ht
    simp only [F, D₂, mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl
    all_goals constructor
    all_goals simp_all [SimpleGraph.IsClique]

/-- **Capstone.** A graph with `3n + 2 ≤ 4·δ(G)` contains a `FlexUnit` realised by actual
triangles of `G`: the octahedron from `exists_octahedron`, with its two triangle decompositions
(all `G`-3-cliques). The flexible-unit foundation of the absorption method, from min-degree
alone. -/
theorem exists_flexUnit_of_minDegree (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : 3 * Fintype.card V + 2 ≤ 4 * G.minDegree) :
    ∃ F : FlexUnit V, (∀ t ∈ F.dec1, G.IsNClique 3 t) ∧ (∀ t ∈ F.dec2, G.IsNClique 3 t) := by
  obtain ⟨a₁, a₂, b₁, b₂, c₁, c₂, haa, hbb, hcc, _, _, _, _, _, _, _, _, _, _, _, _,
    hb11, hb21, hb12, hb22, hc11, hc21, hc12, hc22, hd11, hd21, hd12, hd22⟩ :=
    exists_octahedron G h
  exact octahedron_flexUnit G a₁ a₂ b₁ b₂ c₁ c₂ haa hbb hcc
    hb11 hb21 hb12 hb22 hc11 hc21 hc12 hc22 hd11 hd21 hd12 hd22

end Ax2.BKLO

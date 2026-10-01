/-
A4 terminal structure: rooted defect `≤ s` allows at most `s` "exceptional" vertices of comparator type.

In the comparator `(K_r ⊔ I_s) ∨ I_h` the `s` vertices of `I_s` see every host and none of the core. This lemma says
rooted defect `≤ s` forbids `s + 1` of them. Suppose there are
* a nonempty clique `A` (the core),
* an independent set `H` of at least `s + 2` hosts, each adjacent to all of `A`,
* an independent set `X` of at least `s + 1` vertices, each adjacent to all of `H` and to none of `A`.
Then `RootedDefectAt G s` fails. Take `U = A ∪ H ∪ X` with root `R = A`: a host has neighbourhood `A ∪ X`, whose
largest clique has `|A|` vertices, so its defect is `|X| ≥ s + 1`. A vertex of `X` has neighbourhood `H`, which is
independent, so its defect is `|H| − 1 ≥ s + 1`.

So a regularized terminal root at defect `s` has the shape `C = A ∪ X` with `|X| ≤ s` exceptional vertices, as in
the comparator (for `s = 1` this is the single defective vertex `x` of `RegularizedTerminalRootS1`).

Layer E (unconditional): axiom target = {propext, Classical.choice, Quot.sound}.
-/
import PaperIV.RootedSimplicialDefect

namespace PaperIV.A4Exceptional

open Finset PaperIV.RootedSimplicialDefect

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [Fintype V] [DecidableRel G.Adj] in
/-- A clique inside an independent set has at most one vertex. -/
theorem card_le_one_of_clique_of_indep {C S : Finset V} (hCS : C ⊆ S) (hC : G.IsClique (C : Set V))
    (hS : ∀ x ∈ S, ∀ y ∈ S, ¬ G.Adj x y) : C.card ≤ 1 := by
  rw [Finset.card_le_one]
  intro x hx y hy
  by_contra hxy
  exact hS x (hCS hx) y (hCS hy) (hC hx hy hxy)

omit [Fintype V] in
/-- **At most `s` exceptional vertices.** -/
theorem not_rootedDefect_of_exceptional {s : ℕ} (hG : RootedDefectAt G s) (A H X : Finset V)
    (hA : G.IsClique (A : Set V)) (hAne : A.Nonempty)
    (hAH : Disjoint A H) (hAX : Disjoint A X)
    (hHind : ∀ h ∈ H, ∀ h' ∈ H, ¬ G.Adj h h') (hXind : ∀ x ∈ X, ∀ x' ∈ X, ¬ G.Adj x x')
    (hHA : ∀ h ∈ H, ∀ a ∈ A, G.Adj h a) (hHXadj : ∀ h ∈ H, ∀ x ∈ X, G.Adj h x)
    (hXA : ∀ x ∈ X, ∀ a ∈ A, ¬ G.Adj x a)
    (hH : s + 2 ≤ H.card) (hX : s + 1 ≤ X.card) : False := by
  classical
  set U := A ∪ H ∪ X with hU
  have hHne : H.Nonempty := card_pos.mp (by omega)
  obtain ⟨h0, hh0⟩ := hHne
  obtain ⟨v, hv, C, hCsub, hCcl, hcard⟩ :=
    hG U A (by intro a ha; simp [hU, ha]) hA ⟨h0, by
      rw [mem_sdiff]; exact ⟨by simp [hU, hh0], fun ha => disjoint_left.mp hAH ha hh0⟩⟩
  rw [mem_sdiff] at hv
  obtain ⟨hvU, hvA⟩ := hv
  have hvHX : v ∈ H ∨ v ∈ X := by
    simp only [hU, mem_union] at hvU
    rcases hvU with (h | h) | h
    · exact absurd h hvA
    · exact Or.inl h
    · exact Or.inr h
  rcases hvHX with hvH | hvX
  · -- a host sees exactly `A ∪ X`
    have hN : neighborsIn G U v = A ∪ X := by
      ext w
      simp only [neighborsIn, mem_filter, hU, mem_union]
      constructor
      · rintro ⟨(hw | hw) | hw, hadj⟩
        · exact Or.inl hw
        · exact absurd hadj (hHind v hvH w hw)
        · exact Or.inr hw
      · rintro (hw | hw)
        · exact ⟨Or.inl (Or.inl hw), hHA v hvH w hw⟩
        · exact ⟨Or.inr hw, hHXadj v hvH w hw⟩
    rw [hN, card_union_of_disjoint hAX] at hcard
    rw [hN] at hCsub
    -- a clique inside `A ∪ X` has at most `|A|` vertices
    have hCA : C.card ≤ A.card := by
      by_cases hmeet : ∃ x ∈ C, x ∈ X
      · obtain ⟨x, hxC, hxX⟩ := hmeet
        have hC1 : C ⊆ {x} := by
          intro c hc
          by_contra hcx
          rw [mem_singleton] at hcx
          have hadj := hCcl hc hxC hcx
          rcases mem_union.mp (hCsub hc) with hcA | hcX
          · exact hXA x hxX c hcA hadj.symm
          · exact hXind c hcX x hxX hadj
        have := card_le_card hC1
        rw [card_singleton] at this
        have := hAne.card_pos
        omega
      · push_neg at hmeet
        have hCA' : C ⊆ A := by
          intro c hc
          rcases mem_union.mp (hCsub hc) with h | h
          · exact h
          · exact absurd h (hmeet c hc)
        exact card_le_card hCA'
    omega
  · -- an exceptional vertex sees exactly `H`
    have hN : neighborsIn G U v = H := by
      ext w
      simp only [neighborsIn, mem_filter, hU, mem_union]
      constructor
      · rintro ⟨(hw | hw) | hw, hadj⟩
        · exact absurd hadj (hXA v hvX w hw)
        · exact hw
        · exact absurd hadj (hXind v hvX w hw)
      · intro hw
        exact ⟨Or.inl (Or.inr hw), (hHXadj w hw v hvX).symm⟩
    rw [hN] at hcard hCsub
    have := card_le_one_of_clique_of_indep hCsub hCcl hHind
    omega

end PaperIV.A4Exceptional

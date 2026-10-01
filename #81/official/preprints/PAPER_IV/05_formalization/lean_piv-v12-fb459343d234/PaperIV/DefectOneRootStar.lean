/-
Rooted defect one: the non-edges of a "richly connected" vertex set form a star.

This is the defect-one replacement for the single use of chordality in the near-H1 root regularization
(`PaperIV.RootVocab.regularizedRootSet_isClique`, via `no_induced_fourCycle`). There, the regularized root
`(P ∖ strays) ∪ hubs` is a clique. At rooted defect one it is a clique up to one exceptional vertex `x`, which is
the tolerant §1.2 shape `C = A ⊔ {x}` (`A4S1.TerminalTolerant.tolerantTwoPhase_core`).

* `not_rootedDefectOne_of_rich`: let `Y` be a vertex set whose cliques all have at most `|Y| − 2` vertices. Suppose
  `T` is an independent set of at least three vertices, disjoint from `Y` and complete to `Y`. Then `G` does not
  have rooted defect one. Take `U = Y ∪ T` with empty root. A vertex of `T` sees exactly `Y`, so its defect is at
  least 2. A vertex of `Y` sees all of `T`, which is independent, so its defect is at least `|T| − 1 ≥ 2`.
* `exists_erase_isClique_of_rich`: take `W` such that every `Y ⊆ W` with `|Y| ≤ 4` has such a `T`. Then `W` is a
  clique, or `W ∖ {x}` is a clique for some `x ∈ W`. The non-edges inside `W` contain no two disjoint pairs and no
  independent triple, so they form a star.

Layer E (unconditional): axiom target = {propext, Classical.choice, Quot.sound}.
-/
import PaperIV.A4ExceptionalBound

namespace PaperIV.DefectOneRootStar

open Finset PaperIV.RootedSimplicialDefect

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- **The rich obstruction.** -/
theorem not_rootedDefectOne_of_rich (hG : RootedDefectAt G 1) (Y T : Finset V)
    (hTY : Disjoint T Y) (hT3 : 3 ≤ T.card) (hTind : ∀ t ∈ T, ∀ t' ∈ T, ¬ G.Adj t t')
    (hTadj : ∀ t ∈ T, ∀ y ∈ Y, G.Adj t y)
    (hY : ∀ C ⊆ Y, G.IsClique (C : Set V) → C.card + 2 ≤ Y.card) : False := by
  obtain ⟨t0, ht0⟩ : T.Nonempty := card_pos.1 (by omega)
  obtain ⟨v, hv, C, hCsub, hCcl, hcard⟩ := hG (Y ∪ T) ∅ (empty_subset _) (by simp)
    ⟨t0, by simp [ht0]⟩
  rw [sdiff_empty, mem_union] at hv
  rcases hv with hvY | hvT
  · -- `v ∈ Y` sees all of `T`
    have hvT : v ∉ T := fun h => disjoint_left.1 hTY h hvY
    have hTN : T ⊆ neighborsIn G (Y ∪ T) v := by
      intro t ht
      simp only [neighborsIn, mem_filter, mem_union]
      exact ⟨Or.inr ht, (hTadj t ht v hvY).symm⟩
    have hCT : (C ∩ T).card ≤ 1 :=
      PaperIV.A4Exceptional.card_le_one_of_clique_of_indep inter_subset_right
        (hCcl.subset (by rw [coe_inter]; exact Set.inter_subset_left)) hTind
    have h1 := card_inter_add_card_sdiff C T
    have h2 : (C \ T).card ≤ (neighborsIn G (Y ∪ T) v \ T).card :=
      card_le_card (sdiff_subset_sdiff hCsub (subset_refl T))
    have h3 := card_sdiff_add_card_eq_card hTN
    omega
  · -- `v ∈ T` sees exactly `Y`
    have hN : neighborsIn G (Y ∪ T) v = Y := by
      ext w
      simp only [neighborsIn, mem_filter, mem_union]
      constructor
      · rintro ⟨hw | hw, hadj⟩
        · exact hw
        · exact absurd hadj (hTind v hvT w hw)
      · intro hw
        exact ⟨Or.inl hw, hTadj v hvT w hw⟩
    rw [hN] at hCsub hcard
    have := hY C hCsub hCcl
    omega

omit [DecidableRel G.Adj] in
/-- A clique inside `{a, b, c, d}`, with `a ≁ b` and `c ≁ d`, has at most two vertices. -/
theorem card_clique_le_two_of_two_nonedges {a b c d : V} (hab : ¬ G.Adj a b) (hcd : ¬ G.Adj c d)
    {C : Finset V} (hC : C ⊆ {a, b, c, d}) (hCcl : G.IsClique (C : Set V)) : C.card ≤ 2 := by
  classical
  have hsub : C ⊆ {if a ∈ C then a else b, if c ∈ C then c else d} := by
    intro z hz
    have hz' := hC hz
    simp only [mem_insert, mem_singleton] at hz' ⊢
    rcases hz' with h | h | h | h
    · have ha : a ∈ C := h ▸ hz
      left; rw [if_pos ha]; exact h
    · by_cases ha : a ∈ C
      · by_cases hza : z = a
        · left; rw [if_pos ha]; exact hza
        · exact absurd (by rw [← h]; exact hCcl ha hz (Ne.symm hza)) hab
      · left; rw [if_neg ha]; exact h
    · have hc : c ∈ C := h ▸ hz
      right; rw [if_pos hc]; exact h
    · by_cases hc : c ∈ C
      · by_cases hzc : z = c
        · right; rw [if_pos hc]; exact hzc
        · exact absurd (by rw [← h]; exact hCcl hc hz (Ne.symm hzc)) hcd
      · right; rw [if_neg hc]; exact h
  exact (card_le_card hsub).trans card_le_two

/-- **The non-edges of a rich set form a star.** -/
theorem exists_erase_isClique_of_rich (hG : RootedDefectAt G 1) (W : Finset V)
    (hrich : ∀ Y ⊆ W, Y.card ≤ 4 → ∃ T : Finset V, Disjoint T Y ∧ 3 ≤ T.card ∧
      (∀ t ∈ T, ∀ t' ∈ T, ¬ G.Adj t t') ∧ ∀ t ∈ T, ∀ y ∈ Y, G.Adj t y) :
    G.IsClique (W : Set V) ∨ ∃ x ∈ W, G.IsClique ((W.erase x : Finset V) : Set V) := by
  classical
  -- two disjoint non-edges are impossible
  have hpair : ∀ a ∈ W, ∀ b ∈ W, ∀ c ∈ W, ∀ d ∈ W, a ≠ b → c ≠ d → a ≠ c → a ≠ d → b ≠ c →
      b ≠ d → ¬ G.Adj a b → ¬ G.Adj c d → False := by
    intro a ha b hb c hc d hd hab hcd hac had hbc hbd hnab hncd
    have hY4 : ({a, b, c, d} : Finset V).card = 4 := by
      rw [card_insert_of_notMem (by simp [hab, hac, had]),
        card_insert_of_notMem (by simp [hbc, hbd]), card_pair hcd]
    obtain ⟨T, hTY, hT3, hTind, hTadj⟩ := hrich {a, b, c, d}
      (by intro z hz; simp only [mem_insert, mem_singleton] at hz
          rcases hz with rfl | rfl | rfl | rfl <;> assumption)
      (by rw [hY4])
    refine not_rootedDefectOne_of_rich hG {a, b, c, d} T hTY hT3 hTind hTadj ?_
    intro C hC hCcl
    have := card_clique_le_two_of_two_nonedges hnab hncd hC hCcl
    omega
  -- an independent triple is impossible
  have htriple : ∀ a ∈ W, ∀ b ∈ W, ∀ c ∈ W, a ≠ b → a ≠ c → b ≠ c →
      ¬ G.Adj a b → ¬ G.Adj a c → ¬ G.Adj b c → False := by
    intro a ha b hb c hc hab hac hbc hnab hnac hnbc
    have hY3 : ({a, b, c} : Finset V).card = 3 := by
      rw [card_insert_of_notMem (by simp [hab, hac]), card_pair hbc]
    obtain ⟨T, hTY, hT3, hTind, hTadj⟩ := hrich {a, b, c}
      (by intro z hz; simp only [mem_insert, mem_singleton] at hz
          rcases hz with rfl | rfl | rfl <;> assumption)
      (by rw [hY3]; omega)
    have hind : ∀ x ∈ ({a, b, c} : Finset V), ∀ y ∈ ({a, b, c} : Finset V), ¬ G.Adj x y := by
      intro x hx y hy hxy
      simp only [mem_insert, mem_singleton] at hx hy
      rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
      all_goals first
        | exact G.loopless.irrefl _ hxy
        | exact hnab hxy
        | exact hnac hxy
        | exact hnbc hxy
        | exact hnab hxy.symm
        | exact hnac hxy.symm
        | exact hnbc hxy.symm
    refine not_rootedDefectOne_of_rich hG {a, b, c} T hTY hT3 hTind hTadj ?_
    intro C hC hCcl
    have := PaperIV.A4Exceptional.card_le_one_of_clique_of_indep hC hCcl hind
    omega
  by_cases hW : G.IsClique (W : Set V)
  · exact Or.inl hW
  right
  -- a first non-edge `a b`
  obtain ⟨a, ha, b, hb, hab, hnab⟩ : ∃ a ∈ W, ∃ b ∈ W, a ≠ b ∧ ¬ G.Adj a b := by
    by_contra h
    push_neg at h
    exact hW fun x hx y hy hxy => h x hx y hy hxy
  by_contra hno
  push_neg at hno
  -- a non-edge avoiding `a`, and one avoiding `b`
  have hnon : ∀ x ∈ W, ∃ c ∈ W, ∃ d ∈ W, c ≠ x ∧ d ≠ x ∧ c ≠ d ∧ ¬ G.Adj c d := by
    intro x hx
    have h := hno x hx
    by_contra hc
    push_neg at hc
    apply h
    intro c hc' d hd' hcd
    rw [mem_coe, mem_erase] at hc' hd'
    exact hc c hc'.2 d hd'.2 hc'.1 hd'.1 hcd
  obtain ⟨c, hc, d, hd, hca, hda, hcd, hncd⟩ := hnon a ha
  obtain ⟨e, he, f, hf, heb, hfb, hef, hnef⟩ := hnon b hb
  -- `{c, d}` must meet `{a, b}`, hence contain `b`
  have hbcd : c = b ∨ d = b := by
    by_contra h
    push_neg at h
    exact hpair a ha b hb c hc d hd hab hcd hca.symm hda.symm h.1.symm h.2.symm hnab hncd
  -- `{e, f}` must meet `{a, b}`, hence contain `a`
  have haef : e = a ∨ f = a := by
    by_contra h
    push_neg at h
    exact hpair a ha b hb e he f hf hab hef h.1.symm h.2.symm heb.symm hfb.symm hnab hnef
  -- normalize: a non-edge `b d'` with `d' ∉ {a, b}`, and a non-edge `a f'` with `f' ∉ {a, b}`
  obtain ⟨d', hd', hd'a, hd'b, hnbd⟩ : ∃ d' ∈ W, d' ≠ a ∧ d' ≠ b ∧ ¬ G.Adj b d' := by
    rcases hbcd with rfl | rfl
    · exact ⟨d, hd, hda, fun h => hcd h.symm, hncd⟩
    · exact ⟨c, hc, hca, hcd, fun h => hncd h.symm⟩
  obtain ⟨f', hf', hf'a, hf'b, hnaf⟩ : ∃ f' ∈ W, f' ≠ a ∧ f' ≠ b ∧ ¬ G.Adj a f' := by
    rcases haef with rfl | rfl
    · exact ⟨f, hf, fun h => hef h.symm, hfb, hnef⟩
    · exact ⟨e, he, hef, heb, fun h => hnef h.symm⟩
  by_cases hdf : d' = f'
  · subst hdf
    exact htriple a ha b hb d' hd' hab (Ne.symm hd'a) (Ne.symm hd'b) hnab hnaf hnbd
  · exact hpair b hb d' hd' a ha f' hf' (Ne.symm hd'b) (Ne.symm hf'a) (Ne.symm hab) hf'b.symm
      hd'a hdf hnbd hnaf

end PaperIV.DefectOneRootStar

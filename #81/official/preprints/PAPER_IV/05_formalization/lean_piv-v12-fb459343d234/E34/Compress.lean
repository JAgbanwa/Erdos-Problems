import E34.Trees

/-!
# E34 — lowest common ancestors and compression of a pinned tree

* `lca a b` — the lowest common ancestor; `onPath_iff`: `x` is on the path from `a` to `b` iff
  `lca a b` is an ancestor of `x` and `x` is an ancestor of `a` or of `b`.
* `lca_closed`: the set of pairwise lca's of a family is closed under `lca`.
* `compress`: every family of points `z : L → Fin K` of a rooted tree is the image, under a
  *path-preserving* map `ι`, of a family of vertices of a rooted tree `Γ` with at most `|L|²`
  vertices.  (This is our combinatorial substitute for "up to homeomorphism".)
-/

namespace E34

open Finset

open scoped Classical

namespace RTree

variable {K : ℕ} (T : RTree K)

theorem exists_lca (a b : Fin K) : ∃ l, T.Anc l a ∧ T.Anc l b ∧
    ∀ c, T.Anc c a → T.Anc c b → T.Anc c l := by
  have hne : (univ.filter (fun c => T.Anc c a ∧ T.Anc c b)).Nonempty :=
    ⟨T.root, mem_filter.2 ⟨mem_univ _, T.anc_root a, T.anc_root b⟩⟩
  obtain ⟨l, hl, hmax⟩ := exists_max_image _ T.h hne
  rw [mem_filter] at hl
  refine ⟨l, hl.2.1, hl.2.2, fun c hca hcb => ?_⟩
  rcases T.anc_chain hca hl.2.1 with h | h
  · exact h
  · have := hmax c (mem_filter.2 ⟨mem_univ _, hca, hcb⟩)
    by_cases hcl : l = c
    · rw [hcl]; exact T.anc_refl c
    · exact absurd (T.h_lt_of_anc h hcl) (not_lt.2 this)

/-- Lowest common ancestor. -/
noncomputable def lca (a b : Fin K) : Fin K := (T.exists_lca a b).choose

theorem lca_anc_left (a b : Fin K) : T.Anc (T.lca a b) a := (T.exists_lca a b).choose_spec.1

theorem lca_anc_right (a b : Fin K) : T.Anc (T.lca a b) b := (T.exists_lca a b).choose_spec.2.1

theorem anc_lca {a b c : Fin K} (hca : T.Anc c a) (hcb : T.Anc c b) : T.Anc c (T.lca a b) :=
  (T.exists_lca a b).choose_spec.2.2 c hca hcb

theorem lca_self (a : Fin K) : T.lca a a = a :=
  (T.anc_antisymm (T.anc_lca (T.anc_refl a) (T.anc_refl a)) (T.lca_anc_left a a))

theorem lca_eq_of_anc {a b : Fin K} (h : T.Anc a b) : T.lca a b = a :=
  (T.anc_antisymm (T.anc_lca (T.anc_refl a) h) (T.lca_anc_left a b))

theorem lca_comm (a b : Fin K) : T.lca a b = T.lca b a :=
  T.anc_antisymm (T.anc_lca (T.lca_anc_right b a) (T.lca_anc_left b a))
    (T.anc_lca (T.lca_anc_right a b) (T.lca_anc_left a b))

/-- The path from `a` to `b`, explicitly. -/
theorem onPath_iff (a b x : Fin K) :
    T.OnPath a b x ↔ T.Anc (T.lca a b) x ∧ (T.Anc x a ∨ T.Anc x b) := by
  set l := T.lca a b
  constructor
  · intro hp
    set P := univ.filter (fun x => T.Anc l x ∧ (T.Anc x a ∨ T.Anc x b))
    have hP : T.IsSubAt P l := by
      refine T.isSubAt_of_closed P l ?_ ?_
      · exact mem_filter.2 ⟨mem_univ _, T.anc_refl _, Or.inl (T.lca_anc_left a b)⟩
      · intro y hy hyl
        rw [mem_filter] at hy
        obtain ⟨-, h1, h2⟩ := hy
        refine ⟨mem_filter.2 ⟨mem_univ _, ?_, ?_⟩, T.h_lt_of_anc h1 (Ne.symm hyl)⟩
        · rcases T.anc_step h1 with h | h
          · exact absurd h.symm hyl
          · exact h
        · rcases h2 with h | h
          · exact Or.inl (T.anc_trans (T.anc_par y) h)
          · exact Or.inr (T.anc_trans (T.anc_par y) h)
    have := hp P ⟨l, hP⟩ (mem_filter.2 ⟨mem_univ _, T.lca_anc_left a b, Or.inl (T.anc_refl a)⟩)
      (mem_filter.2 ⟨mem_univ _, T.lca_anc_right a b, Or.inr (T.anc_refl b)⟩)
    exact (mem_filter.1 this).2
  · rintro ⟨h1, h2⟩ S ⟨t, hS⟩ ha hb
    have htl : T.Anc t l := T.anc_lca (hS.2 a ha).1 (hS.2 b hb).1
    rcases h2 with h | h
    · exact hS.mem_of_between ha h (T.anc_trans htl h1)
    · exact hS.mem_of_between hb h (T.anc_trans htl h1)


/-- Four-point property of `lca`. -/
theorem lca_four (a b c d : Fin K) :
    T.lca (T.lca a b) (T.lca c d) = T.lca a b ∨ T.lca (T.lca a b) (T.lca c d) = T.lca c d ∨
    T.lca (T.lca a b) (T.lca c d) = T.lca a c := by
  set x := T.lca a b
  set y := T.lca c d
  set w := T.lca x y
  by_cases hwx : w = x
  · exact Or.inl hwx
  by_cases hwy : w = y
  · exact Or.inr (Or.inl hwy)
  right; right
  set m := T.lca a c
  have hwa : T.Anc w a := T.anc_trans (T.lca_anc_left x y) (T.lca_anc_left a b)
  have hwc : T.Anc w c := T.anc_trans (T.lca_anc_right x y) (T.lca_anc_left c d)
  have h1 : T.Anc w m := T.anc_lca hwa hwc
  have key : T.Anc m w := by
    rcases T.anc_chain (T.lca_anc_left a c) (T.lca_anc_left a b) with hmx | hxm
    · rcases T.anc_chain (T.lca_anc_right a c) (T.lca_anc_left c d) with hmy | hym
      · exact T.anc_lca hmx hmy
      · exact absurd (T.anc_antisymm (T.anc_lca (T.anc_trans hym hmx) (T.anc_refl y))
          (T.lca_anc_right x y)) hwy
    · have hxc : T.Anc x c := T.anc_trans hxm (T.lca_anc_right a c)
      rcases T.anc_chain hxc (T.lca_anc_left c d) with hxy | hyx
      · exact absurd (T.anc_antisymm (T.anc_lca (T.anc_refl x) hxy) (T.lca_anc_left x y)) hwx
      · exact absurd (T.anc_antisymm (T.anc_lca hyx (T.anc_refl y)) (T.lca_anc_right x y)) hwy
  exact T.anc_antisymm key h1

/-- **Compression.**  A family of points of a rooted tree is the path-preserving image of a
family of vertices of a rooted tree with at most `|L|²` vertices. -/
theorem compress {L : Type*} [Fintype L] [Nonempty L] (z : L → Fin K) :
    ∃ K0, K0 ≤ Fintype.card L ^ 2 ∧ ∃ Γ : RTree K0, ∃ y : L → Fin K0, ∃ ι : Fin K0 → Fin K,
      (∀ l, ι (y l) = z l) ∧ ∀ a b g, Γ.OnPath a b g → T.OnPath (ι a) (ι b) (ι g) := by
  set E : Finset (Fin K) := univ.image (fun p : L × L => T.lca (z p.1) (z p.2))
  have hEcard : E.card ≤ Fintype.card L ^ 2 :=
    card_image_le.trans (by simp [sq])
  have hzE : ∀ l, z l ∈ E := fun l => mem_image.2 ⟨(l, l), mem_univ _, T.lca_self _⟩
  have hclosed : ∀ e ∈ E, ∀ f ∈ E, T.lca e f ∈ E := by
    intro e he f hf
    obtain ⟨⟨p, q⟩, -, rfl⟩ := mem_image.1 he
    obtain ⟨⟨r, s⟩, -, rfl⟩ := mem_image.1 hf
    rcases T.lca_four (z p) (z q) (z r) (z s) with h | h | h <;> rw [h]
    · exact mem_image.2 ⟨(p, q), mem_univ _, rfl⟩
    · exact mem_image.2 ⟨(r, s), mem_univ _, rfl⟩
    · exact mem_image.2 ⟨(p, r), mem_univ _, rfl⟩
  have hEne : E.Nonempty := ⟨_, hzE (Classical.arbitrary L)⟩
  obtain ⟨e0, he0, hmin⟩ := exists_min_image E T.h hEne
  have he0anc : ∀ e ∈ E, T.Anc e0 e := by
    intro e he
    have h1 := hmin _ (hclosed e0 he0 e he)
    have : T.lca e0 e = e0 := by
      by_contra hne
      exact absurd (T.h_lt_of_anc (T.lca_anc_left e0 e) hne) (not_lt.2 h1)
    rw [← this]; exact T.lca_anc_right e0 e
  -- nearest proper ancestor inside `E`
  let F : Fin K → Finset (Fin K) := fun e => E.filter (fun f => T.Anc f e ∧ f ≠ e)
  let npa : Fin K → Fin K := fun e =>
    if h : (F e).Nonempty then (exists_max_image _ T.h h).choose else e
  have hnpa1 : ∀ e, (F e).Nonempty → npa e ∈ F e ∧ ∀ f ∈ F e, T.h f ≤ T.h (npa e) := by
    intro e h
    simp only [npa, h, dif_pos]
    exact (exists_max_image _ T.h h).choose_spec
  have hnpa2 : ∀ e, ¬ (F e).Nonempty → npa e = e := by
    intro e h; simp only [npa, h, dif_neg, not_false_eq_true]
  have hnpaE : ∀ e ∈ E, npa e ∈ E ∧ T.Anc (npa e) e := by
    intro e he
    by_cases h : (F e).Nonempty
    · have := (hnpa1 e h).1
      simp only [F, mem_filter] at this
      exact ⟨this.1, this.2.1⟩
    · rw [hnpa2 e h]; exact ⟨he, T.anc_refl e⟩
  -- enumeration of `E`
  set K0 := E.card
  let enc : Fin K0 ≃ E := E.equivFin.symm
  let ι : Fin K0 → Fin K := fun i => (enc i).1
  have hιE : ∀ i, ι i ∈ E := fun i => (enc i).2
  have hιinj : Function.Injective ι := fun i j h => enc.injective (Subtype.ext h)
  let dec : Fin K → Fin K0 := fun e => if h : e ∈ E then enc.symm ⟨e, h⟩ else enc.symm ⟨e0, he0⟩
  have hιdec : ∀ e ∈ E, ι (dec e) = e := by
    intro e he; simp only [dec, he, dif_pos, ι, Equiv.apply_symm_apply]
  have hdecι : ∀ i, dec (ι i) = i := fun i => hιinj (hιdec _ (hιE i))
  have hnoproper : ¬ (F e0).Nonempty := by
    rintro ⟨f, hf⟩
    simp only [F, mem_filter] at hf
    exact absurd (T.h_lt_of_anc hf.2.1 hf.2.2) (not_lt.2 (hmin f hf.1))
  let Γ : RTree K0 :=
    { par := fun i => dec (npa (ι i))
      root := dec e0
      h := fun i => T.h (ι i)
      par_root := by
        show dec (npa (ι (dec e0))) = dec e0
        rw [hιdec e0 he0, hnpa2 e0 hnoproper]
      h_par := by
        intro i hi
        show T.h (ι (dec (npa (ι i)))) < T.h (ι i)
        have hne : ι i ≠ e0 := fun h => hi (by rw [← hdecι i, h])
        have hF : (F (ι i)).Nonempty :=
          ⟨e0, mem_filter.2 ⟨he0, he0anc _ (hιE i), Ne.symm hne⟩⟩
        have := (hnpa1 _ hF).1
        simp only [F, mem_filter] at this
        rw [hιdec _ this.1]
        exact T.h_lt_of_anc this.2.1 this.2.2 }
  have hΓpar : ∀ i, ι (Γ.par i) = npa (ι i) := fun i => hιdec _ (hnpaE _ (hιE i)).1
  have anc_fwd : ∀ i j, Γ.Anc i j → T.Anc (ι i) (ι j) := by
    rintro i j ⟨k, rfl⟩
    induction k generalizing j with
    | zero => exact T.anc_refl _
    | succ k ih =>
      rw [Function.iterate_succ_apply]
      refine T.anc_trans (ih (Γ.par j)) ?_
      rw [hΓpar]; exact (hnpaE _ (hιE j)).2
  have anc_bwd : ∀ i j, T.Anc (ι i) (ι j) → Γ.Anc i j := by
    intro i j hij
    induction hm : T.h (ι j) using Nat.strong_induction_on generalizing j with
    | _ m ih =>
      by_cases he : ι i = ι j
      · rw [hιinj he]; exact Γ.anc_refl j
      have hF : (F (ι j)).Nonempty := ⟨ι i, mem_filter.2 ⟨hιE i, hij, he⟩⟩
      obtain ⟨hpF, hpmax⟩ := hnpa1 _ hF
      simp only [F, mem_filter] at hpF
      have hle := hpmax (ι i) (mem_filter.2 ⟨hιE i, hij, he⟩)
      rcases T.anc_chain hij hpF.2.1 with h | h
      · have hlt : T.h (ι (Γ.par j)) < m := by
          rw [hΓpar, ← hm]; exact T.h_lt_of_anc hpF.2.1 hpF.2.2
        have := ih _ hlt (Γ.par j) (by rw [hΓpar]; exact h) rfl
        exact Γ.anc_of_anc_par this
      · have hpi : npa (ι j) = ι i := by
          by_contra hne
          exact absurd (T.h_lt_of_anc h hne) (not_lt.2 hle)
        have : Γ.par j = i := hιinj (by rw [hΓpar, hpi])
        rw [← this]; exact Γ.anc_par j
  have hlca : ∀ a b, ι (Γ.lca a b) = T.lca (ι a) (ι b) := by
    intro a b
    have hlE := hclosed _ (hιE a) _ (hιE b)
    set l' := dec (T.lca (ι a) (ι b))
    have hl' : ι l' = T.lca (ι a) (ι b) := hιdec _ hlE
    have h1 : T.Anc (ι (Γ.lca a b)) (T.lca (ι a) (ι b)) :=
      T.anc_lca (anc_fwd _ _ (Γ.lca_anc_left a b)) (anc_fwd _ _ (Γ.lca_anc_right a b))
    have h2 : Γ.Anc l' (Γ.lca a b) :=
      Γ.anc_lca (anc_bwd _ _ (by rw [hl']; exact T.lca_anc_left _ _))
        (anc_bwd _ _ (by rw [hl']; exact T.lca_anc_right _ _))
    have h3 := anc_fwd _ _ h2
    rw [hl'] at h3
    exact (T.anc_antisymm h3 h1)
  refine ⟨K0, hEcard, Γ, fun l => dec (z l), ι, fun l => hιdec _ (hzE l), ?_⟩
  intro a b g hg
  rw [Γ.onPath_iff] at hg
  rw [T.onPath_iff, ← hlca]
  obtain ⟨h1, h2⟩ := hg
  refine ⟨anc_fwd _ _ h1, ?_⟩
  rcases h2 with h | h
  · exact Or.inl (anc_fwd _ _ h)
  · exact Or.inr (anc_fwd _ _ h)

end RTree

end E34

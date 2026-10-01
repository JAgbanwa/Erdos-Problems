import BoundedCliqueGap.CompleteSplit

/-
`BoundedCliqueGap.CSPorts` — declaration-level extract of the Route B
triangle-packing development.  Only the declarations in the constant cone of
`BoundedCliqueGap.chordal_gap_linear_cliqueFree` were kept (plus the few that
the retained sources need in order to elaborate); the module documentation
below is the original one and may advertise results that were pruned away.
-/

/-
# The port engine for complete split graphs

A packing of `CS K S` is assembled from two ingredients:

* a family of **port matchings** `M : S → Finset (Finset K)`: for each
  independent vertex `j`, a set of clique-part edges forming a matching, with
  the matchings of distinct independents using distinct clique edges.  Each
  port edge `e ∈ M j` yields the triangle `e ∪ {j}`.
* a **residual clique packing** `P` of `K_K` whose triangles avoid all port
  edges.

`nu3_CS_ge` says that the resulting family is an edge-disjoint triangle family
of `CS K S`, so `∑_j |M j| + |P| ≤ ν₃(CS K S)`.
-/

namespace BoundedCliqueGap

open Finset

variable {K S : Type*} [DecidableEq K] [DecidableEq S]

/-- The triangle spanned by a clique-part edge `e` and the independent vertex `j`. -/
def portTri (j : S) (e : Finset K) : Finset (K ⊕ S) := e.image Sum.inl ∪ {Sum.inr j}

lemma mem_portTri {j : S} {e : Finset K} {u : K ⊕ S} :
    u ∈ portTri j e ↔ (∃ a ∈ e, u = Sum.inl a) ∨ u = Sum.inr j := by
  simp only [portTri, Finset.mem_union, Finset.mem_image, Finset.mem_singleton]
  constructor
  · rintro (⟨a, ha, rfl⟩ | rfl)
    · exact Or.inl ⟨a, ha, rfl⟩
    · exact Or.inr rfl
  · rintro (⟨a, ha, rfl⟩ | rfl)
    · exact Or.inl ⟨a, ha, rfl⟩
    · exact Or.inr rfl

lemma portTri_eq_triple {j : S} {e : Finset K} {a b : K} (he : e = {a, b}) :
    portTri j e = {Sum.inl a, Sum.inl b, Sum.inr j} := by
  subst he
  ext u
  simp [mem_portTri, or_assoc]

lemma isTriangle_portTri {j : S} {e : Finset K} (he : e.card = 2) :
    IsTriangle (CS K S) (portTri j e) := by
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 he
  rw [portTri_eq_triple rfl]
  constructor
  · rw [Finset.card_insert_of_notMem (by simp [hab]),
      Finset.card_insert_of_notMem (by simp), Finset.card_singleton]
  · intro u hu v hv huv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
    rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;>
      simp_all [Sum.inl_injective.ne_iff]

/-- The image of a clique triangle inside `CS K S`. -/
lemma isTriangle_image_inl {T : Finset K} (hT : IsTriangle (⊤ : SimpleGraph K) T) :
    IsTriangle (CS K S) (T.image Sum.inl) :=
  hT.image Sum.inl_injective (fun u v huv => by simpa using huv.ne)

/-- An edge of a port triangle either joins two clique vertices of `e`, or joins
a clique vertex of `e` to `j`. -/
lemma mem_triEdges_portTri {j : S} {e : Finset K} {f : Sym2 (K ⊕ S)}
    (hf : f ∈ triEdges (portTri j e)) :
    (∃ a ∈ e, ∃ b ∈ e, a ≠ b ∧ f = s(Sum.inl a, Sum.inl b)) ∨
      (∃ a ∈ e, f = s(Sum.inl a, Sum.inr j)) := by
  obtain ⟨u, hu, v, hv, huv, rfl⟩ := mem_triEdges_iff.1 hf
  rw [mem_portTri] at hu hv
  rcases hu with ⟨a, ha, rfl⟩ | rfl
  · rcases hv with ⟨b, hb, rfl⟩ | rfl
    · exact Or.inl ⟨a, ha, b, hb, fun h => huv (by rw [h]), rfl⟩
    · exact Or.inr ⟨a, ha, rfl⟩
  · rcases hv with ⟨b, hb, rfl⟩ | rfl
    · exact Or.inr ⟨b, hb, Sym2.eq_swap⟩
    · exact absurd rfl huv

lemma eq_of_card_two_of_subset {e : Finset K} {a b : K} (hab : a ≠ b)
    (he : e.card = 2) (ha : a ∈ e) (hb : b ∈ e) : e = {a, b} := by
  refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  · rw [he, Finset.card_insert_of_notMem (by simp [hab]), Finset.card_singleton]

/-! ## The engine -/

variable [Fintype K] [Fintype S]

/-- **Port engine.**  Given port matchings `M` (pairwise edge-disjoint matchings
of the clique part, indexed by the independent vertices) and a packing `P` of
the clique part avoiding all port edges, the union is an edge-disjoint triangle
family of `CS K S`. -/
theorem nu3_CS_ge (M : S → Finset (Finset K)) (P : Finset (Finset K))
    (hcard2 : ∀ j, ∀ e ∈ M j, e.card = 2)
    (hmatch : ∀ j, ∀ e ∈ M j, ∀ e' ∈ M j, e ≠ e' → Disjoint e e')
    (hglob : ∀ j j' : S, ∀ e : Finset K, e ∈ M j → e ∈ M j' → j = j')
    (hP : IsPacking (⊤ : SimpleGraph K) P)
    (hPavoid : ∀ T ∈ P, ∀ j : S, ∀ e ∈ M j, ¬ e ⊆ T) :
    (∑ j : S, (M j).card) + P.card ≤ nu3 (CS K S) := by
  classical
  set Q : Finset ((_ : S) × Finset K) := Finset.univ.sigma M with hQ
  set A : Finset (Finset (K ⊕ S)) := Q.image (fun p => portTri p.1 p.2) with hA
  set B : Finset (Finset (K ⊕ S)) := P.image (fun T => T.image Sum.inl) with hB
  -- membership unfolding
  have hmemQ : ∀ p : (_ : S) × Finset K, p ∈ Q ↔ p.2 ∈ M p.1 := by
    intro p; simp [hQ, Finset.mem_sigma]
  -- the key disjointness of two distinct port triangles
  have hport_disj : ∀ p ∈ Q, ∀ p' ∈ Q, p ≠ p' →
      Disjoint (triEdges (portTri p.1 p.2)) (triEdges (portTri p'.1 p'.2)) := by
    rintro ⟨j, e⟩ hp ⟨j', e'⟩ hp' hne
    rw [hmemQ] at hp hp'
    simp only at hp hp' ⊢
    have hee' : e ≠ e' := by
      rintro rfl
      exact hne (Sigma.ext_iff.2 ⟨hglob j j' e hp hp', by simp⟩)
    rw [Finset.disjoint_left]
    intro f hf hf'
    rcases mem_triEdges_portTri hf with ⟨a, ha, b, hb, hab, rfl⟩ | ⟨a, ha, rfl⟩
    · -- a clique edge shared by both: forces `e = e'`
      rcases mem_triEdges_portTri hf' with ⟨a', ha', b', hb', hab', hEq⟩ | ⟨a', ha', hEq⟩
      · rw [Sym2.eq_iff] at hEq
        have hfin : a' ∈ e' ∧ b' ∈ e' := ⟨ha', hb'⟩
        rcases hEq with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · cases Sum.inl_injective h1; cases Sum.inl_injective h2
          exact hee' ((eq_of_card_two_of_subset hab (hcard2 j e hp) ha hb).trans
            (eq_of_card_two_of_subset hab (hcard2 j' e' hp') hfin.1 hfin.2).symm)
        · cases Sum.inl_injective h1; cases Sum.inl_injective h2
          exact hee' ((eq_of_card_two_of_subset hab (hcard2 j e hp) ha hb).trans
            (eq_of_card_two_of_subset hab (hcard2 j' e' hp')
              hfin.2 hfin.1).symm)
      · rw [Sym2.eq_iff] at hEq
        rcases hEq with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp_all
    · -- a cross edge shared by both: forces `j = j'` and `e ∩ e' ≠ ∅`
      rcases mem_triEdges_portTri hf' with ⟨a', ha', b', hb', hab', hEq⟩ | ⟨a', ha', hEq⟩
      · rw [Sym2.eq_iff] at hEq
        rcases hEq with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp at h1 h2
      · rw [Sym2.eq_iff] at hEq
        rcases hEq with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · cases Sum.inl_injective h1
          cases Sum.inr_injective h2
          exact (Finset.disjoint_left.1 (hmatch j e hp e' hp' hee')) ha ha'
        · simp at h1
  -- port triangles and clique triangles never share an edge
  have hmix_disj : ∀ p ∈ Q, ∀ T ∈ P,
      Disjoint (triEdges (portTri p.1 p.2)) (triEdges (T.image (Sum.inl : K → K ⊕ S))) := by
    rintro ⟨j, e⟩ hp T hT
    rw [hmemQ] at hp
    simp only at hp ⊢
    rw [Finset.disjoint_left]
    intro f hf hf'
    rw [triEdges_image Sum.inl_injective] at hf'
    obtain ⟨f₀, hf₀, rfl⟩ := Finset.mem_image.1 hf'
    obtain ⟨a', ha', b', hb', hab', rfl⟩ := mem_triEdges_iff.1 hf₀
    rcases mem_triEdges_portTri hf with ⟨a, ha, b, hb, hab, hEq⟩ | ⟨a, ha, hEq⟩
    · rw [Sym2.map_pair_eq, Sym2.eq_iff] at hEq
      have hsub : e ⊆ T := by
        rcases hEq with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · cases Sum.inl_injective h1; cases Sum.inl_injective h2
          rw [eq_of_card_two_of_subset hab (hcard2 j e hp) ha hb]
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl <;> assumption
        · cases Sum.inl_injective h1; cases Sum.inl_injective h2
          rw [eq_of_card_two_of_subset hab (hcard2 j e hp) ha hb]
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl <;> assumption
      exact hPavoid T hT j e hp hsub
    · rw [Sym2.map_pair_eq, Sym2.eq_iff] at hEq
      rcases hEq with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp at h2 h1
  -- injectivity of the two parametrisations
  have hinjA : Set.InjOn (fun p : (_ : S) × Finset K => portTri p.1 p.2) Q := by
    rintro ⟨j, e⟩ hp ⟨j', e'⟩ hp' hEq
    simp only at hEq
    by_contra hne
    exact (Finset.disjoint_left.1 (hport_disj _ hp _ hp' hne))
      (((isTriangle_portTri (hcard2 j e ((hmemQ _).1 hp))).triEdges_nonempty).choose_spec)
      (by
        rw [← hEq]
        exact ((isTriangle_portTri
          (hcard2 j e ((hmemQ _).1 hp))).triEdges_nonempty).choose_spec)
  have hinjB : Set.InjOn (fun T : Finset K => T.image (Sum.inl : K → K ⊕ S)) P :=
    fun T _ T' _ h => Finset.image_injective Sum.inl_injective h
  -- the two parts are disjoint
  have hAB : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro X hX hX'
    obtain ⟨⟨j, e⟩, hp, rfl⟩ := Finset.mem_image.1 hX
    obtain ⟨T, hT, hTeq⟩ := Finset.mem_image.1 hX'
    have : (Sum.inr j : K ⊕ S) ∈ portTri j e := by simp [mem_portTri]
    rw [← hTeq] at this
    simp at this
  -- cardinality
  have hcardA : A.card = ∑ j : S, (M j).card := by
    rw [hA, Finset.card_image_of_injOn hinjA, hQ, Finset.card_sigma]
  have hcardB : B.card = P.card := Finset.card_image_of_injOn hinjB
  have hcard : (A ∪ B).card = (∑ j : S, (M j).card) + P.card := by
    rw [Finset.card_union_of_disjoint hAB, hcardA, hcardB]
  -- the union is a packing
  refine le_trans (le_of_eq hcard.symm) (card_le_nu3 ⟨?_, ?_⟩)
  · intro X hX
    rcases Finset.mem_union.1 hX with hX | hX
    · obtain ⟨⟨j, e⟩, hp, rfl⟩ := Finset.mem_image.1 hX
      exact isTriangle_portTri (hcard2 j e ((hmemQ _).1 hp))
    · obtain ⟨T, hT, rfl⟩ := Finset.mem_image.1 hX
      exact isTriangle_image_inl (hP.1 T hT)
  · intro X hX Y hY hXY
    rcases Finset.mem_union.1 hX with hX | hX <;> rcases Finset.mem_union.1 hY with hY | hY
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hX
      obtain ⟨p', hp', rfl⟩ := Finset.mem_image.1 hY
      exact hport_disj p hp p' hp' (fun h => hXY (by rw [h]))
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hX
      obtain ⟨T, hT, rfl⟩ := Finset.mem_image.1 hY
      exact hmix_disj p hp T hT
    · obtain ⟨T, hT, rfl⟩ := Finset.mem_image.1 hX
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hY
      exact (hmix_disj p hp T hT).symm
    · obtain ⟨T, hT, rfl⟩ := Finset.mem_image.1 hX
      obtain ⟨T', hT', rfl⟩ := Finset.mem_image.1 hY
      have hne : T ≠ T' := fun h => hXY (by rw [h])
      rw [triEdges_image Sum.inl_injective, triEdges_image Sum.inl_injective]
      exact (Finset.disjoint_image (Sym2.map.injective Sum.inl_injective)).2
        (hP.2 T hT T' hT' hne)

/-! ## Monotonicity of `ν₃(CS -, -)` in both parts -/

lemma nu3_CS_mono {K K' S S' : Type*} [Fintype K] [DecidableEq K] [Fintype S] [DecidableEq S]
    [Fintype K'] [DecidableEq K'] [Fintype S'] [DecidableEq S']
    (f : K ↪ K') (g : S ↪ S') : nu3 (CS K S) ≤ nu3 (CS K' S') := by
  refine nu3_le_of_embedding ⟨Sum.map f g, ?_⟩ ?_
  · intro u v h
    cases u <;> cases v <;> simp_all [Sum.map, f.injective.eq_iff, g.injective.eq_iff]
  · rintro (a | i) (b | j) h <;> simp_all [Sum.map]

/-! ## Port matchings from a family of fixed-point-free involutions

The concrete constructions below produce their port matchings as the orbit
sets `{v, σ j v}` of a family of fixed-point-free involutions `σ j` of the
clique part.  Such a family gives *perfect* matchings, so each independent
vertex receives `|K|/2` ports. -/

omit [Fintype K] in
/-- Two-element sets are equal only in the two obvious ways. -/
lemma pair_eq_pair {a b c d : K} (hab : a ≠ b) (h : ({a, b} : Finset K) = {c, d}) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have ha : a ∈ ({c, d} : Finset K) := by rw [← h]; simp
  have hb : b ∈ ({c, d} : Finset K) := by rw [← h]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl
  · rcases hb with rfl | rfl
    · exact absurd rfl hab
    · exact Or.inl ⟨rfl, rfl⟩
  · rcases hb with rfl | rfl
    · exact Or.inr ⟨rfl, rfl⟩
    · exact absurd rfl hab

end BoundedCliqueGap

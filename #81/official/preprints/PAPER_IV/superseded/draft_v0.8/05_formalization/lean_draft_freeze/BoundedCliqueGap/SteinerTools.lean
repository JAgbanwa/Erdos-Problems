import BoundedCliqueGap.Ladder

/-
`BoundedCliqueGap.SteinerTools` — declaration-level extract of the Route B
triangle-packing development.  Only the declarations in the constant cone of
`BoundedCliqueGap.chordal_gap_linear_cliqueFree` were kept (plus the few that
the retained sources need in order to elaborate); the module documentation
below is the original one and may advertise results that were pruned away.
-/

/-
# Steiner ladder, rung S1 — general tools

* `card_triEdges` : a triangle has exactly three edges.
* `value_le_edges_third` : `F.value ≤ |E(G)|/3` for every fractional packing
  (each support triangle consumes three units of edge capacity).
* `nu3_le_of_embedding` : `nu3` is monotone along graph embeddings, and the
  clique form `nu3_top_le_of_card_le` : if `card α ≤ card β` then
  `nu3 (⊤ : SimpleGraph α) ≤ nu3 (⊤ : SimpleGraph β)`.
-/

namespace BoundedCliqueGap

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## The three edges of a triangle -/

omit [Fintype V] in
/-- The edge set of an explicit 3-element vertex set. -/
lemma triEdges_eq_of_card_three {T : Finset V} {a b c : V} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (hT : T = {a, b, c}) :
    triEdges T = {s(a, b), s(a, c), s(b, c)} := by
  subst hT
  ext e
  rw [mem_triEdges_iff]
  constructor
  · rintro ⟨u, hu, v, hv, huv, rfl⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv ⊢
    rcases hu with rfl|rfl|rfl <;> rcases hv with rfl|rfl|rfl <;> simp_all
  · intro he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl|rfl|rfl
    · exact ⟨a, by simp, b, by simp, hab, rfl⟩
    · exact ⟨a, by simp, c, by simp, hac, rfl⟩
    · exact ⟨b, by simp, c, by simp, hbc, rfl⟩

omit [Fintype V] in
/-- A triangle has exactly three edges. -/
lemma card_triEdges {G : SimpleGraph V} {T : Finset V} (hT : IsTriangle G T) :
    (triEdges T).card = 3 := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.1 hT.1
  rw [triEdges_eq_of_card_three hab hac hbc rfl,
    Finset.card_insert_of_notMem (by simp; tauto),
    Finset.card_insert_of_notMem (by simp; tauto), Finset.card_singleton]

omit [Fintype V] in
/-- The edges of a triangle of `G` are edges of `G`. -/
lemma triEdges_subset_edgeFinset {G : SimpleGraph V} [Fintype G.edgeSet] {T : Finset V}
    (hT : IsTriangle G T) : triEdges T ⊆ G.edgeFinset := by
  intro e he
  rw [SimpleGraph.mem_edgeFinset]
  exact mem_edgeSet_of_mem_triEdges hT he

/-! ## Rung S1(a) — the edge-capacity bound -/

/-! ## Rung S1(b) — monotonicity of `nu3` along embeddings -/

omit [Fintype V] in
/-- Edges of an injective image of a vertex set. -/
lemma triEdges_image {W : Type*} [DecidableEq W] {f : V → W} (hf : Function.Injective f)
    (T : Finset V) : triEdges (T.image f) = (triEdges T).image (Sym2.map f) := by
  ext e
  rw [mem_triEdges_iff]
  constructor
  · rintro ⟨u, hu, v, hv, huv, rfl⟩
    obtain ⟨u₀, hu₀, rfl⟩ := Finset.mem_image.1 hu
    obtain ⟨v₀, hv₀, rfl⟩ := Finset.mem_image.1 hv
    refine Finset.mem_image.2 ⟨s(u₀, v₀), mk_mem_triEdges hu₀ hv₀ (fun h => huv (by rw [h])), ?_⟩
    simp
  · intro he
    obtain ⟨e₀, he₀, rfl⟩ := Finset.mem_image.1 he
    obtain ⟨u, hu, v, hv, huv, rfl⟩ := mem_triEdges_iff.1 he₀
    exact ⟨f u, Finset.mem_image_of_mem f hu, f v, Finset.mem_image_of_mem f hv,
      fun h => huv (hf h), by simp⟩

omit [Fintype V] [DecidableEq V] in
/-- Triangles are carried along graph embeddings. -/
lemma IsTriangle.image {W : Type*} [DecidableEq W] {G : SimpleGraph V}
    {H : SimpleGraph W} {f : V → W} (hf : Function.Injective f)
    (hadj : ∀ u v, G.Adj u v → H.Adj (f u) (f v)) {T : Finset V} (hT : IsTriangle G T) :
    IsTriangle H (T.image f) := by
  refine ⟨by rw [Finset.card_image_of_injective _ hf, hT.1], ?_⟩
  intro u hu v hv huv
  obtain ⟨u₀, hu₀, rfl⟩ := Finset.mem_image.1 hu
  obtain ⟨v₀, hv₀, rfl⟩ := Finset.mem_image.1 hv
  exact hadj _ _ (hT.2 u₀ hu₀ v₀ hv₀ (fun h => huv (by rw [h])))

omit [Fintype V] in
/-- Packings are carried along graph embeddings. -/
lemma IsPacking.image {W : Type*} [Fintype W] [DecidableEq W] {G : SimpleGraph V}
    {H : SimpleGraph W} (f : V ↪ W) (hf : ∀ u v, G.Adj u v → H.Adj (f u) (f v))
    {P : Finset (Finset V)} (hP : IsPacking G P) :
    IsPacking H (P.image fun T => T.image f) := by
  classical
  constructor
  · intro T' hT'
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.1 hT'
    exact (hP.1 T hT).image f.injective hf
  · intro A hA B hB hne
    obtain ⟨T₁, hT₁, rfl⟩ := Finset.mem_image.1 hA
    obtain ⟨T₂, hT₂, rfl⟩ := Finset.mem_image.1 hB
    have hne' : T₁ ≠ T₂ := fun h => hne (by rw [h])
    rw [triEdges_image f.injective, triEdges_image f.injective]
    exact (Finset.disjoint_image (Sym2.map.injective f.injective)).2 (hP.2 T₁ hT₁ T₂ hT₂ hne')

/-- **Rung S1(b).**  `nu3` is monotone along embeddings of graphs. -/
theorem nu3_le_of_embedding {W : Type*} [Fintype W] [DecidableEq W] {G : SimpleGraph V}
    {H : SimpleGraph W} (f : V ↪ W) (hf : ∀ u v, G.Adj u v → H.Adj (f u) (f v)) :
    nu3 G ≤ nu3 H := by
  classical
  obtain ⟨P, hP, hcard⟩ := exists_packing_card_eq_nu3 G
  have hinj : Function.Injective (fun T : Finset V => T.image f) :=
    Finset.image_injective f.injective
  have := card_le_nu3 (hP.image f hf)
  rwa [Finset.card_image_of_injective _ hinj, hcard] at this

end BoundedCliqueGap

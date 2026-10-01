import PaperIV.FarRounding

/-!
# Transporte de empaquetamientos mixtos

Herramientas genéricas, independientes de toda construcción concreta, para mover un
`PaperIV.FarRounding.Packing` del grafo completo entre tipos de vértices:

* `mapPacking` : empuje a lo largo de una inyección `V ↪ W` (los vértices nuevos quedan
  simplemente sin cubrir);
* `comapPacking` : retracción a lo largo de una inyección `V ↪ W` cuando todas las piezas
  viven en la imagen (borrado de vértices);
* `gain_eq_two_mul_card_add_three_mul_card_four` : la ganancia de un empaquetamiento mixto es
  `2·(número de piezas) + 3·(número de piezas K₄)`.

Todo se enuncia para el grafo completo `⊤`, que es el único caso que se necesita.
-/

namespace ThreeRegime.Transport

open Finset PaperIV PaperIV.FarRounding

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

/-! ## 1. Ítems del grafo completo -/

/-- En el grafo completo la condición de clique es automática. -/
theorem isItem_top_iff {K : Finset V} :
    IsItem (⊤ : SimpleGraph V) K ↔ (K.card = 3 ∨ K.card = 4) :=
  ⟨fun h => h.2, fun h => ⟨fun _ _ _ _ hab => hab, h⟩⟩

/-! ## 2. La ganancia de un empaquetamiento mixto -/

/-- **Ganancia = `2·piezas + 3·piezas K₄`.**  Cada triángulo aporta `2` y cada `K₄` aporta `5`. -/
theorem gain_eq_two_mul_card_add_three_mul_card_four (P : Packing (⊤ : SimpleGraph V)) :
    P.gain = 2 * P.pieces.card + 3 * (P.pieces.filter (fun K => K.card = 4)).card := by
  classical
  have hsplit : P.gain = ∑ K ∈ P.pieces, (2 + 3 * (if K.card = 4 then 1 else 0)) := by
    refine Finset.sum_congr rfl fun K hK => ?_
    rcases isItem_top_iff.1 (P.isItem K hK) with h3 | h4
    · rw [gainOf_of_card_eq_three h3, if_neg (by omega)]
    · rw [gainOf_of_card_eq_four h4, if_pos h4]
  rw [hsplit, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, ← Finset.mul_sum,
    Finset.card_filter, Nat.mul_comm P.pieces.card 2]

/-! ## 3. Soporte de aristas bajo una inyección -/

/-- El soporte de aristas conmuta con el transporte por una inyección. -/
theorem pairs_map (f : V ↪ W) (K : Finset V) :
    pairs (K.map f) = (pairs K).image (Sym2.map f) := by
  classical
  ext e
  induction e using Sym2.ind with
  | _ a b =>
    constructor
    · intro he
      obtain ⟨ha, hb, hab⟩ := mk_mem_pairs.1 he
      obtain ⟨a', ha', rfl⟩ := Finset.mem_map.1 ha
      obtain ⟨b', hb', rfl⟩ := Finset.mem_map.1 hb
      refine Finset.mem_image.2 ⟨s(a', b'), mk_mem_pairs.2 ⟨ha', hb', ?_⟩, by simp⟩
      exact fun h => hab (by rw [h])
    · intro he
      obtain ⟨e', he', hmap⟩ := Finset.mem_image.1 he
      induction e' using Sym2.ind with
      | _ c d =>
        obtain ⟨hc, hd, hcd⟩ := mk_mem_pairs.1 he'
        have hmap' : s(f c, f d) = s(a, b) := by simpa using hmap
        rcases Sym2.eq_iff.1 hmap' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact mk_mem_pairs.2 ⟨Finset.mem_map_of_mem _ hc, Finset.mem_map_of_mem _ hd,
            fun h => hcd (f.injective h)⟩
        · exact mk_mem_pairs.2 ⟨Finset.mem_map_of_mem _ hd, Finset.mem_map_of_mem _ hc,
            fun h => hcd (f.injective h).symm⟩

/-! ## 4. Empuje a lo largo de una inyección -/

/-- **Empuje.**  Un empaquetamiento de `K_V` produce uno de `K_W` a lo largo de `f : V ↪ W`;
los vértices de `W` fuera de la imagen quedan sin cubrir. -/
def mapPacking (f : V ↪ W) (P : Packing (⊤ : SimpleGraph V)) :
    Packing (⊤ : SimpleGraph W) where
  pieces := P.pieces.map ⟨fun K => K.map f, fun _ _ h => Finset.map_injective f h⟩
  isItem := by
    intro K hK
    obtain ⟨K₀, hK₀, rfl⟩ := Finset.mem_map.1 hK
    refine isItem_top_iff.2 ?_
    simp only [Function.Embedding.coeFn_mk, Finset.card_map]
    exact isItem_top_iff.1 (P.isItem K₀ hK₀)
  edgeDisjoint := by
    intro K hK L hL hKL
    obtain ⟨K₀, hK₀, rfl⟩ := Finset.mem_map.1 hK
    obtain ⟨L₀, hL₀, rfl⟩ := Finset.mem_map.1 hL
    have hne : K₀ ≠ L₀ := fun h => hKL (by rw [h])
    have hdisj := P.edgeDisjoint K₀ hK₀ L₀ hL₀ hne
    simp only [Function.Embedding.coeFn_mk, pairs_map]
    rw [Finset.disjoint_left]
    intro e he he'
    obtain ⟨e₁, he₁, rfl⟩ := Finset.mem_image.1 he
    obtain ⟨e₂, he₂, hmap⟩ := Finset.mem_image.1 he'
    have hee : e₂ = e₁ := Sym2.map.injective f.injective hmap
    subst hee
    exact (Finset.disjoint_left.1 hdisj he₁) he₂

theorem mapPacking_pieces_card (f : V ↪ W) (P : Packing (⊤ : SimpleGraph V)) :
    (mapPacking f P).pieces.card = P.pieces.card := by
  simp [mapPacking]

theorem mapPacking_gain (f : V ↪ W) (P : Packing (⊤ : SimpleGraph V)) :
    (mapPacking f P).gain = P.gain := by
  classical
  show ∑ K ∈ (mapPacking f P).pieces, gainOf K = ∑ K ∈ P.pieces, gainOf K
  rw [show (mapPacking f P).pieces
      = P.pieces.map ⟨fun K => K.map f, fun _ _ h => Finset.map_injective f h⟩ from rfl,
    Finset.sum_map]
  exact Finset.sum_congr rfl fun K _ => by simp [gainOf]

theorem mapPacking_card_four (f : V ↪ W) (P : Packing (⊤ : SimpleGraph V)) :
    ((mapPacking f P).pieces.filter (fun K => K.card = 4)).card
      = (P.pieces.filter (fun K => K.card = 4)).card := by
  classical
  rw [show (mapPacking f P).pieces
      = P.pieces.map ⟨fun K => K.map f, fun _ _ h => Finset.map_injective f h⟩ from rfl,
    Finset.filter_map, Finset.card_map]
  simp [Function.comp_def]


theorem mapPacking_biUnion (f : V ↪ W) (P : Packing (⊤ : SimpleGraph V)) :
    (mapPacking f P).pieces.biUnion pairs = (P.pieces.biUnion pairs).image (Sym2.map f) := by
  classical
  ext e
  simp only [Finset.mem_biUnion, Finset.mem_image]
  constructor
  · rintro ⟨K, hK, he⟩
    obtain ⟨K₀, hK₀, rfl⟩ := Finset.mem_map.1 hK
    simp only [Function.Embedding.coeFn_mk, pairs_map] at he
    obtain ⟨e₀, he₀, rfl⟩ := Finset.mem_image.1 he
    exact ⟨e₀, ⟨K₀, hK₀, he₀⟩, rfl⟩
  · rintro ⟨e₀, ⟨K₀, hK₀, he₀⟩, rfl⟩
    refine ⟨K₀.map f, Finset.mem_map.2 ⟨K₀, hK₀, rfl⟩, ?_⟩
    simp only [pairs_map]
    exact Finset.mem_image.2 ⟨e₀, he₀, rfl⟩

theorem mapPacking_biUnion_card (f : V ↪ W) (P : Packing (⊤ : SimpleGraph V)) :
    ((mapPacking f P).pieces.biUnion pairs).card = (P.pieces.biUnion pairs).card := by
  classical
  rw [mapPacking_biUnion, Finset.card_image_of_injective _ (Sym2.map.injective f.injective)]

/-! ## 5. Retracción a lo largo de una inyección -/

section Comap

private theorem map_preimage_eq (f : V ↪ W) (P : Packing (⊤ : SimpleGraph W))
    (hsub : ∀ K ∈ P.pieces, ∀ w ∈ K, ∃ v, f v = w) {K : Finset W} (hK : K ∈ P.pieces) :
    (K.preimage f f.injective.injOn).map f = K := by
  ext w
  simp only [Finset.mem_map, Finset.mem_preimage]
  constructor
  · rintro ⟨v, hv, rfl⟩; exact hv
  · intro hw
    obtain ⟨v, rfl⟩ := hsub K hK w hw
    exact ⟨v, hw, rfl⟩

private theorem preimage_injOn (f : V ↪ W) (P : Packing (⊤ : SimpleGraph W))
    (hsub : ∀ K ∈ P.pieces, ∀ w ∈ K, ∃ v, f v = w) :
    Set.InjOn (fun K : Finset W => K.preimage f f.injective.injOn)
      (P.pieces : Set (Finset W)) := by
  intro K hK L hL hKL
  simp only at hKL
  rw [← map_preimage_eq f P hsub (Finset.mem_coe.1 hK),
    ← map_preimage_eq f P hsub (Finset.mem_coe.1 hL), hKL]

theorem card_preimage_eq (f : V ↪ W) (P : Packing (⊤ : SimpleGraph W))
    (hsub : ∀ K ∈ P.pieces, ∀ w ∈ K, ∃ v, f v = w) {K : Finset W} (hK : K ∈ P.pieces) :
    (K.preimage f f.injective.injOn).card = K.card := by
  conv_rhs => rw [← map_preimage_eq f P hsub hK]
  rw [Finset.card_map]

/-- **Retracción.**  Si todas las piezas viven en la imagen de `f : V ↪ W`, el empaquetamiento
se retrae a `K_V`.  Es el borrado de vértices. -/
noncomputable def comapPacking (f : V ↪ W) (P : Packing (⊤ : SimpleGraph W))
    (hsub : ∀ K ∈ P.pieces, ∀ w ∈ K, ∃ v, f v = w) : Packing (⊤ : SimpleGraph V) where
  pieces := P.pieces.image (fun K => K.preimage f f.injective.injOn)
  isItem := by
    intro K hK
    obtain ⟨K₀, hK₀, rfl⟩ := Finset.mem_image.1 hK
    refine isItem_top_iff.2 ?_
    rw [card_preimage_eq f P hsub hK₀]
    exact isItem_top_iff.1 (P.isItem K₀ hK₀)
  edgeDisjoint := by
    intro K hK L hL hKL
    obtain ⟨K₀, hK₀, rfl⟩ := Finset.mem_image.1 hK
    obtain ⟨L₀, hL₀, rfl⟩ := Finset.mem_image.1 hL
    have hne : K₀ ≠ L₀ := fun h => hKL (by rw [h])
    have hdisj := P.edgeDisjoint K₀ hK₀ L₀ hL₀ hne
    rw [Finset.disjoint_left]
    intro e he he'
    have hmem : ∀ M : Finset W, e ∈ pairs (M.preimage f f.injective.injOn) →
        Sym2.map f e ∈ pairs M := by
      intro M hM
      induction e using Sym2.ind with
      | _ a b =>
        obtain ⟨ha, hb, hab⟩ := mk_mem_pairs.1 hM
        rw [Finset.mem_preimage] at ha hb
        simpa using mk_mem_pairs.2 ⟨ha, hb, fun h => hab (f.injective h)⟩
    exact (Finset.disjoint_left.1 hdisj (hmem K₀ he)) (hmem L₀ he')

theorem comapPacking_pieces_card (f : V ↪ W) (P : Packing (⊤ : SimpleGraph W))
    (hsub : ∀ K ∈ P.pieces, ∀ w ∈ K, ∃ v, f v = w) :
    (comapPacking f P hsub).pieces.card = P.pieces.card :=
  Finset.card_image_of_injOn (preimage_injOn f P hsub)

theorem comapPacking_card_exists (f : V ↪ W) (P : Packing (⊤ : SimpleGraph W))
    (hsub : ∀ K ∈ P.pieces, ∀ w ∈ K, ∃ v, f v = w) {K : Finset V}
    (hK : K ∈ (comapPacking f P hsub).pieces) : ∃ K₀ ∈ P.pieces, K.card = K₀.card := by
  classical
  obtain ⟨K₀, hK₀, rfl⟩ := Finset.mem_image.1 hK
  exact ⟨K₀, hK₀, card_preimage_eq f P hsub hK₀⟩

theorem comapPacking_gain (f : V ↪ W) (P : Packing (⊤ : SimpleGraph W))
    (hsub : ∀ K ∈ P.pieces, ∀ w ∈ K, ∃ v, f v = w) :
    (comapPacking f P hsub).gain = P.gain := by
  classical
  show ∑ K ∈ (comapPacking f P hsub).pieces, gainOf K = ∑ K ∈ P.pieces, gainOf K
  rw [show (comapPacking f P hsub).pieces
      = P.pieces.image (fun K => K.preimage f f.injective.injOn) from rfl,
    Finset.sum_image (preimage_injOn f P hsub)]
  exact Finset.sum_congr rfl fun K hK => by rw [gainOf, gainOf, card_preimage_eq f P hsub hK]


theorem mem_comapPacking_biUnion (f : V ↪ W) (P : Packing (⊤ : SimpleGraph W))
    (hsub : ∀ K ∈ P.pieces, ∀ w ∈ K, ∃ v, f v = w) {e : Sym2 V}
    (he : Sym2.map f e ∈ P.pieces.biUnion pairs) :
    e ∈ (comapPacking f P hsub).pieces.biUnion pairs := by
  classical
  obtain ⟨K, hK, heK⟩ := Finset.mem_biUnion.1 he
  refine Finset.mem_biUnion.2 ⟨K.preimage f f.injective.injOn,
    Finset.mem_image.2 ⟨K, hK, rfl⟩, ?_⟩
  induction e using Sym2.ind with
  | _ a b =>
    have : s(f a, f b) ∈ pairs K := by simpa using heK
    obtain ⟨ha, hb, hab⟩ := mk_mem_pairs.1 this
    exact mk_mem_pairs.2 ⟨Finset.mem_preimage.2 ha, Finset.mem_preimage.2 hb,
      fun h => hab (by rw [h])⟩

end Comap

end ThreeRegime.Transport

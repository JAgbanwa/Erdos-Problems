import ExactReduction.ShellObstruction

/-!
# La descomposición conjunta de una estrella de bolsas: el conteo no obstruye

`ExactReduction.ShellObstruction` demuestra que una reducción por **una** bolsa hoja, que
prohíbe consumir las aristas internas del separador, es imposible cuando `|R| ≤ |S|`.  Aquí
se trata el escenario que el conteo *sí* permite: una **estrella** de bolsas colgando de un
mismo separador clique `S`, en la que las piezas pueden alojar aristas de `E(S)` (el
mecanismo `2S+1R` del completo-split) y el crédito `C(|S|,2)` se comparte globalmente entre
todas las bolsas.

* `StarCover S Bags` — familia de piezas de orden `≤ 4`, disjuntas en aristas, cada una con
  sus vértices privados dentro de **una sola** bolsa, que cubre `⋃_B (E(S,B) ∪ E(B))`.
* `starCover_card_ge` — la cota de conteo:
  `2·|S|·Σ|B| ≤ 2·#piezas + 3·C(|S|,2) + 3·Σ C(|B|,2)`.
* `star_bound_within_target` — y esa cota **nunca** supera el objetivo global: para todos
  `s, t`, `2·s·t ≤ 2·M(s+t) + 3·C(s,2)`.

Conclusión: el único obstáculo de tipo contable —el que mata la reducción por una bolsa
aislada— desaparece en la versión conjunta con crédito de separador.  Lo que queda es un
problema de diseño/asignación finito dentro de cada bolsa, no una cota asintótica.
-/

namespace ExactReduction.JointStar

open PaperIV PaperIV.FarRounding ExactReduction.ShellObstruction Finset

variable {V : Type*} [DecidableEq V]

/-- Cubrimiento conjunto de una estrella de bolsas sobre el separador `S`. -/
structure StarCover (S : Finset V) (Bags : Finset (Finset V)) where
  /-- Las piezas del cubrimiento. -/
  pieces : Finset (Finset V)
  /-- Modelo físico `c₄`: piezas de orden a lo sumo cuatro. -/
  card_le_four : ∀ K ∈ pieces, K.card ≤ 4
  /-- Los vértices privados de una pieza están todos en una misma bolsa. -/
  inOneBag : ∀ K ∈ pieces, ∃ B ∈ Bags, ∀ x ∈ K, x ∉ S → x ∈ B
  /-- Las piezas son disjuntas en aristas. -/
  edgeDisjoint : ∀ K ∈ pieces, ∀ L ∈ pieces, K ≠ L → Disjoint (pairs K) (pairs L)
  /-- Se cubren todas las aristas cruzadas y todas las internas de cada bolsa. -/
  covers : (Bags.biUnion fun B => crossPairs S B ∪ pairs B) ⊆ pieces.biUnion pairs

variable {S : Finset V} {Bags : Finset (Finset V)}

/-- Todas las aristas cruzadas de la estrella. -/
def crossAll (S : Finset V) (Bags : Finset (Finset V)) : Finset (Sym2 V) :=
  Bags.biUnion fun B => crossPairs S B

/-- Todas las aristas internas de las bolsas. -/
def innerAll (Bags : Finset (Finset V)) : Finset (Sym2 V) := Bags.biUnion pairs

theorem card_crossAll (hdS : ∀ B ∈ Bags, Disjoint S B)
    (hdB : ∀ B ∈ Bags, ∀ B' ∈ Bags, B ≠ B' → Disjoint B B') :
    (crossAll S Bags).card = ∑ B ∈ Bags, S.card * B.card := by
  rw [crossAll, Finset.card_biUnion]
  · exact Finset.sum_congr rfl fun B hB => card_crossPairs (hdS B hB)
  · intro B hB B' hB' hne
    refine Finset.disjoint_left.2 ?_
    intro e he he'
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_crossPairs.1 he
    obtain ⟨a', ha', b', hb', heq⟩ := mem_crossPairs.1 he'
    rcases Sym2.eq_iff.1 heq with ⟨-, h2⟩ | ⟨h1, -⟩
    · have hbB' : b ∈ B' := by rw [h2]; exact hb'
      exact (Finset.disjoint_left.1 (hdB B hB B' hB' hne) hb) hbB'
    · have haB' : a ∈ B' := by rw [h1]; exact hb'
      exact (Finset.disjoint_left.1 (hdS B' hB') ha) haB'

theorem card_innerAll_le : (innerAll Bags).card ≤ ∑ B ∈ Bags, B.card.choose 2 := by
  refine le_trans Finset.card_biUnion_le ?_
  exact le_of_eq (Finset.sum_congr rfl fun B _ => card_pairs B)

private theorem card_eq_sum (C : StarCover S Bags) {T : Finset (Sym2 V)}
    (hT : T ⊆ C.pieces.biUnion pairs) :
    T.card = ∑ K ∈ C.pieces, (T ∩ pairs K).card := by
  have hb : T = C.pieces.biUnion fun K => T ∩ pairs K := by
    ext e
    simp only [Finset.mem_biUnion, Finset.mem_inter]
    constructor
    · intro he
      obtain ⟨K, hK, heK⟩ := Finset.mem_biUnion.1 (hT he)
      exact ⟨K, hK, he, heK⟩
    · rintro ⟨K, -, he, -⟩
      exact he
  conv_lhs => rw [hb]
  refine Finset.card_biUnion ?_
  intro K hK L hL hKL
  exact Finset.disjoint_of_subset_left Finset.inter_subset_right
    (Finset.disjoint_of_subset_right Finset.inter_subset_right (C.edgeDisjoint K hK L hL hKL))

private theorem sum_inter_le (C : StarCover S Bags) (T : Finset (Sym2 V)) :
    ∑ K ∈ C.pieces, (T ∩ pairs K).card ≤ T.card := by
  have hdisj : ∀ K ∈ C.pieces, ∀ L ∈ C.pieces, K ≠ L →
      Disjoint (T ∩ pairs K) (T ∩ pairs L) := fun K hK L hL hKL =>
    Finset.disjoint_of_subset_left Finset.inter_subset_right
      (Finset.disjoint_of_subset_right Finset.inter_subset_right (C.edgeDisjoint K hK L hL hKL))
  rw [← Finset.card_biUnion hdisj]
  refine Finset.card_le_card ?_
  intro e he
  obtain ⟨K, -, heK⟩ := Finset.mem_biUnion.1 he
  exact (Finset.mem_inter.1 heK).1

/-- Cota por pieza en la estrella: cada pieza cubre a lo sumo `1 + (3/2)` veces lo que
consume de crédito de separador y de aristas internas de su bolsa. -/
theorem piece_bound_star (hdS : ∀ B ∈ Bags, Disjoint S B) (C : StarCover S Bags)
    {K : Finset V} (hK : K ∈ C.pieces) :
    2 * (crossAll S Bags ∩ pairs K).card
      ≤ 2 + 3 * (pairs S ∩ pairs K).card + 3 * (innerAll Bags ∩ pairs K).card := by
  obtain ⟨B, hB, hKB⟩ := C.inOneBag K hK
  have hd : Disjoint S B := hdS B hB
  -- todas las aristas cruzadas dentro de `K` van a la bolsa `B`
  have hsub : crossAll S Bags ∩ pairs K ⊆ crossPairs (K ∩ S) (K ∩ B) := by
    intro e he
    obtain ⟨hcross, hpairs⟩ := Finset.mem_inter.1 he
    obtain ⟨B', hB', hmem⟩ := Finset.mem_biUnion.1 hcross
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_crossPairs.1 hmem
    obtain ⟨haK, hbK, -⟩ := mk_mem_pairs.1 hpairs
    have hbS : b ∉ S := fun h => (Finset.disjoint_left.1 (hdS B' hB') h) hb
    exact mem_crossPairs.2
      ⟨a, Finset.mem_inter.2 ⟨haK, ha⟩, b, Finset.mem_inter.2 ⟨hbK, hKB b hbK hbS⟩, rfl⟩
  have h1 : (crossAll S Bags ∩ pairs K).card ≤ (K ∩ S).card * (K ∩ B).card :=
    le_trans (Finset.card_le_card hsub) (card_crossPairs_le _ _)
  have hdKK : Disjoint (K ∩ S) (K ∩ B) :=
    Finset.disjoint_of_subset_left Finset.inter_subset_right
      (Finset.disjoint_of_subset_right Finset.inter_subset_right hd)
  have hsum : (K ∩ S).card + (K ∩ B).card ≤ 4 := by
    rw [← Finset.card_union_of_disjoint hdKK]
    refine le_trans (Finset.card_le_card ?_) (C.card_le_four K hK)
    intro x hx
    rcases Finset.mem_union.1 hx with hx | hx <;> exact (Finset.mem_inter.1 hx).1
  have hS : (pairs S ∩ pairs K).card = (K ∩ S).card.choose 2 := by
    rw [pairs_inter, card_pairs, Finset.inter_comm]
  have hBin : (K ∩ B).card.choose 2 ≤ (innerAll Bags ∩ pairs K).card := by
    have hsub' : pairs B ∩ pairs K ⊆ innerAll Bags ∩ pairs K := by
      intro e he
      obtain ⟨heB, heK⟩ := Finset.mem_inter.1 he
      exact Finset.mem_inter.2 ⟨Finset.mem_biUnion.2 ⟨B, hB, heB⟩, heK⟩
    have : (pairs B ∩ pairs K).card = (K ∩ B).card.choose 2 := by
      rw [pairs_inter, card_pairs, Finset.inter_comm]
    rw [← this]
    exact Finset.card_le_card hsub'
  have hkey := two_mul_le_credit hsum
  omega

/-- **Cota de conteo para la descomposición conjunta de una estrella de bolsas.** -/
theorem starCover_card_ge (hdS : ∀ B ∈ Bags, Disjoint S B)
    (hdB : ∀ B ∈ Bags, ∀ B' ∈ Bags, B ≠ B' → Disjoint B B') (C : StarCover S Bags) :
    2 * (∑ B ∈ Bags, S.card * B.card)
      ≤ 2 * C.pieces.card + 3 * S.card.choose 2 + 3 * ∑ B ∈ Bags, B.card.choose 2 := by
  have hcross : crossAll S Bags ⊆ C.pieces.biUnion pairs := by
    intro e he
    obtain ⟨B, hB, hmem⟩ := Finset.mem_biUnion.1 he
    exact C.covers (Finset.mem_biUnion.2 ⟨B, hB, Finset.mem_union_left _ hmem⟩)
  have hsum : (crossAll S Bags).card
      = ∑ K ∈ C.pieces, (crossAll S Bags ∩ pairs K).card := card_eq_sum C hcross
  have hstep : ∑ K ∈ C.pieces, 2 * (crossAll S Bags ∩ pairs K).card
      ≤ ∑ K ∈ C.pieces, (2 + 3 * (pairs S ∩ pairs K).card
          + 3 * (innerAll Bags ∩ pairs K).card) :=
    Finset.sum_le_sum fun K hK => piece_bound_star hdS C hK
  have hl : ∑ K ∈ C.pieces, 2 * (crossAll S Bags ∩ pairs K).card
      = 2 * ∑ K ∈ C.pieces, (crossAll S Bags ∩ pairs K).card := by rw [Finset.mul_sum]
  have hr : ∑ K ∈ C.pieces, (2 + 3 * (pairs S ∩ pairs K).card
        + 3 * (innerAll Bags ∩ pairs K).card)
      = 2 * C.pieces.card + 3 * (∑ K ∈ C.pieces, (pairs S ∩ pairs K).card)
        + 3 * (∑ K ∈ C.pieces, (innerAll Bags ∩ pairs K).card) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul,
      ← Finset.mul_sum, ← Finset.mul_sum, Nat.mul_comm C.pieces.card 2]
  have hSsum : ∑ K ∈ C.pieces, (pairs S ∩ pairs K).card ≤ S.card.choose 2 := by
    have := sum_inter_le C (pairs S); rwa [card_pairs] at this
  have hIsum : ∑ K ∈ C.pieces, (innerAll Bags ∩ pairs K).card
      ≤ ∑ B ∈ Bags, B.card.choose 2 :=
    le_trans (sum_inter_le C (innerAll Bags)) card_innerAll_le
  rw [card_crossAll hdS hdB] at hsum
  omega

/-! ## La noción no es vacía -/

private theorem not_isDiag_of_mem_star (hdS : ∀ B ∈ Bags, Disjoint S B) {e : Sym2 V}
    (he : e ∈ Bags.biUnion fun B => crossPairs S B ∪ pairs B) : ¬ e.IsDiag := by
  obtain ⟨B, hB, hmem⟩ := Finset.mem_biUnion.1 he
  exact ShellObstruction.not_isDiag_of_mem_shell (hdS B hB) hmem

/-- El cubrimiento trivial por `K₂`: una pieza por cada arista de la estrella.  Prueba que
`StarCover` no es una noción vacía. -/
def trivialStarCover (hdS : ∀ B ∈ Bags, Disjoint S B) : StarCover S Bags where
  pieces := (Bags.biUnion fun B => crossPairs S B ∪ pairs B).image Sym2.toFinset
  card_le_four := by
    intro K hK
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hK
    rw [Sym2.card_toFinset_of_not_isDiag e (not_isDiag_of_mem_star hdS he)]
    norm_num
  inOneBag := by
    intro K hK
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hK
    obtain ⟨B, hB, hmem⟩ := Finset.mem_biUnion.1 he
    refine ⟨B, hB, ?_⟩
    rcases Finset.mem_union.1 hmem with hc | hi
    · obtain ⟨a, ha, b, hb, rfl⟩ := mem_crossPairs.1 hc
      intro x hx hxS
      have : x = a ∨ x = b := by simpa using hx
      rcases this with rfl | rfl
      · exact absurd ha hxS
      · exact hb
    · intro x hx _
      exact (mem_pairs.1 hi).1 x (by simpa using hx)
  edgeDisjoint := by
    intro K hK L hL hKL
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hK
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hL
    rw [pairs_toFinset (not_isDiag_of_mem_star hdS he),
      pairs_toFinset (not_isDiag_of_mem_star hdS hf)]
    simp only [Finset.disjoint_singleton]
    exact fun h => hKL (by rw [h])
  covers := by
    intro e he
    refine Finset.mem_biUnion.2 ⟨e.toFinset, Finset.mem_image_of_mem _ he, ?_⟩
    rw [pairs_toFinset (not_isDiag_of_mem_star hdS he)]
    exact Finset.mem_singleton_self e

/-- **El conteo de la estrella nunca supera el objetivo global.**  Para todos `s, t`,
`2·s·t ≤ 2·M(s+t) + 3·C(s,2)`; con `s = |S|` y `t = Σ|B|` esto dice que la cota inferior
de `starCover_card_ge` cabe siempre en `M(n)`, incluso ignorando el término
`3·Σ C(|B|,2)`. -/
theorem star_bound_within_target (s t : ℕ) :
    2 * (s * t) ≤ 2 * PaperIV.targetSize (s + t) + 3 * s.choose 2 := by
  have h1 : (s + t) * (s + t + 1) ≤ 6 * PaperIV.targetSize (s + t) + 2 :=
    ExactReduction.le_six_mul_targetSize_add_two _
  rcases Nat.lt_or_ge s 2 with hs | hs
  · interval_cases s
    · simp
    · -- `s = 1`: hace falta `t ≤ M(t+1)`, cierto para todo `t`
      simp only [Nat.one_mul, Nat.choose, Nat.mul_zero, Nat.add_zero] at *
      rcases Nat.lt_or_ge t 3 with ht | ht
      · interval_cases t <;> norm_num [PaperIV.targetSize]
      · nlinarith [h1, ht]
  · obtain ⟨s', rfl⟩ : ∃ s', s = s' + 2 := ⟨s - 2, by omega⟩
    have h3' : 2 * (s' + 2).choose 2 = (s' + 2) * (s' + 1) := by
      have h := ExactReduction.two_mul_choose_two (s' + 2)
      simpa using h
    zify at h1 h3' ⊢
    nlinarith [h1, h3', sq_nonneg ((2 : ℤ) * (t : ℤ) - 4 * (s' : ℤ) - 7),
      Int.natCast_nonneg t, Int.natCast_nonneg s']

end ExactReduction.JointStar

import MixedRounding.Defs

/-!
# El levantamiento físico (CMR, gate G3)

La mitad de G3 que hace **consumible** su salida: que ninguna hiperarista invente cliques, y
que un matching del hipergrafo de soportes sea literalmente un empaquetamiento de `G`.

## El punto

El productor de patrones construye un hipergrafo cuyos **vértices son las aristas de `G`** y
cuyas hiperaristas son los soportes `pairs K` de items reales.  La propiedad crítica del plan
—*«no inventamos cliques: cada hiperarista seleccionable levanta a un `K₃` o `K₄` real»*— es
aquí un teorema y no una convención:

* `cliqueOf_pairs` — de `pairs K` se recupera `K`; el soporte determina la clique;
* `pairs_injOn_items` — luego `pairs` es **inyectiva** sobre items;
* `packing_of_matching` — un matching del hipergrafo de soportes **es** un `Packing G`, con la
  ganancia que le corresponde.

Eso es lo que G4 necesita para ensamblar, y es lo que separa este enfoque de un conteo
abstracto de patrones.

## La unión mixta sale gratis

`packing_of_matching` se enuncia sobre **todos** los soportes a la vez, no por brazo.  Así la
unión de un matching de `K₃` y uno de `K₄` —que es lo que produce el nibble en sus dos
uniformidades `3` y `6`— es un caso particular, no un teorema aparte: `mixed_union` sale de
partir una suma.  La hipótesis que hace falta es la que ya sabíamos: que los dos matchings sean
disjuntos **entre brazos**, no sólo dentro de cada uno.

## Uniformidades

`supportsOfCard G k` es `(k choose 2)`-uniforme.  Para `k = 3` da `3`, para `k = 4` da **`6`**.
Es la corrección de nomenclatura ya registrada en `NearPerfect`.

## Procedencia

`filter_isDiag_sym2` y `card_pairs` se portan de `PaperIV.FarRounding` (líneas 64 y 82), y
`cliqueOf_pairs` de `PaperIV.NibblePort`, sin cambios matemáticos.  Se reproducen aquí en vez de
importarse para que la biblioteca siga siendo neutral; `PaperIV.MixedRoundingAdapter` certifica
que las dos copias coinciden.
-/

namespace MixedRounding

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ## 1. El soporte determina la clique -/

lemma filter_isDiag_sym2 (K : Finset V) :
    K.sym2.filter (fun e => e.IsDiag) = K.image Sym2.diag := by
  ext e
  induction e using Sym2.ind with
  | _ a b =>
    rw [Finset.mem_filter, Finset.mk_mem_sym2_iff, Sym2.isDiag_iff_proj_eq, Finset.mem_image]
    constructor
    · rintro ⟨⟨ha, _⟩, hab⟩
      refine ⟨a, ha, ?_⟩
      show s(a, a) = s(a, b)
      rw [Sym2.eq_iff]
      exact Or.inl ⟨rfl, hab⟩
    · rintro ⟨x, hx, hxe⟩
      have hxe' : s(x, x) = s(a, b) := hxe
      rw [Sym2.eq_iff] at hxe'
      rcases hxe' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨⟨hx, hx⟩, rfl⟩

/-- El soporte de un `k`-conjunto tiene exactamente `C(k,2)` aristas. -/
lemma card_pairs (K : Finset V) : (pairs K).card = K.card.choose 2 := by
  have hsplit := Finset.card_filter_add_card_filter_not (s := K.sym2) (fun e => e.IsDiag)
  rw [filter_isDiag_sym2, Finset.card_image_of_injective _ Sym2.diag_injective,
    Finset.card_sym2] at hsplit
  have hchoose : (K.card + 1).choose 2 = K.card + K.card.choose 2 := by
    rw [Nat.choose_succ_succ K.card 1, Nat.choose_one_right]
  rw [hchoose] at hsplit
  exact Nat.add_left_cancel hsplit

/-- Los vértices que toca un conjunto de aristas. -/
def cliqueOf (S : Finset (Sym2 V)) : Finset V := S.biUnion Sym2.toFinset

/-- **El soporte determina la clique.**  De `pairs K` se recupera `K`, en cuanto `K` tiene al
menos dos vértices.  Es la forma precisa de «no inventamos cliques». -/
theorem cliqueOf_pairs {K : Finset V} (h : 2 ≤ K.card) : cliqueOf (pairs K) = K := by
  classical
  ext v
  simp only [cliqueOf, Finset.mem_biUnion]
  constructor
  · rintro ⟨e, he, hve⟩
    induction e using Sym2.ind with
    | _ a b =>
      rw [mk_mem_pairs] at he
      rw [Sym2.mem_toFinset, Sym2.mem_iff] at hve
      rcases hve with rfl | rfl
      · exact he.1
      · exact he.2.1
  · intro hv
    have hne : (K.erase v).Nonempty := by
      rw [← Finset.card_pos, Finset.card_erase_of_mem hv]; omega
    obtain ⟨u, hu⟩ := hne
    obtain ⟨huv, huK⟩ := Finset.mem_erase.1 hu
    refine ⟨s(v, u), ?_, ?_⟩
    · rw [mk_mem_pairs]; exact ⟨hv, huK, fun hc => huv hc.symm⟩
    · rw [Sym2.mem_toFinset, Sym2.mem_iff]; exact Or.inl rfl

/-- Todo item tiene al menos dos vértices. -/
lemma two_le_card_of_isItem {K : Finset V} (h : IsItem G K) : 2 ≤ K.card := by
  rcases h.2 with h3 | h4 <;> omega

/-- **`pairs` es inyectiva sobre items.** -/
theorem pairs_injOn_items {K L : Finset V} (hK : IsItem G K) (hL : IsItem G L)
    (h : pairs K = pairs L) : K = L := by
  have := cliqueOf_pairs (two_le_card_of_isItem hK)
  rw [h, cliqueOf_pairs (two_le_card_of_isItem hL)] at this
  exact this.symm

/-! ## 2. El hipergrafo de soportes -/

/-- El hipergrafo cuyos vértices son las aristas de `G` y cuyas hiperaristas son los soportes
de los items. -/
def supports (G : SimpleGraph V) [DecidableRel G.Adj] : Finset (Finset (Sym2 V)) :=
  (items G).image pairs

/-- Los soportes de los items de un tamaño fijo. -/
def supportsOfCard (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) :
    Finset (Finset (Sym2 V)) :=
  ((items G).filter (fun K => K.card = k)).image pairs

theorem mem_supports {S : Finset (Sym2 V)} :
    S ∈ supports G ↔ ∃ K, IsItem G K ∧ pairs K = S := by
  simp only [supports, Finset.mem_image, mem_items]

/-- **Uniformidad.**  Los soportes de los `k`-items tienen `C(k,2)` aristas: `3` para `K₃` y
**`6`** para `K₄`. -/
theorem supportsOfCard_uniform (k : ℕ) :
    IsUniformHypergraph (supportsOfCard G k) (k.choose 2) := by
  intro S hS
  simp only [supportsOfCard, Finset.mem_image, Finset.mem_filter] at hS
  obtain ⟨K, ⟨-, hk⟩, rfl⟩ := hS
  rw [card_pairs, hk]

theorem supportsOfCard_subset : supportsOfCard G k ⊆ supports G := by
  intro S hS
  simp only [supportsOfCard, Finset.mem_image, Finset.mem_filter] at hS
  obtain ⟨K, ⟨hK, -⟩, rfl⟩ := hS
  exact Finset.mem_image.2 ⟨K, hK, rfl⟩

/-- Sobre los soportes, `cliqueOf` invierte a `pairs`. -/
theorem pairs_cliqueOf {S : Finset (Sym2 V)} (hS : S ∈ supports G) : pairs (cliqueOf S) = S := by
  obtain ⟨K, hK, rfl⟩ := mem_supports.1 hS
  rw [cliqueOf_pairs (two_le_card_of_isItem hK)]

theorem isItem_cliqueOf {S : Finset (Sym2 V)} (hS : S ∈ supports G) :
    IsItem G (cliqueOf S) := by
  obtain ⟨K, hK, rfl⟩ := mem_supports.1 hS
  rwa [cliqueOf_pairs (two_le_card_of_isItem hK)]

/-! ## 3. Un matching **es** un empaquetamiento -/

/-- **G3 → G4.**  Un matching del hipergrafo de soportes es literalmente un `Packing G`, y su
ganancia es la suma de las ganancias de las cliques levantadas.

Éste es el puente que impide que el productor entregue conteos abstractos: cada hiperarista
seleccionada **es** el soporte de una copia real, y la disyunción de hiperaristas **es** la
disyunción por aristas que pide `Packing`. -/
theorem packing_of_matching (M : Finset (Finset (Sym2 V))) (hsub : M ⊆ supports G)
    (hdisj : ∀ S ∈ M, ∀ T ∈ M, S ≠ T → Disjoint S T) :
    ∃ P : Packing G, P.gain = ∑ S ∈ M, gainOf (cliqueOf S) := by
  classical
  have hinj : ∀ S ∈ M, ∀ T ∈ M, cliqueOf S = cliqueOf T → S = T := by
    intro S hS T hT h
    have := pairs_cliqueOf (hsub hS)
    rw [h, pairs_cliqueOf (hsub hT)] at this
    exact this.symm
  refine ⟨{ pieces := M.image cliqueOf
            isItem := ?_
            edgeDisjoint := ?_ }, ?_⟩
  · intro K hK
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.1 hK
    exact isItem_cliqueOf (hsub hS)
  · intro K hK L hL hne
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.1 hK
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.1 hL
    rw [pairs_cliqueOf (hsub hS), pairs_cliqueOf (hsub hT)]
    exact hdisj S hS T hT (fun hc => hne (by rw [hc]))
  · rw [Packing.gain, Finset.sum_image hinj]

/-! ## 4. La unión mixta -/

/-- **La unión de los dos brazos.**  Si el matching de `K₃` y el de `K₄` son disjuntos
**entre sí** —no sólo cada uno por dentro— su unión es un empaquetamiento de ganancia
`2|M₃| + 5|M₄|`.

No es un teorema aparte: es `packing_of_matching` sobre la unión, más partir la suma. -/
theorem mixed_union (M₃ M₄ : Finset (Finset (Sym2 V)))
    (h3 : M₃ ⊆ supportsOfCard G 3) (h4 : M₄ ⊆ supportsOfCard G 4)
    (hdisj : ∀ S ∈ M₃ ∪ M₄, ∀ T ∈ M₃ ∪ M₄, S ≠ T → Disjoint S T)
    (hcross : Disjoint M₃ M₄) :
    ∃ P : Packing G, P.gain = 2 * M₃.card + 5 * M₄.card := by
  classical
  have hsub : M₃ ∪ M₄ ⊆ supports G := by
    intro S hS
    rcases Finset.mem_union.1 hS with h | h
    · exact supportsOfCard_subset (h3 h)
    · exact supportsOfCard_subset (h4 h)
  obtain ⟨P, hP⟩ := packing_of_matching (M₃ ∪ M₄) hsub hdisj
  refine ⟨P, ?_⟩
  have hgain3 : ∀ S ∈ M₃, gainOf (cliqueOf S) = 2 := by
    intro S hS
    have := h3 hS
    simp only [supportsOfCard, Finset.mem_image, Finset.mem_filter] at this
    obtain ⟨K, ⟨hK, hk⟩, rfl⟩ := this
    rw [cliqueOf_pairs (two_le_card_of_isItem (mem_items.1 hK)), gainOf, hk]
    decide
  have hgain4 : ∀ S ∈ M₄, gainOf (cliqueOf S) = 5 := by
    intro S hS
    have := h4 hS
    simp only [supportsOfCard, Finset.mem_image, Finset.mem_filter] at this
    obtain ⟨K, ⟨hK, hk⟩, rfl⟩ := this
    have e42 : Nat.choose 4 2 = 6 := by decide
    rw [cliqueOf_pairs (two_le_card_of_isItem (mem_items.1 hK)), gainOf, hk, e42]
  have e3 : ∑ S ∈ M₃, gainOf (cliqueOf S) = 2 * M₃.card := by
    rw [Finset.sum_congr rfl hgain3, Finset.sum_const, smul_eq_mul]; ring
  have e4 : ∑ S ∈ M₄, gainOf (cliqueOf S) = 5 * M₄.card := by
    rw [Finset.sum_congr rfl hgain4, Finset.sum_const, smul_eq_mul]; ring
  rw [hP, Finset.sum_union hcross, e3, e4]

end MixedRounding

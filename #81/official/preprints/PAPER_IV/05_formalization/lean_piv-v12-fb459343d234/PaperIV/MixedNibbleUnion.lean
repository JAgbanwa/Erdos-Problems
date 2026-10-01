import PaperIV.TriangleNibblePort

/-!
# Ensamblaje de los brazos triangular y cuadrangular

Una selección conjunta sólo tiene que certificar disjunción transversal de
recursos. Este módulo convierte esa certificación en un único packing mixto y
una identidad exacta de ganancia.

`exists_mixed_packing_of_matchings` se construye **directamente** desde los dos
matchings: `packing_of_k3_matching` y `packing_of_matching` sólo devuelven la
existencia de un packing con la ganancia correcta, y no exponen sus piezas, de
modo que la disyunción cruzada hay que leerla en los soportes originales.
-/

namespace PaperIV.MixedNibbleUnion

open Finset
open PaperIV.FarRounding
open PaperIV.NibblePort

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Un item tiene al menos una arista en su soporte. -/
theorem pairs_ne_empty_of_isItem {K : Finset V} (h : IsItem G K) : pairs K ≠ ∅ := by
  intro hK
  have hcard := card_pairs_of_isItem h
  rw [hK, Finset.card_empty] at hcard
  omega

theorem packing_union_of_cross_disjoint (P₃ P₄ : Packing G)
    (hcross : ∀ K ∈ P₃.pieces, ∀ L ∈ P₄.pieces, Disjoint (pairs K) (pairs L)) :
    ∃ P : Packing G, P.gain = P₃.gain + P₄.gain := by
  have hpieces : Disjoint P₃.pieces P₄.pieces := by
    rw [Finset.disjoint_left]
    intro K hK₃ hK₄
    have hd := hcross K hK₃ K hK₄
    obtain ⟨e, he⟩ :=
      Finset.nonempty_iff_ne_empty.2 (pairs_ne_empty_of_isItem (P₃.isItem K hK₃))
    exact (Finset.disjoint_left.1 hd) he he
  refine ⟨{ pieces := P₃.pieces ∪ P₄.pieces
            isItem := by
              intro K hK
              rcases Finset.mem_union.1 hK with hK | hK
              · exact P₃.isItem K hK
              · exact P₄.isItem K hK
            edgeDisjoint := by
              intro K hK L hL hKL
              rcases Finset.mem_union.1 hK with hK | hK <;>
                rcases Finset.mem_union.1 hL with hL | hL
              · exact P₃.edgeDisjoint K hK L hL hKL
              · exact hcross K hK L hL
              · exact (hcross L hL K hK).symm
              · exact P₄.edgeDisjoint K hK L hL hKL }, ?_⟩
  simp only [Packing.gain]
  exact Finset.sum_union hpieces

theorem exists_mixed_packing_of_matchings
    (M₃ M₄ : Finset (Finset (Sym2 V)))
    (h₃ : NibblePort.Hypergraph.IsMatching (NibblePort.k3Supports G) M₃)
    (h₄ : NibblePort.Hypergraph.IsMatching (NibblePort.k4Supports G) M₄)
    (hcross : ∀ S ∈ M₃, ∀ T ∈ M₄, Disjoint S T) :
    ∃ P : Packing G, P.gain = 2 * M₃.card + 5 * M₄.card := by
  classical
  -- las piezas de cada brazo, con su tamaño
  have hitem₃ : ∀ S ∈ M₃, IsItem G (cliqueOf S) ∧ (cliqueOf S).card = 3 := by
    intro S hS
    obtain ⟨K, hK, h3, rfl⟩ := mem_k3Supports.1 (h₃.subset hS)
    rw [cliqueOf_pairs (by omega : 2 ≤ K.card)]
    exact ⟨hK, h3⟩
  have hitem₄ : ∀ T ∈ M₄, IsItem G (cliqueOf T) ∧ (cliqueOf T).card = 4 := by
    intro T hT
    obtain ⟨K, hK, h4, rfl⟩ := mem_k4Supports.1 (h₄.subset hT)
    rw [cliqueOf_pairs (by omega : 2 ≤ K.card)]
    exact ⟨hK, h4⟩
  have hinj₃ : ∀ S ∈ M₃, ∀ S' ∈ M₃, cliqueOf S = cliqueOf S' → S = S' := by
    intro S hS S' hS' heq
    rw [← pairs_cliqueOf_k3 (h₃.subset hS), ← pairs_cliqueOf_k3 (h₃.subset hS'), heq]
  have hinj₄ : ∀ T ∈ M₄, ∀ T' ∈ M₄, cliqueOf T = cliqueOf T' → T = T' := by
    intro T hT T' hT' heq
    rw [← pairs_cliqueOf (h₄.subset hT), ← pairs_cliqueOf (h₄.subset hT'), heq]
  -- los soportes de un brazo no son vacíos
  have hne₃ : ∀ S ∈ M₃, S.Nonempty := by
    intro S hS
    rw [← Finset.card_pos, NibblePort.k3Supports_uniform S (h₃.subset hS)]
    omega
  -- las dos imágenes son disjuntas: un soporte común sería disjunto de sí mismo
  have himg : Disjoint (M₃.image cliqueOf) (M₄.image cliqueOf) := by
    rw [Finset.disjoint_left]
    intro K hK hK'
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.1 hK
    obtain ⟨T, hT, hTS⟩ := Finset.mem_image.1 hK'
    have hST : S = T := by
      rw [← pairs_cliqueOf_k3 (h₃.subset hS), ← pairs_cliqueOf (h₄.subset hT), hTS]
    subst hST
    obtain ⟨e, he⟩ := hne₃ S hS
    exact (Finset.disjoint_left.1 (hcross S hS S hT)) he he
  refine ⟨{ pieces := M₃.image cliqueOf ∪ M₄.image cliqueOf
            isItem := by
              intro K hK
              rcases Finset.mem_union.1 hK with hK | hK
              · obtain ⟨S, hS, rfl⟩ := Finset.mem_image.1 hK
                exact (hitem₃ S hS).1
              · obtain ⟨T, hT, rfl⟩ := Finset.mem_image.1 hK
                exact (hitem₄ T hT).1
            edgeDisjoint := by
              intro K hK L hL hKL
              rcases Finset.mem_union.1 hK with hK | hK <;>
                rcases Finset.mem_union.1 hL with hL | hL
              · obtain ⟨S, hS, rfl⟩ := Finset.mem_image.1 hK
                obtain ⟨S', hS', rfl⟩ := Finset.mem_image.1 hL
                rw [pairs_cliqueOf_k3 (h₃.subset hS), pairs_cliqueOf_k3 (h₃.subset hS')]
                exact h₃.disjoint S hS S' hS' (fun hc => hKL (by rw [hc]))
              · obtain ⟨S, hS, rfl⟩ := Finset.mem_image.1 hK
                obtain ⟨T, hT, rfl⟩ := Finset.mem_image.1 hL
                rw [pairs_cliqueOf_k3 (h₃.subset hS), pairs_cliqueOf (h₄.subset hT)]
                exact hcross S hS T hT
              · obtain ⟨T, hT, rfl⟩ := Finset.mem_image.1 hK
                obtain ⟨S, hS, rfl⟩ := Finset.mem_image.1 hL
                rw [pairs_cliqueOf (h₄.subset hT), pairs_cliqueOf_k3 (h₃.subset hS)]
                exact (hcross S hS T hT).symm
              · obtain ⟨T, hT, rfl⟩ := Finset.mem_image.1 hK
                obtain ⟨T', hT', rfl⟩ := Finset.mem_image.1 hL
                rw [pairs_cliqueOf (h₄.subset hT), pairs_cliqueOf (h₄.subset hT')]
                exact h₄.disjoint T hT T' hT' (fun hc => hKL (by rw [hc])) }, ?_⟩
  show ∑ K ∈ M₃.image cliqueOf ∪ M₄.image cliqueOf, gainOf K = 2 * M₃.card + 5 * M₄.card
  rw [Finset.sum_union himg, Finset.sum_image hinj₃, Finset.sum_image hinj₄,
    Finset.sum_congr rfl (fun S hS => gainOf_of_card_eq_three (hitem₃ S hS).2),
    Finset.sum_congr rfl (fun T hT => gainOf_of_card_eq_four (hitem₄ T hT).2),
    Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul, mul_comm (M₃.card) 2,
    mul_comm (M₄.card) 5]

end PaperIV.MixedNibbleUnion

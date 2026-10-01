import PaperIV.NibblePort

/-!
# Porte triangular del nibble

La ruta RC01 no puede limitarse a `K₄`: un packing fraccional mixto puede tener
valor macroscópico únicamente en triángulos.  Este módulo da el adaptador
literal paralelo al ya existente para `K₄`: el hipergrafo de soportes de `K₃`
es `3`-uniforme y cada matching se convierte en un packing físico de ganancia
exacta `2` por pieza.
-/

namespace PaperIV.NibblePort

open Finset
open PaperIV.FarRounding

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Hiperaristas: los tres lados de cada `K₃` literal de `G`. -/
def k3Supports (G : SimpleGraph V) [DecidableRel G.Adj] : Finset (Finset (Sym2 V)) :=
  ((items G).filter (fun K => K.card = 3)).image pairs

theorem mem_k3Supports {S : Finset (Sym2 V)} :
    S ∈ k3Supports G ↔ ∃ K : Finset V, IsItem G K ∧ K.card = 3 ∧ pairs K = S := by
  classical
  simp only [k3Supports, Finset.mem_image, Finset.mem_filter, mem_items]
  constructor
  · rintro ⟨K, ⟨hK, h3⟩, rfl⟩
    exact ⟨K, hK, h3, rfl⟩
  · rintro ⟨K, hK, h3, rfl⟩
    exact ⟨K, ⟨hK, h3⟩, rfl⟩

theorem k3Supports_uniform : Hypergraph.IsUniform (k3Supports G) 3 := by
  intro S hS
  obtain ⟨K, _, h3, rfl⟩ := mem_k3Supports.1 hS
  rw [card_pairs, h3]
  decide

theorem pairs_cliqueOf_k3 {S : Finset (Sym2 V)} (hS : S ∈ k3Supports G) :
    pairs (cliqueOf S) = S := by
  obtain ⟨K, _, h3, rfl⟩ := mem_k3Supports.1 hS
  rw [cliqueOf_pairs (by omega : 2 ≤ K.card)]

/-- Un matching de soportes triangulares es un packing físico de ganancia `2` por pieza. -/
theorem packing_of_k3_matching (M : Finset (Finset (Sym2 V)))
    (hM : Hypergraph.IsMatching (k3Supports G) M) :
    ∃ P : Packing G, P.gain = 2 * M.card := by
  classical
  have hitem : ∀ S ∈ M, IsItem G (cliqueOf S) ∧ (cliqueOf S).card = 3 := by
    intro S hS
    obtain ⟨K, hK, h3, rfl⟩ := mem_k3Supports.1 (hM.subset hS)
    rw [cliqueOf_pairs (by omega : 2 ≤ K.card)]
    exact ⟨hK, h3⟩
  have hinj : ∀ S ∈ M, ∀ S' ∈ M, cliqueOf S = cliqueOf S' → S = S' := by
    intro S hS S' hS' heq
    rw [← pairs_cliqueOf_k3 (hM.subset hS), ← pairs_cliqueOf_k3 (hM.subset hS'), heq]
  refine ⟨{ pieces := M.image cliqueOf
            isItem := by
              intro K hK
              obtain ⟨S, hS, rfl⟩ := Finset.mem_image.1 hK
              exact (hitem S hS).1
            edgeDisjoint := by
              intro K hK L hL hKL
              obtain ⟨S, hS, rfl⟩ := Finset.mem_image.1 hK
              obtain ⟨S', hS', rfl⟩ := Finset.mem_image.1 hL
              rw [pairs_cliqueOf_k3 (hM.subset hS), pairs_cliqueOf_k3 (hM.subset hS')]
              exact hM.disjoint S hS S' hS' (fun hc => hKL (by rw [hc])) }, ?_⟩
  show ∑ K ∈ M.image cliqueOf, gainOf K = 2 * M.card
  rw [Finset.sum_image hinj]
  rw [Finset.sum_congr rfl (fun S hS => gainOf_of_card_eq_three (hitem S hS).2),
    Finset.sum_const, smul_eq_mul, mul_comm]

end PaperIV.NibblePort

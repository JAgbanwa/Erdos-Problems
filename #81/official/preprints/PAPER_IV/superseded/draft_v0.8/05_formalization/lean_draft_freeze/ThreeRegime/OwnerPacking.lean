import ThreeRegime.PackingTransport
import ThreeRegime.CompleteStateCentre
import ThreeRegime.TrianglePackingParity

/-!
# Empaquetamientos definidos por una función «dueño»

Para construir un empaquetamiento explícito de `K_V` basta:

* una familia `blocks` de cliques de orden `3` o `4`;
* una función `own : V → V → Finset V` que a cada arista le asigna *un* bloque;
* la verificación de que todo bloque que contiene a la arista `s(a,b)` es precisamente `own a b`.

La disjunción por aristas se sigue entonces sin ningún análisis de casos adicional
(`packingOfOwn`).  El módulo incluye además las cuentas de vértice que se usan al borrar un
punto de una descomposición triangular completa.
-/

namespace ThreeRegime.Owner

open Finset PaperIV PaperIV.FarRounding

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## 1. De una función dueño a un empaquetamiento -/

/-- **Empaquetamiento definido por una función dueño.** -/
def packingOfOwn (blocks : Finset (Finset V)) (own : V → V → Finset V)
    (hcard : ∀ K ∈ blocks, K.card = 3 ∨ K.card = 4)
    (hown : ∀ K ∈ blocks, ∀ a b : V, s(a, b) ∈ pairs K → K = own a b) :
    Packing (⊤ : SimpleGraph V) where
  pieces := blocks
  isItem := fun K hK => Transport.isItem_top_iff.2 (hcard K hK)
  edgeDisjoint := by
    intro K hK L hL hKL
    rw [Finset.disjoint_left]
    intro e he he'
    induction e using Sym2.ind with
    | _ a b => exact hKL ((hown K hK a b he).trans (hown L hL a b he').symm)

@[simp] theorem packingOfOwn_pieces (blocks : Finset (Finset V)) (own : V → V → Finset V)
    (hcard : ∀ K ∈ blocks, K.card = 3 ∨ K.card = 4)
    (hown : ∀ K ∈ blocks, ∀ a b : V, s(a, b) ∈ pairs K → K = own a b) :
    (packingOfOwn blocks own hcard hown).pieces = blocks := rfl

/-- Cualquier subfamilia de un empaquetamiento es un empaquetamiento. -/
def subPacking (P : Packing (⊤ : SimpleGraph V)) (S : Finset (Finset V)) (hS : S ⊆ P.pieces) :
    Packing (⊤ : SimpleGraph V) where
  pieces := S
  isItem := fun K hK => P.isItem K (hS hK)
  edgeDisjoint := fun K hK L hL h => P.edgeDisjoint K (hS hK) L (hS hL) h

@[simp] theorem subPacking_pieces (P : Packing (⊤ : SimpleGraph V)) (S : Finset (Finset V))
    (hS : S ⊆ P.pieces) : (subPacking P S hS).pieces = S := rfl

/-! ## 2. La ganancia a partir del recuento de aristas cubiertas -/

/-- **`3·ganancia = 2·(aristas cubiertas) + 3·(piezas `K₄`)`.** -/
theorem three_mul_gain (P : Packing (⊤ : SimpleGraph V)) :
    3 * P.gain = 2 * (P.pieces.biUnion pairs).card
      + 3 * (P.pieces.filter (fun K => K.card = 4)).card := by
  have h1 := P.card_biUnion
  have h2 := Transport.gain_eq_two_mul_card_add_three_mul_card_four P
  omega

/-! ## 3. Cuentas de vértice en una descomposición triangular completa -/

section Complete

variable (P : Packing (⊤ : SimpleGraph V))

private theorem pairs_mono' {K L : Finset V} (h : K ⊆ L) : pairs K ⊆ pairs L := by
  intro e he
  obtain ⟨hall, hdiag⟩ := mem_pairs.1 he
  exact mem_pairs.2 ⟨fun a ha => h (hall a ha), hdiag⟩

/-- En una descomposición triangular completa cada vértice está en exactamente `(n−1)/2`
piezas. -/
theorem two_mul_card_pieces_at (htri : ∀ K ∈ P.pieces, K.card = 3)
    (hcov : (⊤ : SimpleGraph V).edgeFinset ⊆ P.pieces.biUnion pairs) (v : V) :
    2 * (P.pieces.filter (fun K => v ∈ K)).card = Fintype.card V - 1 := by
  classical
  set A := P.pieces.filter (fun K => v ∈ K) with hA
  have hdisj : ∀ K ∈ A, ∀ L ∈ A, K ≠ L →
      Disjoint ((pairs K).filter (fun e => v ∈ e)) ((pairs L).filter (fun e => v ∈ e)) := by
    intro K hK L hL hne
    exact (P.edgeDisjoint K (Finset.mem_filter.1 hK).1 L (Finset.mem_filter.1 hL).1
      hne).mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hcards : ∀ K ∈ A, ((pairs K).filter (fun e => v ∈ e)).card = 2 := by
    intro K hK
    obtain ⟨hKP, hvK⟩ := Finset.mem_filter.1 hK
    rw [TrianglePackingParity.card_filter_mem_pairs hvK, htri K hKP]
  have hsum : (A.biUnion fun K => (pairs K).filter (fun e => v ∈ e)).card = 2 * A.card := by
    rw [Finset.card_biUnion hdisj, Finset.sum_congr rfl hcards, Finset.sum_const,
      smul_eq_mul, Nat.mul_comm]
  have heq : (A.biUnion fun K => (pairs K).filter (fun e => v ∈ e))
      = (pairs (Finset.univ : Finset V)).filter (fun e => v ∈ e) := by
    refine Finset.Subset.antisymm (fun e he => ?_) (fun e he => ?_)
    · obtain ⟨K, hK, hmem⟩ := Finset.mem_biUnion.1 he
      obtain ⟨hpair, hv⟩ := Finset.mem_filter.1 hmem
      exact Finset.mem_filter.2 ⟨pairs_mono' (Finset.subset_univ K) hpair, hv⟩
    · obtain ⟨hpair, hv⟩ := Finset.mem_filter.1 he
      have hedge : e ∈ (⊤ : SimpleGraph V).edgeFinset := by
        rwa [← ThreeRegime.pairs_univ_eq_edgeFinset]
      obtain ⟨K, hK, heK⟩ := Finset.mem_biUnion.1 (hcov hedge)
      have hvK : v ∈ K := (mem_pairs.1 heK).1 v hv
      exact Finset.mem_biUnion.2 ⟨K, Finset.mem_filter.2 ⟨hK, hvK⟩,
        Finset.mem_filter.2 ⟨heK, hv⟩⟩
  have htotal : ((pairs (Finset.univ : Finset V)).filter (fun e => v ∈ e)).card
      = Fintype.card V - 1 := by
    rw [TrianglePackingParity.card_filter_mem_pairs (Finset.mem_univ v), Finset.card_univ]
  rw [← hsum, heq, htotal]

/-- Una descomposición triangular completa de `K_n` tiene `n(n−1)/6` piezas. -/
theorem six_mul_card_pieces (htri : ∀ K ∈ P.pieces, K.card = 3)
    (hcov : P.pieces.biUnion pairs = (⊤ : SimpleGraph V).edgeFinset) :
    6 * P.pieces.card = Fintype.card V * (Fintype.card V - 1) := by
  have hgain : P.gain = 2 * P.pieces.card :=
    ThreeRegime.gain_of_all_triangles P htri
  have h1 := P.card_biUnion
  rw [hcov, SimpleGraph.card_edgeFinset_top_eq_card_choose_two] at h1
  have h2 := ThreeRegime.six_mul_choose_two (Fintype.card V)
  omega

/-- **Borrado de un punto.**  Las piezas que evitan a `v` son `(n−1)(n−3)/6`. -/
theorem six_mul_card_pieces_avoiding (htri : ∀ K ∈ P.pieces, K.card = 3)
    (hcov : P.pieces.biUnion pairs = (⊤ : SimpleGraph V).edgeFinset) (v : V) :
    6 * (P.pieces.filter (fun K => v ∉ K)).card + 3 * (Fintype.card V - 1)
      = Fintype.card V * (Fintype.card V - 1) := by
  classical
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := P.pieces) (p := fun K => v ∈ K)
  have hA := two_mul_card_pieces_at P htri (fun e he => hcov ▸ he) v
  have hP := six_mul_card_pieces P htri hcov
  omega

end Complete

end ThreeRegime.Owner

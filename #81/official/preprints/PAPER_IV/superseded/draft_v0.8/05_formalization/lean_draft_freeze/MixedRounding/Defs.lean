import Mathlib

/-!
# Redondeo mixto `K₃/K₄` — definiciones neutrales

Biblioteca **neutral**: depende sólo de Mathlib, de ningún paper del programa.  La idea es que
Paper V y Paper VI puedan importarla sin arrastrar `PaperIV`.

## La meta

```
UniformRoundingTarget ε :
  ∃ N, ∀ n ≥ N, ∀ G : SimpleGraph (Fin n), ∀ x : FracPacking G,
    ∃ P : Packing G, x.value − P.gain ≤ ε·n²
```

Sin `IsChordal`.  Conviene decir en voz alta lo que eso implica: quitar la cordalidad **no
simplifica, fortalece**.  El enunciado pasa a ser exactamente el régimen de Haxell–Rödl (para
`K₃`) y Yuster (para `K_r`), es decir que la brecha de integralidad del LP de empaquetamiento
por aristas es `o(n²)` en **todo** grafo.  Es un teorema verdadero y conocido, pero no queda
ningún atajo por cordalidad.

## Duplicación deliberada

Las definiciones de abajo replican las de `PaperIV.FarRounding`.  Es duplicación consciente: el
precio de que la biblioteca sea neutral.  Quien conecte esto con `PaperIV` necesitará un
adaptador de una línea por definición, y conviene escribirlo pronto para que las dos copias no
diverjan.
-/

namespace MixedRounding

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## 1. Items: las copias de `K₃` y `K₄` -/

/-- Las parejas no diagonales de un conjunto de vértices. -/
def pairs (K : Finset V) : Finset (Sym2 V) := K.sym2.filter fun e => ¬ e.IsDiag

lemma mem_pairs {K : Finset V} {e : Sym2 V} :
    e ∈ pairs K ↔ (∀ a ∈ e, a ∈ K) ∧ ¬ e.IsDiag := by
  simp [pairs]

lemma mk_mem_pairs {K : Finset V} {a b : V} :
    s(a, b) ∈ pairs K ↔ a ∈ K ∧ b ∈ K ∧ a ≠ b := by
  simp only [pairs, Finset.mem_filter, Finset.mk_mem_sym2_iff, Sym2.isDiag_iff_proj_eq]
  tauto

/-- Un **item** es una copia de `K₃` o de `K₄`. -/
def IsItem (G : SimpleGraph V) (K : Finset V) : Prop :=
  (∀ a ∈ K, ∀ b ∈ K, a ≠ b → G.Adj a b) ∧ (K.card = 3 ∨ K.card = 4)

instance (G : SimpleGraph V) [DecidableRel G.Adj] (K : Finset V) :
    Decidable (IsItem G K) := by unfold IsItem; infer_instance

/-- Todos los items de `G`. -/
def items (G : SimpleGraph V) [DecidableRel G.Adj] : Finset (Finset V) :=
  Finset.univ.filter fun K => IsItem G K

lemma mem_items {G : SimpleGraph V} [DecidableRel G.Adj] {K : Finset V} :
    K ∈ items G ↔ IsItem G K := by simp [items]

/-- La ganancia de un item: `C(|K|,2) − 1`, o sea `2` para `K₃` y `5` para `K₄`. -/
def gainOf (K : Finset V) : ℕ := K.card.choose 2 - 1

/-- La ganancia en un cuerpo ordenado. -/
def gainF (F : Type*) [Field F] (K : Finset V) : F := (K.card.choose 2 : F) - 1

lemma gainF_le_five {G : SimpleGraph V} {K : Finset V} (hK : IsItem G K) :
    gainF ℚ K ≤ 5 := by
  rcases hK.2 with h3 | h4
  · rw [gainF, h3]; norm_num
  · have e42 : Nat.choose 4 2 = 6 := by decide
    rw [gainF, h4, e42]; norm_num

lemma gainF_nonneg {G : SimpleGraph V} {K : Finset V} (hK : IsItem G K) :
    (0 : ℚ) ≤ gainF ℚ K := by
  rcases hK.2 with h3 | h4
  · rw [gainF, h3]; norm_num
  · have e42 : Nat.choose 4 2 = 6 := by decide
    rw [gainF, h4, e42]; norm_num

/-- Las aristas de un item son aristas reales de `G`. -/
lemma pairs_subset_edgeFinset {G : SimpleGraph V} [DecidableRel G.Adj] {K : Finset V}
    (h : IsItem G K) : pairs K ⊆ G.edgeFinset := by
  intro e he
  induction e using Sym2.ind with
  | _ a b =>
    rw [mk_mem_pairs] at he
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact h.1 a he.1 b he.2.1 he.2.2

/-! ## 2. El LP de empaquetamiento mixto -/

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Un **empaquetamiento fraccional**: pesos no negativos cuya carga sobre cada arista real de
`G` no excede `1`. -/
structure FracPacking where
  weight : Finset V → ℚ
  weight_nonneg : ∀ K, 0 ≤ weight K
  capacity : ∀ e ∈ G.edgeFinset,
    ∑ K ∈ items G, (if e ∈ pairs K then weight K else 0) ≤ 1

variable {G}

/-- El valor de un empaquetamiento fraccional. -/
def FracPacking.value (x : FracPacking G) : ℚ := ∑ K ∈ items G, gainF ℚ K * x.weight K

variable (G)

/-- Un **empaquetamiento físico**: items reales, disjuntos por aristas. -/
structure Packing where
  pieces : Finset (Finset V)
  isItem : ∀ K ∈ pieces, IsItem G K
  edgeDisjoint : ∀ K ∈ pieces, ∀ L ∈ pieces, K ≠ L → Disjoint (pairs K) (pairs L)

variable {G}

/-- La ganancia de un empaquetamiento físico. -/
def Packing.gain (P : Packing G) : ℕ := ∑ K ∈ P.pieces, gainOf K

/-! ## 3. La meta -/

/-- **`UniformRoundingTarget ε`** — el contrato CMR, sin cordalidad.

Para todo grafo suficientemente grande y todo empaquetamiento fraccional mixto, existe un
empaquetamiento físico que pierde a lo sumo `ε·n²`. -/
def UniformRoundingTarget (ε : ℚ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    ∀ x : FracPacking G, ∃ P : Packing G,
      x.value - (P.gain : ℚ) ≤ ε * (n : ℚ) ^ 2

/-! ## 4. Hipergrafos, en forma neutral -/

/-- Un hipergrafo es `r`-uniforme si toda hiperarista tiene `r` vértices. -/
def IsUniformHypergraph {W : Type*} (H : Finset (Finset W)) (r : ℕ) : Prop :=
  ∀ e ∈ H, e.card = r

/-- Un matching: subfamilia de hiperaristas disjuntas dos a dos. -/
structure IsHypergraphMatching {W : Type*} [DecidableEq W] (H M : Finset (Finset W)) : Prop where
  subset : M ⊆ H
  disjoint : ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f

end MixedRounding

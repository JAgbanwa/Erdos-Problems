-- Import-order pin (build optimisation): loading `Field.Defs` before `EuclideanDomain` keeps the
-- baseline instance path `Field.toEuclideanDomain`/`EuclideanDomain.toCommRing` in `FracPacking`.
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Rat.Star
import Mathlib.Order.Partition.Basic
import PaperIV.ChordalStructure

/-!
# Far rounding for the mixed `{K₃, K₄}` packing problem (component E01)

This module formalizes the *literal* objects behind the far-regime statement of the
candidate route, and every finite reduction around it.  It is deliberately
self-contained: it imports `Mathlib` only.  It does **not** import
`AlternativeAssembly`, `MainTheorem`, `NearTerminalInput`, any Paper V material, or
any historical aggregate source, and it contains no `axiom`, `sorry`, `admit` or
`implemented_by`.

## What is proved here

* `pairs` : the literal edge support of a vertex set, with `card_pairs`
  (prerequisite 1: the resources are the edges of `G`).
* `IsItem` / `items` : real cliques of `G` of size three or four (prerequisite 2),
  with gains `2` and `5` (`gainOf_of_card_eq_three`, `gainOf_of_card_eq_four`).
* `FracPacking` : fractional packing with **unit capacity per edge** (prerequisite 3),
  over any linearly ordered field.
* `Packing` : integral packing as an **edge-disjoint** family (prerequisite 4).
* `weak_duality`, `CertifiedFractionalOptimum`, `certified_value_unique`,
  `certified_isOptimum`, `gain_le_of_certified` : the finite LP layer.
* `certified_real_le`, `exists_real_fracPacking_value_eq` : the rational-to-real
  bridge (prerequisite 6).
* `exists_cliquePartition_of_packing` : packing-to-partition completion with `K₂`
  (prerequisite 7), in the subtraction-free form `Q.size + P.gain = e(G)`.

## What is *not* proved here

The uniform weighted transfer for the fixed family `{K₃, K₄}` (prerequisite 5,
Rohatgi–Urschel–Wellens) is **not** formalized.  It appears only as the explicitly
named predicate `UniformTransferAt` and its chordal restriction `FarRoundingAt`,
which are *hypotheses* of the theorems below, never conclusions.  See
`FarRoundingDependencies.md` for the exact remaining statement.

The general transfer statement (`UniformTransferAt`, all finite graphs) is kept
separate from the corollary restricted to chordal graphs (`FarRoundingAt`); the
implication between them is `farRoundingAt_of_uniformTransferAt`.
-/

namespace PaperIV.FarRounding

open Finset

/-! ## 1. Literal resource model: the edges of `G` -/

section Pairs

variable {V : Type*} [DecidableEq V]

/-- The literal edge support of a vertex set: its off-diagonal unordered pairs. -/
def pairs (K : Finset V) : Finset (Sym2 V) := K.sym2.filter fun e => ¬ e.IsDiag

lemma mem_pairs {K : Finset V} {e : Sym2 V} :
    e ∈ pairs K ↔ (∀ a ∈ e, a ∈ K) ∧ ¬ e.IsDiag := by
  simp [pairs]

lemma mk_mem_pairs {K : Finset V} {a b : V} :
    s(a, b) ∈ pairs K ↔ a ∈ K ∧ b ∈ K ∧ a ≠ b := by
  simp only [pairs, Finset.mem_filter, Finset.mk_mem_sym2_iff, Sym2.isDiag_iff_proj_eq]
  tauto

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

/-- The edge support of a `k`-set has exactly `k.choose 2` elements. -/
lemma card_pairs (K : Finset V) : (pairs K).card = K.card.choose 2 := by
  have hsplit := Finset.card_filter_add_card_filter_not (s := K.sym2) (fun e => e.IsDiag)
  rw [filter_isDiag_sym2, Finset.card_image_of_injective _ Sym2.diag_injective,
    Finset.card_sym2] at hsplit
  have hchoose : (K.card + 1).choose 2 = K.card + K.card.choose 2 := by
    rw [Nat.choose_succ_succ K.card 1, Nat.choose_one_right]
  rw [hchoose] at hsplit
  exact Nat.add_left_cancel hsplit

/-- A non-degenerate unordered pair is the edge support of its own vertex set. -/
lemma pairs_toFinset {e : Sym2 V} (he : ¬ e.IsDiag) : pairs e.toFinset = {e} := by
  induction e using Sym2.ind with
  | _ a b =>
    have hab : a ≠ b := by
      rw [Sym2.isDiag_iff_proj_eq] at he; exact he
    ext f
    induction f using Sym2.ind with
    | _ c d =>
      rw [mk_mem_pairs, Finset.mem_singleton, Sym2.eq_iff]
      simp only [Sym2.mem_toFinset, Sym2.mem_iff]
      constructor
      · rintro ⟨hc, hd, hcd⟩
        rcases hc with rfl | rfl
        · rcases hd with rfl | rfl
          · exact absurd rfl hcd
          · exact Or.inl ⟨rfl, rfl⟩
        · rcases hd with rfl | rfl
          · exact Or.inr ⟨rfl, rfl⟩
          · exact absurd rfl hcd
      · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
        · exact ⟨Or.inl rfl, Or.inr rfl, hab⟩
        · exact ⟨Or.inr rfl, Or.inl rfl, fun h => hab h.symm⟩

/-- The natural gain of a clique of size `k`: `k.choose 2 - 1`, i.e. `2` for `K₃`
and `5` for `K₄`. -/
def gainOf (K : Finset V) : ℕ := K.card.choose 2 - 1

lemma gainOf_of_card_eq_three {K : Finset V} (h : K.card = 3) : gainOf K = 2 := by
  rw [gainOf, h]; decide

lemma gainOf_of_card_eq_four {K : Finset V} (h : K.card = 4) : gainOf K = 5 := by
  rw [gainOf, h]; decide

/-- Splitting a union of `biUnion`s. -/
lemma biUnion_union_eq {ι : Type*} [DecidableEq ι] (s t : Finset ι)
    (f : ι → Finset (Sym2 V)) :
    (s ∪ t).biUnion f = s.biUnion f ∪ t.biUnion f := by
  ext e
  simp only [Finset.mem_biUnion, Finset.mem_union]
  constructor
  · rintro ⟨a, ha | ha, he⟩
    · exact Or.inl ⟨a, ha, he⟩
    · exact Or.inr ⟨a, ha, he⟩
  · rintro (⟨a, ha, he⟩ | ⟨a, ha, he⟩)
    · exact ⟨a, Or.inl ha, he⟩
    · exact ⟨a, Or.inr ha, he⟩

end Pairs

/-! ## 2. Objects: real `K₃` and `K₄` copies -/

section Items

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A *mixed item*: a real clique of `G` on exactly three or four vertices.
The clique condition is stated on literal vertices of `G`. -/
def IsItem (G : SimpleGraph V) (K : Finset V) : Prop :=
  (∀ a ∈ K, ∀ b ∈ K, a ≠ b → G.Adj a b) ∧ (K.card = 3 ∨ K.card = 4)

instance (G : SimpleGraph V) [DecidableRel G.Adj] (K : Finset V) :
    Decidable (IsItem G K) := by
  unfold IsItem; infer_instance

/-- The finite set of all mixed items of `G`. -/
def items (G : SimpleGraph V) [DecidableRel G.Adj] : Finset (Finset V) :=
  Finset.univ.filter fun K => IsItem G K

lemma mem_items {G : SimpleGraph V} [DecidableRel G.Adj] {K : Finset V} :
    K ∈ items G ↔ IsItem G K := by
  simp [items]

variable {G : SimpleGraph V}

lemma one_le_choose_two_of_isItem {K : Finset V} (h : IsItem G K) :
    1 ≤ K.card.choose 2 := by
  rcases h.2 with h3 | h3 <;> rw [h3] <;> decide

/-- For an item, the edge support has exactly `gain + 1` elements. -/
lemma card_pairs_of_isItem {K : Finset V} (h : IsItem G K) :
    (pairs K).card = gainOf K + 1 := by
  rw [card_pairs, gainOf]
  exact (Nat.sub_add_cancel (one_le_choose_two_of_isItem h)).symm

/-- The edge support of an item consists of real edges of `G`. -/
lemma pairs_subset_edgeFinset [DecidableRel G.Adj] {K : Finset V} (h : IsItem G K) :
    pairs K ⊆ G.edgeFinset := by
  intro e he
  induction e using Sym2.ind with
  | _ a b =>
    rw [mk_mem_pairs] at he
    obtain ⟨ha, hb, hab⟩ := he
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact h.1 a ha b hb hab

end Items

/-! ## 3. Fractional packing with unit capacity per edge -/

section Fractional

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (F : Type*) [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- The gain of an item as a field element. -/
def gainF (K : Finset V) : F := (K.card.choose 2 : F) - 1

/-- A fractional mixed packing: nonnegative weights on items whose total load on
every real edge of `G` is at most one. -/
structure FracPacking where
  weight : Finset V → F
  weight_nonneg : ∀ K, 0 ≤ weight K
  capacity : ∀ e ∈ G.edgeFinset,
    ∑ K ∈ items G, (if e ∈ pairs K then weight K else 0) ≤ 1

/-- A feasible dual: nonnegative edge prices covering every item's gain. -/
structure DualCover where
  price : Sym2 V → F
  price_nonneg : ∀ e, 0 ≤ price e
  covers : ∀ K ∈ items G, gainF F K ≤ ∑ e ∈ pairs K, price e

variable {G F}

/-- The value of a fractional packing. -/
def FracPacking.value (x : FracPacking G F) : F := ∑ K ∈ items G, gainF F K * x.weight K

/-- The value of a dual cover. -/
def DualCover.value (y : DualCover G F) : F := ∑ e ∈ G.edgeFinset, y.price e

/-- Weak duality for the mixed `{K₃, K₄}` linear program. -/
theorem weak_duality (x : FracPacking G F) (y : DualCover G F) :
    x.value ≤ y.value := by
  have step₁ :
      x.value ≤ ∑ K ∈ items G, (∑ e ∈ pairs K, y.price e) * x.weight K :=
    Finset.sum_le_sum fun K hK =>
      mul_le_mul_of_nonneg_right (y.covers K hK) (x.weight_nonneg K)
  have step₂ :
      ∑ K ∈ items G, (∑ e ∈ pairs K, y.price e) * x.weight K =
        ∑ e ∈ G.edgeFinset, y.price e *
          ∑ K ∈ items G, (if e ∈ pairs K then x.weight K else 0) := by
    have expand : ∀ K ∈ items G,
        (∑ e ∈ pairs K, y.price e) * x.weight K =
          ∑ e ∈ G.edgeFinset, (if e ∈ pairs K then y.price e * x.weight K else 0) := by
      intro K hK
      have hsub : pairs K ⊆ G.edgeFinset := pairs_subset_edgeFinset (mem_items.1 hK)
      rw [Finset.sum_mul]
      rw [← Finset.sum_subset hsub (fun e _ hnot => by simp [hnot])]
      exact Finset.sum_congr rfl fun e he => by simp [he]
    rw [Finset.sum_congr rfl expand, Finset.sum_comm]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun K _ => by by_cases h : e ∈ pairs K <;> simp [h]
  have step₃ :
      ∑ e ∈ G.edgeFinset, y.price e *
          ∑ K ∈ items G, (if e ∈ pairs K then x.weight K else 0) ≤ y.value := by
    rw [DualCover.value]
    refine Finset.sum_le_sum fun e he => ?_
    calc y.price e * ∑ K ∈ items G, (if e ∈ pairs K then x.weight K else 0)
        ≤ y.price e * 1 := mul_le_mul_of_nonneg_left (x.capacity e he) (y.price_nonneg e)
      _ = y.price e := mul_one _
  calc x.value ≤ ∑ K ∈ items G, (∑ e ∈ pairs K, y.price e) * x.weight K := step₁
    _ = _ := step₂
    _ ≤ y.value := step₃

end Fractional

/-! ## 4. Integral packing: an edge-disjoint family of items -/

section Integral

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A physical (integral) mixed packing: a family of items whose literal edge
supports are pairwise disjoint. -/
structure Packing where
  pieces : Finset (Finset V)
  isItem : ∀ K ∈ pieces, IsItem G K
  edgeDisjoint : ∀ K ∈ pieces, ∀ L ∈ pieces, K ≠ L → Disjoint (pairs K) (pairs L)

variable {G}

/-- The gain of a physical packing. -/
def Packing.gain (P : Packing G) : ℕ := ∑ K ∈ P.pieces, gainOf K

lemma Packing.pieces_subset_items (P : Packing G) : P.pieces ⊆ items G :=
  fun _ hK => mem_items.2 (P.isItem _ hK)

lemma Packing.pairwiseDisjoint (P : Packing G) :
    (↑P.pieces : Set (Finset V)).PairwiseDisjoint pairs := by
  intro K hK L hL hKL
  exact P.edgeDisjoint K (by simpa using hK) L (by simpa using hL) hKL

lemma Packing.card_biUnion (P : Packing G) :
    (P.pieces.biUnion pairs).card = P.gain + P.pieces.card := by
  rw [Finset.card_biUnion P.pairwiseDisjoint,
    Finset.sum_congr rfl (fun K hK => card_pairs_of_isItem (P.isItem K hK)),
    Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
  rfl

lemma Packing.biUnion_subset_edgeFinset (P : Packing G) :
    P.pieces.biUnion pairs ⊆ G.edgeFinset := by
  intro e he
  obtain ⟨K, hK, heK⟩ := Finset.mem_biUnion.1 he
  exact pairs_subset_edgeFinset (P.isItem K hK) heK

/-- The gain of a physical packing never exceeds the number of edges. -/
theorem Packing.gain_add_card_le (P : Packing G) :
    P.gain + P.pieces.card ≤ G.edgeFinset.card := by
  rw [← P.card_biUnion]
  exact Finset.card_le_card P.biUnion_subset_edgeFinset

theorem Packing.gain_le_card_edgeFinset (P : Packing G) :
    P.gain ≤ G.edgeFinset.card :=
  le_trans (Nat.le_add_right _ _) P.gain_add_card_le

end Integral

/-! ## 5. Clique partitions and the packing-to-partition completion -/

section Partition

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A physical clique partition of the edges of `G`: nontrivial real cliques whose
literal edge supports are pairwise disjoint and cover every edge. -/
structure CliquePartition where
  pieces : Finset (Finset V)
  isClique : ∀ K ∈ pieces, ∀ a ∈ K, ∀ b ∈ K, a ≠ b → G.Adj a b
  two_le_card : ∀ K ∈ pieces, 2 ≤ K.card
  edgeDisjoint : ∀ K ∈ pieces, ∀ L ∈ pieces, K ≠ L → Disjoint (pairs K) (pairs L)
  covers : pieces.biUnion pairs = G.edgeFinset

variable {G}

/-- The number of pieces. -/
def CliquePartition.size (Q : CliquePartition G) : ℕ := Q.pieces.card

/-- Every piece has at most `r` vertices. -/
def CliquePartition.OrderAtMost (Q : CliquePartition G) (r : ℕ) : Prop :=
  ∀ K ∈ Q.pieces, K.card ≤ r

/-- **Packing-to-partition completion.**  Completing a physical mixed packing with
one `K₂` per uncovered edge yields a clique partition of order at most four whose
size is exactly `e(G) - gain(P)`, stated without natural subtraction. -/
theorem exists_cliquePartition_of_packing (P : Packing G) :
    ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size + P.gain = G.edgeFinset.card := by
  classical
  set rest : Finset (Sym2 V) := G.edgeFinset \ P.pieces.biUnion pairs with hrest
  set newPieces : Finset (Finset V) := rest.image Sym2.toFinset with hnew
  have hrest_not_diag : ∀ e ∈ rest, ¬ e.IsDiag := fun e he =>
    G.not_isDiag_of_mem_edgeFinset (Finset.mem_sdiff.1 he).1
  have hpairs_new : ∀ e ∈ rest, pairs e.toFinset = {e} := fun e he =>
    pairs_toFinset (hrest_not_diag e he)
  have hcard_new : ∀ e ∈ rest, e.toFinset.card = 2 := fun e he =>
    Sym2.card_toFinset_of_not_isDiag e (hrest_not_diag e he)
  have hedge_new : ∀ e ∈ rest, ∀ a ∈ e.toFinset, ∀ b ∈ e.toFinset, a ≠ b → G.Adj a b := by
    intro e he a ha b hb hab
    have hmem : s(a, b) ∈ pairs e.toFinset := mk_mem_pairs.2 ⟨ha, hb, hab⟩
    rw [hpairs_new e he, Finset.mem_singleton] at hmem
    subst hmem
    have hE := (Finset.mem_sdiff.1 he).1
    rwa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at hE
  have hinj : Set.InjOn Sym2.toFinset (↑rest : Set (Sym2 V)) := by
    intro e he f hf h
    have hsing : ({e} : Finset (Sym2 V)) = {f} := by
      rw [← hpairs_new e (by simpa using he), ← hpairs_new f (by simpa using hf), h]
    simpa using hsing
  have hdisj_old_new : Disjoint P.pieces newPieces := by
    rw [Finset.disjoint_right]
    intro K hK hKP
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hK
    have h2 := hcard_new e he
    rcases (P.isItem _ hKP).2 with h3 | h4 <;> omega
  have hnew_pairs_mem : ∀ K ∈ newPieces, ∃ e ∈ rest, pairs K = {e} := by
    intro K hK
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hK
    exact ⟨e, he, hpairs_new e he⟩
  have hkey : ∀ A ∈ newPieces, ∀ B ∈ P.pieces ∪ newPieces, A ≠ B →
      Disjoint (pairs A) (pairs B) := by
    intro A hA B hB hAB
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hA
    rw [hpairs_new e he, Finset.disjoint_singleton_left]
    intro hmem
    rcases Finset.mem_union.1 hB with h | h
    · exact (Finset.mem_sdiff.1 he).2 (Finset.mem_biUnion.2 ⟨B, h, hmem⟩)
    · obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 h
      rw [hpairs_new g hg, Finset.mem_singleton] at hmem
      exact hAB (by rw [hmem])
  refine ⟨⟨P.pieces ∪ newPieces, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro K hK a ha b hb hab
    rcases Finset.mem_union.1 hK with h | h
    · exact (P.isItem K h).1 a ha b hb hab
    · obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 h
      exact hedge_new e he a ha b hb hab
  · intro K hK
    rcases Finset.mem_union.1 hK with h | h
    · rcases (P.isItem K h).2 with h3 | h4 <;> omega
    · obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 h
      exact le_of_eq (hcard_new e he).symm
  · intro K hK L hL hKL
    rcases Finset.mem_union.1 hK with hKo | hKn
    · rcases Finset.mem_union.1 hL with hLo | hLn
      · exact P.edgeDisjoint K hKo L hLo hKL
      · exact (hkey L hLn K hK (Ne.symm hKL)).symm
    · exact hkey K hKn L hL hKL
  · rw [biUnion_union_eq]
    have h₁ : newPieces.biUnion pairs = rest := by
      ext e
      simp only [Finset.mem_biUnion]
      constructor
      · rintro ⟨K, hK, heK⟩
        obtain ⟨f, hf, hKf⟩ := hnew_pairs_mem K hK
        rw [hKf, Finset.mem_singleton] at heK
        exact heK ▸ hf
      · intro he
        exact ⟨e.toFinset, Finset.mem_image.2 ⟨e, he, rfl⟩,
          by rw [hpairs_new e he]; exact Finset.mem_singleton_self e⟩
    rw [h₁, hrest]
    ext e
    simp only [Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro (h | h)
      · exact P.biUnion_subset_edgeFinset h
      · exact h.1
    · intro h
      by_cases hm : e ∈ P.pieces.biUnion pairs
      · exact Or.inl hm
      · exact Or.inr ⟨h, hm⟩
  · intro K hK
    rcases Finset.mem_union.1 hK with h | h
    · rcases (P.isItem K h).2 with h3 | h4 <;> omega
    · obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 h
      have h2 := hcard_new e he
      omega
  · have hcard_union : (P.pieces ∪ newPieces).card = P.pieces.card + newPieces.card :=
      Finset.card_union_of_disjoint hdisj_old_new
    have hcard_image : newPieces.card = rest.card := Finset.card_image_of_injOn hinj
    have hle := Finset.card_le_card P.biUnion_subset_edgeFinset
    have hcard_rest : rest.card = G.edgeFinset.card - (P.gain + P.pieces.card) := by
      rw [hrest, Finset.card_sdiff_of_subset P.biUnion_subset_edgeFinset, P.card_biUnion]
    have hbound := P.gain_add_card_le
    show (P.pieces ∪ newPieces).card + P.gain = G.edgeFinset.card
    rw [hcard_union, hcard_image, hcard_rest]
    rw [P.card_biUnion] at hle
    omega

end Partition

/-! ## 6. Certified fractional optimum and the rational-to-real bridge -/

section Certificates

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A rational certificate of optimality: a feasible primal and a feasible dual of
the same value `w`. -/
def CertifiedFractionalOptimum (w : ℚ) : Prop :=
  ∃ x : FracPacking G ℚ, ∃ y : DualCover G ℚ, x.value = w ∧ y.value = w

variable {G}

/-- A certificate pins down the fractional optimum: no fractional packing beats it. -/
theorem certified_isOptimum {w : ℚ} (h : CertifiedFractionalOptimum G w)
    (x : FracPacking G ℚ) : x.value ≤ w := by
  obtain ⟨-, y, -, hy⟩ := h
  exact hy ▸ weak_duality x y

/-- The certified value is unique. -/
theorem certified_value_unique {w w' : ℚ} (h : CertifiedFractionalOptimum G w)
    (h' : CertifiedFractionalOptimum G w') : w = w' := by
  obtain ⟨x, -, hx, -⟩ := id h
  obtain ⟨x', -, hx', -⟩ := id h'
  exact le_antisymm (hx ▸ certified_isOptimum h' x) (hx' ▸ certified_isOptimum h x')

/-- A physical packing induces a fractional packing of the same value. -/
def Packing.toFrac {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    (P : Packing G) : FracPacking G F where
  weight := fun K => if K ∈ P.pieces then 1 else 0
  weight_nonneg := by
    intro K; by_cases h : K ∈ P.pieces <;> simp [h]
  capacity := by
    intro e _
    classical
    set T : Finset (Finset V) := P.pieces.filter fun K => e ∈ pairs K with hT
    have hTsub : T ⊆ items G := fun K hK =>
      P.pieces_subset_items (Finset.mem_filter.1 hK).1
    have hvanish : ∀ K ∈ items G, K ∉ T →
        (if e ∈ pairs K then (if K ∈ P.pieces then (1 : F) else 0) else 0) = 0 := by
      intro K _ hKT
      by_cases h₁ : e ∈ pairs K
      · by_cases h₂ : K ∈ P.pieces
        · exact absurd (Finset.mem_filter.2 ⟨h₂, h₁⟩) hKT
        · simp [h₁, h₂]
      · simp [h₁]
    have hsum : ∑ K ∈ items G, (if e ∈ pairs K then (if K ∈ P.pieces then (1 : F) else 0) else 0)
        = (T.card : F) := by
      rw [← Finset.sum_subset hTsub hvanish]
      have hone_on : ∀ K ∈ T,
          (if e ∈ pairs K then (if K ∈ P.pieces then (1 : F) else 0) else 0) = 1 := by
        intro K hK
        rw [hT, Finset.mem_filter] at hK
        rw [if_pos hK.2, if_pos hK.1]
      rw [Finset.sum_congr rfl hone_on, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hone : T.card ≤ 1 := by
      rw [Finset.card_le_one]
      intro K hK L hL
      rw [hT, Finset.mem_filter] at hK hL
      by_contra hne
      exact (Finset.disjoint_left.1 (P.edgeDisjoint K hK.1 L hL.1 hne)) hK.2 hL.2
    rw [hsum]
    exact_mod_cast hone

lemma gainF_eq_gainOf {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    {K : Finset V} (h : IsItem G K) : gainF F K = (gainOf K : F) := by
  rw [gainF, gainOf, Nat.cast_sub (one_le_choose_two_of_isItem h), Nat.cast_one]

lemma Packing.toFrac_value {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    (P : Packing G) : (P.toFrac (F := F)).value = (P.gain : F) := by
  classical
  have hvanish : ∀ K ∈ items G, K ∉ P.pieces →
      gainF F K * (if K ∈ P.pieces then (1 : F) else 0) = 0 := by
    intro K _ hK; simp [hK]
  rw [FracPacking.value, Packing.gain]
  show ∑ K ∈ items G, gainF F K * (if K ∈ P.pieces then (1 : F) else 0) = _
  rw [← Finset.sum_subset P.pieces_subset_items hvanish]
  push_cast
  exact Finset.sum_congr rfl fun K hK => by
    rw [if_pos hK, mul_one, gainF_eq_gainOf (P.isItem K hK)]

/-- The integral optimum never exceeds a certified fractional optimum. -/
theorem gain_le_of_certified {w : ℚ} (h : CertifiedFractionalOptimum G w)
    (P : Packing G) : (P.gain : ℚ) ≤ w := by
  have hx := certified_isOptimum h (P.toFrac (F := ℚ))
  rwa [Packing.toFrac_value] at hx

/-! ### Non-vacuity guards -/

/-- The empty packing always exists, so `Packing G` is never empty. -/
def Packing.empty : Packing G where
  pieces := ∅
  isItem := by simp
  edgeDisjoint := by simp

instance : Nonempty (Packing G) := ⟨Packing.empty⟩

/-- A graph with no `K₃` and no `K₄` has certified fractional optimum `0`.  This is a
witness that `CertifiedFractionalOptimum` is inhabited, so the statements of §8 are
not vacuous on that side. -/
theorem certified_zero_of_items_empty (h : items G = ∅) :
    CertifiedFractionalOptimum G 0 := by
  refine ⟨⟨fun _ => 0, fun _ => le_refl 0, ?_⟩, ⟨fun _ => 0, fun _ => le_refl 0, ?_⟩, ?_, ?_⟩
  · intro e _; simp
  · intro K hK; rw [h] at hK; simp at hK
  · simp [FracPacking.value]
  · simp [DualCover.value]

/-! ### Rational-to-real bridge -/

/-- A rational fractional packing, read over the reals. -/
def FracPacking.toReal (x : FracPacking G ℚ) : FracPacking G ℝ where
  weight := fun K => (x.weight K : ℝ)
  weight_nonneg := fun K => by exact_mod_cast x.weight_nonneg K
  capacity := by
    intro e he
    have h := x.capacity e he
    have hcast : ∑ K ∈ items G, (if e ∈ pairs K then ((x.weight K : ℝ)) else 0) =
        ((∑ K ∈ items G, (if e ∈ pairs K then x.weight K else 0) : ℚ) : ℝ) := by
      push_cast
      exact Finset.sum_congr rfl fun K _ => by by_cases hK : e ∈ pairs K <;> simp [hK]
    rw [hcast]
    exact_mod_cast h

/-- A rational dual cover, read over the reals. -/
def DualCover.toReal (y : DualCover G ℚ) : DualCover G ℝ where
  price := fun e => (y.price e : ℝ)
  price_nonneg := fun e => by exact_mod_cast y.price_nonneg e
  covers := by
    intro K hK
    have h := y.covers K hK
    have hgain : gainF ℝ K = ((gainF ℚ K : ℚ) : ℝ) := by
      rw [gainF, gainF]; push_cast; ring
    have hsum : ∑ e ∈ pairs K, ((y.price e : ℝ)) =
        ((∑ e ∈ pairs K, y.price e : ℚ) : ℝ) := by push_cast; ring
    rw [hgain, hsum]
    exact_mod_cast h

lemma FracPacking.toReal_value (x : FracPacking G ℚ) :
    x.toReal.value = ((x.value : ℚ) : ℝ) := by
  rw [FracPacking.value, FracPacking.value]
  push_cast
  refine Finset.sum_congr rfl fun K _ => ?_
  show gainF ℝ K * ((x.weight K : ℚ) : ℝ) = _
  rw [gainF, gainF]
  push_cast
  ring

lemma DualCover.toReal_value (y : DualCover G ℚ) :
    y.toReal.value = ((y.value : ℚ) : ℝ) := by
  show ∑ e ∈ G.edgeFinset, ((y.price e : ℝ)) = ((∑ e ∈ G.edgeFinset, y.price e : ℚ) : ℝ)
  push_cast
  rfl

/-- **Rational-to-real bridge.** A rational certificate of value `w` certifies the
optimum over the reals as well. -/
theorem certified_real_le {w : ℚ} (h : CertifiedFractionalOptimum G w)
    (x : FracPacking G ℝ) : x.value ≤ (w : ℝ) := by
  obtain ⟨-, y, -, hy⟩ := h
  have hle := weak_duality x y.toReal
  rwa [DualCover.toReal_value, hy] at hle

/-- The real optimum is attained by the cast of the rational certificate. -/
theorem exists_real_fracPacking_value_eq {w : ℚ} (h : CertifiedFractionalOptimum G w) :
    ∃ x : FracPacking G ℝ, x.value = (w : ℝ) := by
  obtain ⟨x, -, hx, -⟩ := h
  exact ⟨x.toReal, by rw [FracPacking.toReal_value, hx]⟩

end Certificates

/-! ## 7. Chordality -/

/-! `G` is chordal: every cycle of length at least four has a chord.  **Alias** of the canonical
`SimpleGraph.IsChordal` (`PaperIV/ChordalStructure.lean`, the Paper II contribution merged into
`lean-pool` #349).  Chordality is a *restriction* in the statements below; no proof of this
module uses it. -/
/-- Backwards-compatible qualified name for the canonical chordality predicate.
Keeping this literal alias makes the public `PaperIV.FarRounding.IsChordal`
interface stable while all structural lemmas use `SimpleGraph.IsChordal`. -/
abbrev IsChordal {V : Type*} (G : SimpleGraph V) : Prop :=
  SimpleGraph.IsChordal G

/-! ## 8. The external transfer input, and the far regime -/

/-- **General uniform transfer** for the fixed family `{K₃, K₄}` (the statement
attributed to Rohatgi–Urschel–Wellens, in the "minor form" of the candidate route).
It speaks about *all* finite graphs: chordality does not occur.

This is a `Prop`-valued **definition**, never proved in this module. -/
def UniformTransferAt (ζ : ℚ) : Prop :=
  ∃ T : ℕ, ∀ n : ℕ, T ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (w : ℚ),
    CertifiedFractionalOptimum G w → ∃ P : Packing G, w - (P.gain : ℚ) ≤ ζ * (n : ℚ) ^ 2

/-- **Far rounding at `η`**: the corollary of the transfer restricted to chordal
graphs in the far regime.  This is the only external boundary of the assembly. -/
def FarRoundingAt (η : ℚ) : Prop :=
  ∃ T : ℕ, ∀ n : ℕ, T ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    IsChordal G → ∀ w : ℚ, CertifiedFractionalOptimum G w →
      (G.edgeFinset.card : ℚ) - w < (n : ℚ) ^ 2 / 6 - η * (n : ℚ) ^ 2 →
        ∃ P : Packing G, w - (P.gain : ℚ) ≤ η * (n : ℚ) ^ 2 / 2

/-- The general transfer implies the chordal far-rounding corollary.  The converse
is not claimed: `FarRoundingAt` is strictly weaker (chordal graphs only, far regime
only). -/
theorem farRoundingAt_of_uniformTransferAt {η : ℚ} (h : UniformTransferAt (η / 2)) :
    FarRoundingAt η := by
  obtain ⟨T, hT⟩ := h
  refine ⟨T, ?_⟩
  intro n hn G _ _ w hw _
  obtain ⟨P, hP⟩ := hT n hn G w hw
  exact ⟨P, by linarith [hP]⟩


/-! ## 9. Far-regime assembly (conditional on the external input) -/

/-- The target size `M(n) = ⌊n(n+1)/6⌋`. -/
def targetSize (n : ℕ) : ℕ := n * (n + 1) / 6

/-- **Far-regime closure, conditional on `FarRoundingAt η`.**  Every finite reduction
is internal: only the transfer hypothesis is external, and it appears explicitly in
the statement. -/
theorem farRegime_cliquePartition {η : ℚ} (hη : 0 ≤ η) (h : FarRoundingAt η) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      IsChordal G → ∀ w : ℚ, CertifiedFractionalOptimum G w →
        (G.edgeFinset.card : ℚ) - w < (n : ℚ) ^ 2 / 6 - η * (n : ℚ) ^ 2 →
          ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ targetSize n := by
  obtain ⟨T, hT⟩ := h
  refine ⟨T, ?_⟩
  intro n hn G _ hchord w hw hfar
  obtain ⟨P, hP⟩ := hT n hn G hchord w hw hfar
  obtain ⟨Q, hQ4, hQsize⟩ := exists_cliquePartition_of_packing P
  refine ⟨Q, hQ4, ?_⟩
  have hsize : (Q.size : ℚ) + (P.gain : ℚ) = (G.edgeFinset.card : ℚ) := by
    exact_mod_cast hQsize
  have hlt : (Q.size : ℚ) < (n : ℚ) ^ 2 / 6 - η * (n : ℚ) ^ 2 / 2 := by
    have hrw : (Q.size : ℚ) = ((G.edgeFinset.card : ℚ) - w) + (w - (P.gain : ℚ)) := by
      linarith
    rw [hrw]; linarith
  have hn0 : (0 : ℚ) ≤ (n : ℚ) := Nat.cast_nonneg n
  have hn2 : (n : ℚ) ^ 2 ≤ (n : ℚ) * ((n : ℚ) + 1) := by nlinarith
  have hηn : 0 ≤ η * (n : ℚ) ^ 2 / 2 := by positivity
  have h6 : 6 * Q.size ≤ n * (n + 1) := by
    have hcast : ((6 * Q.size : ℕ) : ℚ) ≤ ((n * (n + 1) : ℕ) : ℚ) := by push_cast; linarith
    exact_mod_cast hcast
  rw [targetSize, Nat.le_div_iff_mul_le (by norm_num)]
  omega

end PaperIV.FarRounding

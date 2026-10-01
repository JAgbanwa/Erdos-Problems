import PaperIV.IntegralStability
import PaperIV.Erdos81Unconditional
import PaperIV.DefectComparatorGraph
import PaperIV.SplitEditIdentity
import PaperIV.SubgraphPadding
import PaperIV.DefectTargetArithmetic
import PaperIV.SplitBaselineTarget

/-!
# A4 transfer through a defect set: exact linear stability up to the defect–core incidences

Let `Q_s(n) = defectTarget s n = M(n+s) - C(s+1,2)` and let the defect comparator be the
project's `defSplitGraph R D H = (K_R ⊔ I_D) ∨ I_H` (`PaperIV.DefectComparatorGraph`),
with `R, D, H` a partition of the vertex set and `|D| = s`.

## Main theorem

`defect_apex_linear_stability s`: for all large `n`, every graph `G` on `Fin n` and every
set `D` of `s` vertices such that `G[V ∖ D]` is chordal, if every clique partition of `G`
of order at most four has at least `Q_s(n) - d` pieces, `0 ≤ d ≤ gammaApex · n²`, then
there is a clique `R` of `G`, disjoint from `D`, with

```text
d_E(G, (K_R ⊔ I_D) ∨ I_{V∖(R∪D)}) ≤ 16 d + 17 ρ,
ρ = |defectCoreEdges G D R| = #{edges of G from D into R ∪ D}.
```

There is **no additive constant**: at `d = 0` and `ρ = 0` the graph *is* a comparator.

## Proof

1. *Transport.*  Enumerate `V ∖ D` as `Fin n'`, `n' = n - s`, and let `H` be the induced
   graph there; it is chordal.
2. *Padding.*  A partition of `H` pushes forward to `avoidPart G D` and is padded with one
   `K₂` per edge at `D` (`SubgraphPadding`), so every order-four partition of `H` has at
   least `Q_s(n) - d - e_D` pieces, `e_D = #edges at D`.
3. *Chordal linear stability* (`IntegralStability.chordal_linear_stability_sixteen`) at
   deficit `δ = d + e_D - Q_s(n) + M(n')` (nonnegative by the chordal theorem, and at most
   `γ n'²` since `e_D ≤ s n`) gives a clique `R'` of `H` with the exact reserve
   `M(n') - B_{n'}(k) + m/16 + A/2 ≤ δ`, `k = |R'|`.
4. *Exact edge accounting.*  `d_E(G, comparator) = (m + A) + ρ + μ`, where `μ` counts the
   missing `D`–host links, and `e_D + μ = ρ + s (n' - k)`.
5. *Exact arithmetic.*  `B_{n'}(k) + s (n' - k) = B_{n+s}(k+s) - C(s+1,2) ≤ Q_s(n)`
   (`splitBaseline_add_links_le_defectTarget`).  Hence `m/16 + A/2 + μ ≤ d + ρ` and the bound.

## What this does not do

It does not bound `ρ`, and it does not produce `D`.  Both are the remaining A4 gap; see
`A4_DEFECT_APEX_STATUS.md`.  The hypothesis is on order-four partitions only (weaker than
the unrestricted `cp` hypothesis); nothing about `c₄ ≤ Q_s` is used.
-/

namespace PaperIV.DefectApexStability

open Finset
open scoped symmDiff
open PaperIV.FarRounding
open PaperIV.GraphFamilyDistance
open PaperIV.DefectComparatorGraph
open PaperIV.SplitUniformIncidence

section General

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

/-- The spanning subgraph of `G` keeping exactly the edges with no endpoint in `D`. -/
def avoidPart (G : SimpleGraph V) (D : Finset V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ x ∉ D ∧ y ∉ D
  symm := fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩
  loopless := ⟨fun _ h => h.1.ne rfl⟩

instance avoidPartDecidableRel (G : SimpleGraph V) [DecidableRel G.Adj] (D : Finset V) :
    DecidableRel (avoidPart G D).Adj := fun x y =>
  inferInstanceAs (Decidable (G.Adj x y ∧ x ∉ D ∧ y ∉ D))

omit [Fintype V] [DecidableEq V] in
theorem avoidPart_le (G : SimpleGraph V) (D : Finset V) : avoidPart G D ≤ G :=
  fun _ _ h => h.1

/-- An edge "touches" `D` when one of its endpoints lies in `D`. -/
def Touches (D : Finset V) (z : Sym2 V) : Prop := ∃ x ∈ z, x ∈ D

instance (D : Finset V) : DecidablePred (Touches D) := fun z => by
  unfold Touches; infer_instance

/-- The **defect–core incidences** of `G` relative to a defect set `D` and a core `R`:
the edges of `G` with an endpoint in `D` and both endpoints in `R ∪ D`.  These are exactly
the edges at `D` that the comparator `(K_R ⊔ I_D) ∨ I_{V∖(R∪D)}` does not have. -/
def defectCoreEdges (G : SimpleGraph V) [DecidableRel G.Adj] (D R : Finset V) :
    Finset (Sym2 V) :=
  G.edgeFinset.filter fun z => Touches D z ∧ ∀ x ∈ z, x ∈ R ∪ D

theorem sdiff_avoidPart (G : SimpleGraph V) [DecidableRel G.Adj] (D : Finset V) :
    G.edgeFinset \ (avoidPart G D).edgeFinset = G.edgeFinset.filter (Touches D) := by
  ext z
  induction z using Sym2.ind with
  | _ x y =>
    simp only [Finset.mem_sdiff, Finset.mem_filter, SimpleGraph.mem_edgeFinset,
      SimpleGraph.mem_edgeSet, Touches, Sym2.mem_iff]
    constructor
    · rintro ⟨h, hn⟩
      refine ⟨h, ?_⟩
      by_contra hc
      push_neg at hc
      exact hn ⟨h, hc x (Or.inl rfl), hc y (Or.inr rfl)⟩
    · rintro ⟨h, w, hw, hwD⟩
      refine ⟨h, fun h' => ?_⟩
      rcases hw with rfl | rfl
      · exact h'.2.1 hwD
      · exact h'.2.2 hwD

/-- At most `|D| · |V|` edges touch `D`. -/
theorem card_touch_le (G : SimpleGraph V) [DecidableRel G.Adj] (D : Finset V) :
    (G.edgeFinset.filter (Touches D)).card ≤ D.card * Fintype.card V := by
  have hsub : G.edgeFinset.filter (Touches D) ⊆
      (D ×ˢ (Finset.univ : Finset V)).image fun p => s(p.1, p.2) := by
    intro z hz
    induction z using Sym2.ind with
    | _ x y =>
      simp only [Finset.mem_filter, Touches, Sym2.mem_iff] at hz
      obtain ⟨-, w, hw, hwD⟩ := hz
      rw [Finset.mem_image]
      rcases hw with rfl | rfl
      · exact ⟨(w, y), by simp [hwD], rfl⟩
      · exact ⟨(w, x), by simp [hwD], Sym2.eq_swap⟩
  calc (G.edgeFinset.filter (Touches D)).card
      ≤ ((D ×ˢ (Finset.univ : Finset V)).image fun p => s(p.1, p.2)).card :=
        Finset.card_le_card hsub
    _ ≤ (D ×ˢ (Finset.univ : Finset V)).card := Finset.card_image_le
    _ = D.card * Fintype.card V := by rw [Finset.card_product, Finset.card_univ]

/-- **Pushing a partition forward along an induced embedding.**  If `H` is the graph induced
by `G` on the image of `e`, and the image of `e` is the complement of `D`, then every clique
partition of `H` gives one of `avoidPart G D` with the same number of pieces and the same
orders. -/
theorem exists_push_partition (G : SimpleGraph V) [DecidableRel G.Adj] (D : Finset V)
    (e : W ↪ V) (he : ∀ x, x ∉ D ↔ ∃ a, e a = x)
    (H : SimpleGraph W) [DecidableRel H.Adj] (hH : ∀ a b, H.Adj a b ↔ G.Adj (e a) (e b))
    (Q : CliquePartition H) (h4 : Q.OrderAtMost 4) :
    ∃ Q' : CliquePartition (avoidPart G D), Q'.OrderAtMost 4 ∧ Q'.size = Q.size := by
  have heD : ∀ a, e a ∉ D := fun a => (he (e a)).2 ⟨a, rfl⟩
  let phi : Finset W ↪ Finset V := ⟨Finset.map e, Finset.map_injective e⟩
  refine ⟨{ pieces := Q.pieces.map phi, isClique := ?_, two_le_card := ?_,
            edgeDisjoint := ?_, covers := ?_ }, ?_, ?_⟩
  · intro K hK a ha b hb hab
    rw [Finset.mem_map] at hK
    obtain ⟨K0, hK0, rfl⟩ := hK
    simp only [phi, Function.Embedding.coeFn_mk, Finset.mem_map] at ha hb
    obtain ⟨a0, ha0, rfl⟩ := ha
    obtain ⟨b0, hb0, rfl⟩ := hb
    have hne : a0 ≠ b0 := fun h => hab (h ▸ rfl)
    exact ⟨(hH a0 b0).1 (Q.isClique K0 hK0 a0 ha0 b0 hb0 hne), heD a0, heD b0⟩
  · intro K hK
    rw [Finset.mem_map] at hK
    obtain ⟨K0, hK0, rfl⟩ := hK
    simp only [phi, Function.Embedding.coeFn_mk, Finset.card_map]
    exact Q.two_le_card K0 hK0
  · intro K hK L hL hKL
    rw [Finset.mem_map] at hK hL
    obtain ⟨K0, hK0, rfl⟩ := hK
    obtain ⟨L0, hL0, rfl⟩ := hL
    have hne : K0 ≠ L0 := fun h => hKL (h ▸ rfl)
    have hdisj := Q.edgeDisjoint K0 hK0 L0 hL0 hne
    rw [Finset.disjoint_left] at hdisj ⊢
    intro z hzK hzL
    induction z using Sym2.ind with
    | _ x y =>
      simp only [phi, Function.Embedding.coeFn_mk, mk_mem_pairs, Finset.mem_map] at hzK hzL
      obtain ⟨⟨a0, ha0, rfl⟩, ⟨b0, hb0, rfl⟩, hxy⟩ := hzK
      obtain ⟨⟨a1, ha1, hea⟩, ⟨b1, hb1, heb⟩, -⟩ := hzL
      have h1 : a1 = a0 := e.injective hea
      have h2 : b1 = b0 := e.injective heb
      subst h1; subst h2
      have hne' : a1 ≠ b1 := fun h => hxy (h ▸ rfl)
      exact hdisj (mk_mem_pairs.2 ⟨ha0, hb0, hne'⟩) (mk_mem_pairs.2 ⟨ha1, hb1, hne'⟩)
  · ext z
    induction z using Sym2.ind with
    | _ x y =>
      simp only [Finset.mem_biUnion, Finset.mem_map, SimpleGraph.mem_edgeFinset,
        SimpleGraph.mem_edgeSet]
      constructor
      · rintro ⟨K, ⟨K0, hK0, rfl⟩, hz⟩
        simp only [phi, Function.Embedding.coeFn_mk, mk_mem_pairs, Finset.mem_map] at hz
        obtain ⟨⟨a0, ha0, rfl⟩, ⟨b0, hb0, rfl⟩, hxy⟩ := hz
        have hne : a0 ≠ b0 := fun h => hxy (h ▸ rfl)
        exact ⟨(hH a0 b0).1 (Q.isClique K0 hK0 a0 ha0 b0 hb0 hne), heD a0, heD b0⟩
      · rintro ⟨hxy, hx, hy⟩
        obtain ⟨a, rfl⟩ := (he x).1 hx
        obtain ⟨b, rfl⟩ := (he y).1 hy
        have hab : H.Adj a b := (hH a b).2 hxy
        have hmem : s(a, b) ∈ H.edgeFinset := by simpa using hab
        rw [← Q.covers, Finset.mem_biUnion] at hmem
        obtain ⟨K0, hK0, hzK⟩ := hmem
        rw [mk_mem_pairs] at hzK
        refine ⟨phi K0, ⟨K0, hK0, rfl⟩, ?_⟩
        simp only [phi, Function.Embedding.coeFn_mk, mk_mem_pairs, Finset.mem_map]
        exact ⟨⟨a, hzK.1, rfl⟩, ⟨b, hzK.2.1, rfl⟩, fun h => hzK.2.2 (e.injective h)⟩
  · intro K hK
    rw [Finset.mem_map] at hK
    obtain ⟨K0, hK0, rfl⟩ := hK
    simp only [phi, Function.Embedding.coeFn_mk, Finset.card_map]
    exact h4 K0 hK0
  · simp [CliquePartition.size]

theorem card_symmDiff_eq {α : Type*} [DecidableEq α] (A B : Finset α) :
    (A ∆ B).card = (A \ B).card + (B \ A).card := by
  rw [symmDiff_def, Finset.sup_eq_union,
    Finset.card_union_of_disjoint disjoint_sdiff_sdiff]

/-- **The part of a symmetric difference away from `D` is read inside the induced graph.** -/
theorem card_symmDiff_filter_not_touch (G C : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel C.Adj] (D : Finset V) (e : W ↪ V) (he : ∀ x, x ∉ D ↔ ∃ a, e a = x)
    (H S : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel S.Adj]
    (hH : ∀ a b, H.Adj a b ↔ G.Adj (e a) (e b))
    (hS : ∀ a b, S.Adj a b ↔ C.Adj (e a) (e b)) :
    ((G.edgeFinset ∆ C.edgeFinset).filter (fun z => ¬ Touches D z)).card =
      (H.edgeFinset ∆ S.edgeFinset).card := by
  have heD : ∀ a, e a ∉ D := fun a => (he (e a)).2 ⟨a, rfl⟩
  have hEq : (G.edgeFinset ∆ C.edgeFinset).filter (fun z => ¬ Touches D z) =
      (H.edgeFinset ∆ S.edgeFinset).map e.sym2Map := by
    ext z
    constructor
    · intro hz
      induction z using Sym2.ind with
      | _ x y =>
        simp only [Finset.mem_filter, Touches, Sym2.mem_iff] at hz
        obtain ⟨hmem, hnt⟩ := hz
        push_neg at hnt
        obtain ⟨a, rfl⟩ := (he x).1 (hnt x (Or.inl rfl))
        obtain ⟨b, rfl⟩ := (he y).1 (hnt y (Or.inr rfl))
        rw [Finset.mem_map]
        refine ⟨s(a, b), ?_, by simp⟩
        simp only [Finset.mem_symmDiff, SimpleGraph.mem_edgeFinset,
          SimpleGraph.mem_edgeSet] at hmem ⊢
        rw [hH, hS]
        exact hmem
    · intro hz
      rw [Finset.mem_map] at hz
      obtain ⟨w, hw, rfl⟩ := hz
      induction w using Sym2.ind with
      | _ a b =>
        simp only [Function.Embedding.sym2Map_apply, Sym2.map_pair_eq, Finset.mem_filter,
          Touches, Sym2.mem_iff]
        refine ⟨?_, ?_⟩
        · simp only [Finset.mem_symmDiff, SimpleGraph.mem_edgeFinset,
            SimpleGraph.mem_edgeSet] at hw ⊢
          rw [hH, hS] at hw
          exact hw
        · rintro ⟨w, hw', hwD⟩
          rcases hw' with rfl | rfl
          · exact heD a hwD
          · exact heD b hwD
  rw [hEq, Finset.card_map]

/-- The symmetric difference restricted to edges touching `D`. -/
theorem symmDiff_filter_touch (A B : Finset (Sym2 V)) (D : Finset V) :
    (A ∆ B).filter (Touches D) = (A.filter (Touches D)) ∆ (B.filter (Touches D)) := by
  ext z
  simp only [Finset.mem_filter, Finset.mem_symmDiff]
  tauto

end General

section Comparator

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Adjacency of a defective vertex in the comparator `(K_R ⊔ I_D) ∨ I_{Dᶜ ∖ R}`. -/
theorem defSplit_adj_of_mem_def {R D : Finset V} (hRD : Disjoint R D) {x y : V}
    (hx : x ∈ D) (hxy : x ≠ y) :
    (defSplitGraph R D (Dᶜ \ R)).Adj x y ↔ y ∉ R ∧ y ∉ D := by
  have hxR : x ∉ R := fun h => Finset.disjoint_left.mp hRD h hx
  rw [defSplitGraph_adj_iff]
  simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_compl]
  constructor
  · rintro ⟨-, h | h | h⟩
    · exact absurd h.1 hxR
    · exact ⟨h.2.2, h.2.1⟩
    · exact absurd hx h.1.1
  · rintro ⟨hyR, hyD⟩
    exact ⟨hxy, Or.inr (Or.inl ⟨Or.inr hx, hyD, hyR⟩)⟩

/-- The edges of `G` at `D` missing from the comparator are the defect–core incidences. -/
theorem touch_sdiff_eq_defectCoreEdges (G : SimpleGraph V) [DecidableRel G.Adj]
    {R D : Finset V} (hRD : Disjoint R D) :
    G.edgeFinset.filter (Touches D) \
        (defSplitGraph R D (Dᶜ \ R)).edgeFinset.filter (Touches D) =
      defectCoreEdges G D R := by
  ext z
  induction z using Sym2.ind with
  | _ x y =>
    simp only [defectCoreEdges, Finset.mem_sdiff, Finset.mem_filter,
      SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    constructor
    · rintro ⟨⟨hG, ht⟩, hn⟩
      refine ⟨hG, ht, ?_⟩
      have hxy : x ≠ y := hG.ne
      simp only [Touches, Sym2.mem_iff] at ht
      obtain ⟨w, hw, hwD⟩ := ht
      have hnC : ¬ (defSplitGraph R D (Dᶜ \ R)).Adj x y := fun hC =>
        hn ⟨hC, ⟨w, by rcases hw with rfl | rfl <;> simp, hwD⟩⟩
      intro v hv
      rw [Sym2.mem_iff] at hv
      rcases hw with rfl | rfl
      · rw [defSplit_adj_of_mem_def hRD hwD hxy] at hnC
        rcases hv with rfl | rfl
        · exact Finset.mem_union_right _ hwD
        · rw [Finset.mem_union]; tauto
      · rw [(defSplitGraph R D (Dᶜ \ R)).adj_comm,
          defSplit_adj_of_mem_def hRD hwD hxy.symm] at hnC
        rcases hv with rfl | rfl
        · rw [Finset.mem_union]; tauto
        · exact Finset.mem_union_right _ hwD
    · rintro ⟨hG, ht, hall⟩
      refine ⟨⟨hG, ht⟩, ?_⟩
      rintro ⟨hC, -⟩
      have hxy : x ≠ y := hG.ne
      simp only [Touches, Sym2.mem_iff] at ht
      obtain ⟨w, hw, hwD⟩ := ht
      rcases hw with rfl | rfl
      · rw [defSplit_adj_of_mem_def hRD hwD hxy] at hC
        have := hall y (Sym2.mem_mk_right _ _)
        rw [Finset.mem_union] at this
        tauto
      · rw [(defSplitGraph R D (Dᶜ \ R)).adj_comm,
          defSplit_adj_of_mem_def hRD hwD hxy.symm] at hC
        have := hall x (Sym2.mem_mk_left _ _)
        rw [Finset.mem_union] at this
        tauto

/-- The comparator edges at `D` are exactly the `|D| · |Dᶜ ∖ R|` links. -/
theorem card_comparator_touch {R D : Finset V} (hRD : Disjoint R D) :
    ((defSplitGraph R D (Dᶜ \ R)).edgeFinset.filter (Touches D)).card =
      D.card * (Dᶜ \ R).card := by
  have hDH : Disjoint D (Dᶜ \ R) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    exact (Finset.mem_compl.mp (Finset.mem_sdiff.mp hx').1) hx
  rw [← PaperIV.SplitEdgeCount.card_crossEdges hDH]
  congr 1
  ext z
  induction z using Sym2.ind with
  | _ x y =>
    simp only [Finset.mem_filter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
      PaperIV.SplitEdgeCount.mem_crossEdges]
    constructor
    · rintro ⟨hC, ht⟩
      have hxy : x ≠ y := hC.ne
      simp only [Touches, Sym2.mem_iff] at ht
      obtain ⟨w, hw, hwD⟩ := ht
      rcases hw with rfl | rfl
      · rw [defSplit_adj_of_mem_def hRD hwD hxy] at hC
        exact ⟨w, hwD, y, by simp [hC.1, hC.2], rfl⟩
      · rw [(defSplitGraph R D (Dᶜ \ R)).adj_comm,
          defSplit_adj_of_mem_def hRD hwD hxy.symm] at hC
        exact ⟨w, hwD, x, by simp [hC.1, hC.2], Sym2.eq_swap⟩
    · rintro ⟨a, ha, b, hb, hab⟩
      have hne : a ≠ b := fun h => (Finset.disjoint_left.mp hDH ha) (h ▸ hb)
      have hadj : (defSplitGraph R D (Dᶜ \ R)).Adj a b := by
        rw [defSplit_adj_of_mem_def hRD ha hne]
        simp only [Finset.mem_sdiff, Finset.mem_compl] at hb
        exact ⟨hb.2, hb.1⟩
      rw [Sym2.eq_iff] at hab
      rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨hadj, ⟨x, Sym2.mem_mk_left _ _, ha⟩⟩
      · exact ⟨hadj.symm, ⟨y, Sym2.mem_mk_right _ _, ha⟩⟩

end Comparator

section Arithmetic

open PaperIV.DefectTargetArithmetic

theorem farRounding_targetSize_eq (m : ℕ) :
    PaperIV.FarRounding.targetSize m = PaperIV.targetSize m := rfl

theorem targetSize_mono {a b : ℕ} (h : a ≤ b) : PaperIV.targetSize a ≤ PaperIV.targetSize b := by
  unfold PaperIV.targetSize
  exact Nat.div_le_div_right (Nat.mul_le_mul h (Nat.add_le_add_right h 1))

/-- **The comparator value never exceeds the defect target.**  With `n' = n - s` hosts-and-core
vertices, core size `k` and `s` defective vertices joined to the `n' - k` hosts,
`B_{n'}(k) + s (n' - k) = B_{n+s}(k+s) - C(s+1,2) ≤ Q_s(n)`. -/
theorem splitBaseline_add_links_le_defectTarget {n s : ℕ} (hs : s ≤ n) (k : ℕ) :
    PaperIV.splitBaseline ((n - s : ℕ) : ℚ) (k : ℚ) + (s : ℚ) * (((n - s : ℕ) : ℚ) - k) ≤
      (defectTarget s n : ℚ) := by
  have hcast : ((n - s : ℕ) : ℚ) = (n : ℚ) - s := by rw [Nat.cast_sub hs]
  -- the shifted split value is an integer bounded by `M(n+s)`
  set S : ℤ := ((k + s : ℕ) : ℤ) * (((n + s : ℕ) : ℤ) - ((k + s : ℕ) : ℤ)) -
    (((k + s).choose 2 : ℕ) : ℤ) with hSdef
  have hS : (S : ℚ) = PaperIV.splitBaseline ((n + s : ℕ) : ℚ) ((k + s : ℕ) : ℚ) := by
    rw [hSdef, PaperIV.splitBaseline]
    push_cast
    rw [Nat.cast_choose_two]
    push_cast
    ring
  have hle := PaperIV.SplitBaselineTarget.splitBaseline_le_targetSize hS
  have hleQ : (S : ℚ) ≤ (PaperIV.targetSize (n + s) : ℚ) := by exact_mod_cast hle
  -- the truncated subtraction in `defectTarget` only helps
  have hdt : (PaperIV.targetSize (n + s) : ℚ) - ((s + 1).choose 2 : ℕ) ≤
      (defectTarget s n : ℚ) := by
    unfold defectTarget
    rw [farRounding_targetSize_eq]
    by_cases hc : (s + 1).choose 2 ≤ PaperIV.targetSize (n + s)
    · rw [Nat.cast_sub hc]
    · push_neg at hc
      have : ((PaperIV.targetSize (n + s) : ℕ) : ℚ) < (((s + 1).choose 2 : ℕ) : ℚ) := by
        exact_mod_cast hc
      have h0 : (0 : ℚ) ≤ ((PaperIV.targetSize (n + s) - (s + 1).choose 2 : ℕ) : ℚ) := by
        positivity
      linarith
  have hchoose : (((s + 1).choose 2 : ℕ) : ℚ) = ((s : ℚ) + 1) * s / 2 := by
    rw [Nat.cast_choose_two]; push_cast; ring
  rw [hchoose] at hdt
  rw [hS] at hleQ
  have hid : PaperIV.splitBaseline ((n - s : ℕ) : ℚ) (k : ℚ) +
      (s : ℚ) * (((n - s : ℕ) : ℚ) - k) =
      PaperIV.splitBaseline ((n + s : ℕ) : ℚ) ((k + s : ℕ) : ℚ) - ((s : ℚ) + 1) * s / 2 := by
    rw [hcast, PaperIV.splitBaseline, PaperIV.splitBaseline]
    push_cast
    ring
  rw [hid]
  linarith

end Arithmetic

section Main

open PaperIV.DefectTargetArithmetic

/-- The admissible deficit window of the transfer theorem: one eighth of the chordal
stability constant `IntegralStability.gamma`. -/
def gammaApex : ℚ := PaperIV.IntegralStability.gamma / 8

theorem gammaApex_pos : 0 < gammaApex := by
  unfold gammaApex; linarith [PaperIV.IntegralStability.gamma_pos]

/-- **A4 through a defect set (exact, linear, no additive loss).**

Fix `s`.  For all large `n`, let `G` be any graph on `Fin n` and `D` a set of `s` vertices
such that the graph induced on `V ∖ D` is chordal.  If every clique partition of `G` with
pieces of order at most four has at least `Q_s(n) - d` pieces, with
`0 ≤ d ≤ gammaApex · n²`, then there is a clique `R` of `G`, disjoint from `D`, such that
the edit distance from `G` to the defect comparator `(K_R ⊔ I_D) ∨ I_{V∖(R∪D)}` is at most
`16 d + 17 ρ`, where `ρ = |defectCoreEdges G D R|` counts the edges of `G` from `D` into
`R ∪ D`. -/
theorem defect_apex_linear_stability (s : ℕ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (D : Finset (Fin n)), D.card = s →
      (G.induce ((Dᶜ : Finset (Fin n)) : Set (Fin n))).IsChordal →
      ∀ d : ℚ, 0 ≤ d → d ≤ gammaApex * (n : ℚ) ^ 2 →
      (∀ P : CliquePartition G, P.OrderAtMost 4 →
          (defectTarget s n : ℚ) - d ≤ (P.size : ℚ)) →
      ∃ R : Finset (Fin n), Disjoint R D ∧ G.IsClique (R : Set (Fin n)) ∧ 2 ≤ R.card ∧
        (PaperIV.EditMetric.editDist G.edgeFinset
            (graphEdgeSupport (defSplitGraph R D (Dᶜ \ R))) : ℚ) ≤
          16 * d + 17 * ((defectCoreEdges G D R).card : ℚ) := by
  classical
  obtain ⟨Nst, hst⟩ := PaperIV.IntegralStability.chordal_linear_stability_sixteen
  obtain ⟨N81, h81⟩ := PaperIV.Erdos81Unconditional.erdos81_cliquePartition
  refine ⟨Nst + N81 + 2 * s + ⌈8 * (s : ℚ) / PaperIV.IntegralStability.gamma⌉₊ + 1, ?_⟩
  intro n hn G _ D hDs hch d hd0 hdle hyp
  have hgam := PaperIV.IntegralStability.gamma_pos
  set n' := (Dᶜ).card with hn'
  have hn'eq : n' = n - s := by rw [hn', Finset.card_compl, Fintype.card_fin, hDs]
  have hsn : 2 * s + 1 ≤ n := by omega
  have hn'st : Nst ≤ n' := by omega
  have hn'81 : N81 ≤ n' := by omega
  -- the enumeration of `V ∖ D`
  let e : Fin n' ↪ Fin n := ((Dᶜ).orderEmbOfFin hn'.symm).toEmbedding
  have he : ∀ x, x ∉ D ↔ ∃ a, e a = x := by
    intro x
    have hr := Finset.range_orderEmbOfFin (Dᶜ) hn'.symm
    constructor
    · intro hx
      have hx' : x ∈ Set.range ((Dᶜ).orderEmbOfFin hn'.symm) := by
        rw [hr]; simpa using hx
      obtain ⟨a, ha⟩ := hx'
      exact ⟨a, ha⟩
    · rintro ⟨a, rfl⟩
      exact Finset.mem_compl.mp (Finset.orderEmbOfFin_mem (Dᶜ) hn'.symm a)
  have heD : ∀ a, e a ∉ D := fun a => (he (e a)).2 ⟨a, rfl⟩
  -- the induced chordal graph on `Fin n'`
  let H : SimpleGraph (Fin n') := G.comap e
  haveI : DecidableRel H.Adj := fun a b => inferInstanceAs (Decidable (G.Adj (e a) (e b)))
  have hH : ∀ a b, H.Adj a b ↔ G.Adj (e a) (e b) := fun a b => Iff.rfl
  have hHch : PaperIV.FarRounding.IsChordal H := by
    let f' : Fin n' ↪ ((Dᶜ : Finset (Fin n)) : Set (Fin n)) :=
      ⟨fun a => ⟨e a, by simpa using heD a⟩,
        fun a b h => e.injective (congrArg Subtype.val h)⟩
    exact hch.comap f' H (fun a b => Iff.rfl)
  -- the edges at `D`
  set eD := (G.edgeFinset.filter (Touches D)).card with heDdef
  have heDle : (eD : ℚ) ≤ (s : ℚ) * n := by
    have h := card_touch_le G D
    rw [hDs, Fintype.card_fin] at h
    exact_mod_cast h
  -- extension of partitions of `H` to partitions of `G`
  have hext : ∀ Q : CliquePartition H, Q.OrderAtMost 4 →
      (defectTarget s n : ℚ) - d - eD ≤ (Q.size : ℚ) := by
    intro Q hQ
    obtain ⟨Q0, hQ04, hQ0s⟩ := exists_push_partition G D e he H hH Q hQ
    obtain ⟨P, hP4, hPs⟩ := PaperIV.SubgraphPadding.exists_cliquePartition_of_subgraph
      G (avoidPart G D) (avoidPart_le G D) Q0 hQ04
    rw [sdiff_avoidPart] at hPs
    have h1 := hyp P hP4
    have h2 : (P.size : ℚ) ≤ (Q0.size : ℚ) + eD := by exact_mod_cast hPs
    rw [hQ0s] at h2
    linarith
  -- the targets
  have hTn' : PaperIV.targetSize n' ≤ defectTarget s n := by
    have h1 := targetSize_mono (show n' ≤ n by omega)
    have h2 := targetSize_le_defectTarget s n (by omega)
    rw [farRounding_targetSize_eq] at h2
    omega
  have hTn'Q : (PaperIV.targetSize n' : ℚ) ≤ (defectTarget s n : ℚ) := by exact_mod_cast hTn'
  -- the chordal deficit
  set δ : ℚ := d + eD - defectTarget s n + PaperIV.targetSize n' with hδdef
  have hδ0 : 0 ≤ δ := by
    obtain ⟨Q0, hQ04, hQ0s⟩ := h81 n' hn'81 H hHch
    have h1 := hext Q0 hQ04
    have h2 : (Q0.size : ℚ) ≤ (PaperIV.targetSize n' : ℚ) := by
      rw [← farRounding_targetSize_eq]; exact_mod_cast hQ0s
    linarith
  have hceil : 8 * (s : ℚ) ≤ PaperIV.IntegralStability.gamma * n := by
    have h1 : 8 * (s : ℚ) / PaperIV.IntegralStability.gamma ≤
        (⌈8 * (s : ℚ) / PaperIV.IntegralStability.gamma⌉₊ : ℚ) := Nat.le_ceil _
    have h2 : (⌈8 * (s : ℚ) / PaperIV.IntegralStability.gamma⌉₊ : ℚ) ≤ (n : ℚ) := by
      exact_mod_cast (show ⌈8 * (s : ℚ) / PaperIV.IntegralStability.gamma⌉₊ ≤ n by omega)
    rw [div_le_iff₀ hgam] at h1
    nlinarith
  have hn'Q : (n' : ℚ) = (n : ℚ) - s := by rw [hn'eq, Nat.cast_sub (by omega)]
  have hsnQ : 2 * (s : ℚ) ≤ n := by exact_mod_cast (show 2 * s ≤ n by omega)
  have hδle : δ ≤ PaperIV.IntegralStability.gamma * (n' : ℚ) ^ 2 := by
    have hA : δ ≤ d + (s : ℚ) * n := by rw [hδdef]; linarith
    have hB : (n : ℚ) ^ 2 / 4 ≤ (n' : ℚ) ^ 2 := by
      rw [hn'Q]; nlinarith
    have hC : (s : ℚ) * n ≤ PaperIV.IntegralStability.gamma * (n : ℚ) ^ 2 / 8 := by
      have hn0 : (0 : ℚ) ≤ n := by positivity
      nlinarith
    have hD : d ≤ PaperIV.IntegralStability.gamma * (n : ℚ) ^ 2 / 8 := by
      unfold gammaApex at hdle; linarith
    nlinarith
  -- chordal linear stability on the induced graph
  obtain ⟨R', hR'cl, hR'2, -, -, -, hres, -⟩ :=
    hst n' hn'st H hHch δ hδ0 hδle (fun Q hQ => by have := hext Q hQ; linarith)
  set R : Finset (Fin n) := R'.map e with hRdef
  have hRD : Disjoint R D := by
    rw [Finset.disjoint_left]
    intro x hx
    rw [hRdef, Finset.mem_map] at hx
    obtain ⟨a, -, rfl⟩ := hx
    exact heD a
  have hRcl : G.IsClique (R : Set (Fin n)) := by
    intro x hx y hy hxy
    rw [Finset.mem_coe, hRdef, Finset.mem_map] at hx hy
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    exact (hH a b).1 (hR'cl ha hb (fun h => hxy (h ▸ rfl)))
  have hRcard : R.card = R'.card := Finset.card_map _
  refine ⟨R, hRD, hRcl, by rw [hRcard]; exact hR'2, ?_⟩
  -- the comparator and its trace on `V ∖ D`
  set C := defSplitGraph R D (Dᶜ \ R) with hCdef
  let S' : SimpleGraph (Fin n') := splitGraph R' (Finset.univ \ R')
  have hS : ∀ a b, S'.Adj a b ↔ C.Adj (e a) (e b) := by
    intro a b
    have h1 : ∀ c, e c ∈ R ↔ c ∈ R' := fun c => by rw [hRdef, Finset.mem_map' e]
    have h2 : ∀ c, e c ∈ R ∪ D ↔ c ∈ R' := fun c => by
      rw [Finset.mem_union, h1]; exact ⟨fun h => h.resolve_right (heD c), Or.inl⟩
    have h3 : ∀ c, e c ∈ Dᶜ \ R ↔ c ∈ Finset.univ \ R' := fun c => by
      rw [Finset.mem_sdiff, Finset.mem_sdiff, Finset.mem_compl, h1]
      exact ⟨fun h => ⟨Finset.mem_univ _, h.2⟩, fun h => ⟨heD c, h.2⟩⟩
    have h4 : e a ≠ e b ↔ a ≠ b := e.injective.ne_iff
    show (splitGraph R' (Finset.univ \ R')).Adj a b ↔
      (defSplitGraph R D (Dᶜ \ R)).Adj (e a) (e b)
    rw [splitGraph_adj_iff, defSplitGraph_adj_iff, h4, h1, h1, h2, h2, h3, h3]
  have hinside := card_symmDiff_filter_not_touch G C D e he H S' hH hS
  have hsplit := PaperIV.SplitEditIdentity.editDist_split_eq H hR'cl
  rw [graphEdgeSupport_eq_edgeFinset] at hsplit
  -- the edges at `D`
  set T := G.edgeFinset.filter (Touches D) with hTdef
  set CT := C.edgeFinset.filter (Touches D) with hCTdef
  have hrho : (T \ CT).card = (defectCoreEdges G D R).card := by
    rw [hTdef, hCTdef, touch_sdiff_eq_defectCoreEdges G hRD]
  have hCTcard : CT.card = s * (n' - R'.card) := by
    rw [hCTdef, card_comparator_touch hRD, hDs, Finset.card_sdiff_of_subset, hRcard]
    intro x hx
    rw [hRdef, Finset.mem_map] at hx
    obtain ⟨a, -, rfl⟩ := hx
    exact Finset.mem_compl.mpr (heD a)
  have hbal : T.card + (CT \ T).card = (T \ CT).card + CT.card := by
    have h1 := Finset.card_sdiff_add_card T CT
    have h2 := Finset.card_sdiff_add_card CT T
    rw [Finset.union_comm] at h2
    omega
  have hdist : PaperIV.EditMetric.editDist G.edgeFinset (graphEdgeSupport C) =
      (T \ CT).card + (CT \ T).card +
        ((PaperIV.RootVocab.outsideEdges H R').card +
          PaperIV.RootVocab.missingIncidences H R') := by
    rw [graphEdgeSupport_eq_edgeFinset, PaperIV.EditMetric.editDist,
      ← Finset.card_filter_add_card_filter_not (p := Touches D), symmDiff_filter_touch,
      card_symmDiff_eq, hinside, ← hsplit, PaperIV.EditMetric.editDist]
  -- the final ledger
  have hk : R'.card ≤ n' := by
    have := Finset.card_le_univ R'
    simpa using this
  have hval := splitBaseline_add_links_le_defectTarget (n := n) (s := s) (by omega) R'.card
  rw [← hn'eq] at hval
  have hbalQ : (T.card : ℚ) + ((CT \ T).card : ℚ) =
      ((T \ CT).card : ℚ) + (s : ℚ) * ((n' : ℚ) - R'.card) := by
    have := hbal
    rw [hCTcard] at this
    have h' : ((T.card + (CT \ T).card : ℕ) : ℚ) =
        (((T \ CT).card + s * (n' - R'.card) : ℕ) : ℚ) := by rw [this]
    push_cast [Nat.cast_sub hk] at h'
    linarith
  rw [hdist]
  rw [← hrho]
  push_cast
  have hm0 : (0 : ℚ) ≤ ((PaperIV.RootVocab.outsideEdges H R').card : ℚ) := Nat.cast_nonneg _
  have hA0 : (0 : ℚ) ≤ (PaperIV.RootVocab.missingIncidences H R' : ℚ) := Nat.cast_nonneg _
  have hmu0 : (0 : ℚ) ≤ ((CT \ T).card : ℚ) := Nat.cast_nonneg _
  have heDT : (eD : ℚ) = (T.card : ℚ) := rfl
  linarith

end Main

end PaperIV.DefectApexStability

import PaperIV.FarRounding
import PaperIV.RootEdgeSplit
import PaperIV.SplitCompleteRigidity

/-!
# E4, part A — lifted pieces pay the outside edges

Fix a clique `A` (the localized root) of a graph `G` on a finite vertex type with
`n = |V|` vertices; write `a = |A|`, `Z = V \ A`, `D = missingIncidences G A` and
`m = |outsideEdges G A|`.

A **lifted piece** is `{u, v, x, y}` with `u ≠ v` in `A`, `xy` an outside edge and the
four cross adjacencies present.  It is a `K₄` of `G` (`liftedPiece_isItem`) covering one
core pair, four links and one outside edge, with gain `5`.  A **hosted triangle** is
`{u, v, z}` with `z ∈ Z`, gain `2`.

## Main results

* `disjoint_pairs_iff` : two vertex sets are edge-disjoint iff they share at most one
  vertex.  This is the compatibility test between lifted pieces and hosted triangles
  (the analogue of `hostedTri_inter_exterior`, which is `pairs_hostedTri_inter_outside`
  here, together with `pairs_liftedPiece_inter_outside`).
* `ledger` : for **any** physical packing `P` whose pieces are hosted triangles, lifted
  pieces or exterior triangles `{u, x, y}` and which covers every core pair, its
  completion `Q` satisfies the exact identity
  `|Q| + C(a,2) + 2·oc(P) + ℓ(P) + D = m + a·(n − a)`,
  where `oc` is the number of outside edges covered and `ℓ` the number of lifted pieces.
* `size_add_eq_baseline_of_all_lifted` / `size_le_targetSize_of_all_lifted` :
  **the budget chain of part A**: if the pieces are hosted triangles and lifted pieces
  only and every outside edge is lifted, then `|Q| + D + 2m = splitBaseline(n, a)`, hence
  `|Q| ≤ M(n) = targetSize n`, with slack `D + 2m`.
* `size_le_targetSize_of_ledger` : the general closing condition `m ≤ D + 2·oc + ℓ`.
* `outsideDegree_le_coreDegree`, `two_mul_outsideDegree_le_coreDegree` : the **exact
  obstruction** to lifting all outside edges: at every exterior vertex `x`, the lifted
  outside edges at `x` use two private links each, so full lifting forces
  `2·deg_Z(x) ≤ |N(x) ∩ A|`.  A localized root does *not* control `deg_Z(x)` per vertex
  (a star inside `Z` has `m = O(n)` but one vertex of degree `≈ 2a`), so full lifting is
  not always possible; exterior triangles `{u,x,y}` weaken the requirement to
  `deg_Z(x) ≤ |N(x) ∩ A|` and still pay `2` per covered outside edge.
-/

namespace PaperIV.LiftedPieces

open Finset PaperIV.FarRounding PaperIV.RootVocab

variable {V : Type*} [DecidableEq V]

/-! ## 1. Edge supports -/

lemma pairs_inter (K L : Finset V) : pairs K ∩ pairs L = pairs (K ∩ L) := by
  ext e
  induction e using Sym2.ind with
  | _ a b =>
    simp only [Finset.mem_inter, mk_mem_pairs]
    tauto

/-- **Compatibility test.**  Two vertex sets have edge-disjoint supports iff they share
at most one vertex. -/
theorem disjoint_pairs_iff (K L : Finset V) :
    Disjoint (pairs K) (pairs L) ↔ (K ∩ L).card ≤ 1 := by
  rw [Finset.disjoint_iff_inter_eq_empty, pairs_inter, ← Finset.card_eq_zero, card_pairs,
    Nat.choose_eq_zero_iff]
  omega

/-! ## 2. The pieces -/

/-- The lifted piece `{u, v, x, y}`: a core pair `uv` together with an outside edge `xy`. -/
def liftedPiece (u v x y : V) : Finset V := {u, v, x, y}

/-- The hosted triangle `{u, v, z}`: a core pair `uv` hosted at the exterior vertex `z`. -/
def hostedTri (u v z : V) : Finset V := {u, v, z}

section Pieces

variable {G : SimpleGraph V} {A : Finset V}

/-- **The lifted piece is a `K₄` of `G`.** -/
theorem liftedPiece_isItem (hA : G.IsClique (A : Set V)) {u v x y : V}
    (hu : u ∈ A) (hv : v ∈ A) (huv : u ≠ v) (hx : x ∉ A) (hy : y ∉ A)
    (hxy : G.Adj x y) (hux : G.Adj u x) (huy : G.Adj u y) (hvx : G.Adj v x)
    (hvy : G.Adj v y) :
    IsItem G (liftedPiece u v x y) ∧ (liftedPiece u v x y).card = 4 := by
  have hux' : u ≠ x := fun h => hx (h ▸ hu)
  have huy' : u ≠ y := fun h => hy (h ▸ hu)
  have hvx' : v ≠ x := fun h => hx (h ▸ hv)
  have hvy' : v ≠ y := fun h => hy (h ▸ hv)
  have hxy' : x ≠ y := G.ne_of_adj hxy
  have huvG : G.Adj u v := hA (mem_coe.2 hu) (mem_coe.2 hv) huv
  have hcard : (liftedPiece u v x y).card = 4 := by
    unfold liftedPiece
    rw [card_insert_of_notMem (by simp [huv, hux', huy']),
      card_insert_of_notMem (by simp [hvx', hvy']),
      card_insert_of_notMem (by simp [hxy']), card_singleton]
  refine ⟨⟨?_, Or.inr hcard⟩, hcard⟩
  intro p hp q hq hpq
  simp only [liftedPiece, mem_insert, mem_singleton] at hp hq
  rcases hp with rfl | rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl hpq
    | assumption
    | exact G.symm ‹_›

/-- **The hosted triangle is a `K₃` of `G`.** -/
theorem hostedTri_isItem (hA : G.IsClique (A : Set V)) {u v z : V}
    (hu : u ∈ A) (hv : v ∈ A) (huv : u ≠ v) (hz : z ∉ A)
    (huz : G.Adj u z) (hvz : G.Adj v z) :
    IsItem G (hostedTri u v z) ∧ (hostedTri u v z).card = 3 := by
  have huz' : u ≠ z := fun h => hz (h ▸ hu)
  have hvz' : v ≠ z := fun h => hz (h ▸ hv)
  have huvG : G.Adj u v := hA (mem_coe.2 hu) (mem_coe.2 hv) huv
  have hcard : (hostedTri u v z).card = 3 := by
    unfold hostedTri
    rw [card_insert_of_notMem (by simp [huv, huz']),
      card_insert_of_notMem (by simp [hvz']), card_singleton]
  refine ⟨⟨?_, Or.inl hcard⟩, hcard⟩
  intro p hp q hq hpq
  simp only [hostedTri, mem_insert, mem_singleton] at hp hq
  rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl <;>
    first
    | exact absurd rfl hpq
    | assumption
    | exact G.symm ‹_›

theorem liftedPiece_inter_core {u v x y : V} (hu : u ∈ A) (hv : v ∈ A)
    (hx : x ∉ A) (hy : y ∉ A) : liftedPiece u v x y ∩ A = {u, v} := by
  ext w
  simp only [liftedPiece, mem_inter, mem_insert, mem_singleton]
  constructor
  · rintro ⟨rfl | rfl | rfl | rfl, hw⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact absurd hw hx
    · exact absurd hw hy
  · rintro (rfl | rfl)
    · exact ⟨Or.inl rfl, hu⟩
    · exact ⟨Or.inr (Or.inl rfl), hv⟩

theorem liftedPiece_sdiff_core {u v x y : V} (hu : u ∈ A) (hv : v ∈ A)
    (hx : x ∉ A) (hy : y ∉ A) : liftedPiece u v x y \ A = {x, y} := by
  ext w
  simp only [liftedPiece, mem_sdiff, mem_insert, mem_singleton]
  constructor
  · rintro ⟨rfl | rfl | rfl | rfl, hw⟩
    · exact absurd hu hw
    · exact absurd hv hw
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨Or.inr (Or.inr (Or.inl rfl)), hx⟩
    · exact ⟨Or.inr (Or.inr (Or.inr rfl)), hy⟩

theorem hostedTri_inter_core {u v z : V} (hu : u ∈ A) (hv : v ∈ A) (hz : z ∉ A) :
    hostedTri u v z ∩ A = {u, v} := by
  ext w
  simp only [hostedTri, mem_inter, mem_insert, mem_singleton]
  constructor
  · rintro ⟨rfl | rfl | rfl, hw⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact absurd hw hz
  · rintro (rfl | rfl)
    · exact ⟨Or.inl rfl, hu⟩
    · exact ⟨Or.inr (Or.inl rfl), hv⟩

theorem hostedTri_sdiff_core {u v z : V} (hu : u ∈ A) (hv : v ∈ A) (hz : z ∉ A) :
    hostedTri u v z \ A = {z} := by
  ext w
  simp only [hostedTri, mem_sdiff, mem_insert, mem_singleton]
  constructor
  · rintro ⟨rfl | rfl | rfl, hw⟩
    · exact absurd hu hw
    · exact absurd hv hw
    · rfl
  · rintro rfl
    exact ⟨Or.inr (Or.inr rfl), hz⟩

end Pieces

/-! ## 3. Outside edges and core pairs seen by a piece -/

section Supports

variable [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj] {A : Finset V}

/-- The core pairs covered by a real clique `K` are exactly the pairs of `K ∩ A`. -/
theorem pairs_inter_rootEdges {K : Finset V} (hK : pairs K ⊆ G.edgeFinset) :
    pairs K ∩ rootEdges G A = pairs (K ∩ A) := by
  ext e
  induction e using Sym2.ind with
  | _ a b =>
    simp only [rootEdges, Finset.mem_inter, Finset.mem_filter, mk_mem_pairs,
      Sym2.toFinset_mk_eq, Finset.insert_subset_iff, Finset.singleton_subset_iff]
    constructor
    · rintro ⟨⟨ha, hb, hab⟩, -, haA, hbA⟩
      exact ⟨⟨ha, haA⟩, ⟨hb, hbA⟩, hab⟩
    · rintro ⟨⟨ha, haA⟩, ⟨hb, hbA⟩, hab⟩
      exact ⟨⟨ha, hb, hab⟩, hK (mk_mem_pairs.2 ⟨ha, hb, hab⟩), haA, hbA⟩

/-- The outside edges covered by a real clique `K` are exactly the pairs of `K \ A`. -/
theorem pairs_inter_outsideEdges {K : Finset V} (hK : pairs K ⊆ G.edgeFinset) :
    pairs K ∩ outsideEdges G A = pairs (K \ A) := by
  ext e
  induction e using Sym2.ind with
  | _ a b =>
    simp only [outsideEdges, Finset.mem_inter, Finset.mem_filter, mk_mem_pairs,
      Sym2.toFinset_mk_eq, Finset.insert_subset_iff, Finset.singleton_subset_iff,
      mem_outsideVertices, Finset.mem_sdiff]
    constructor
    · rintro ⟨⟨ha, hb, hab⟩, -, haA, hbA⟩
      exact ⟨⟨ha, haA⟩, ⟨hb, hbA⟩, hab⟩
    · rintro ⟨⟨ha, haA⟩, ⟨hb, hbA⟩, hab⟩
      exact ⟨⟨ha, hb, hab⟩, hK (mk_mem_pairs.2 ⟨ha, hb, hab⟩), haA, hbA⟩

/-- **Analogue of `hostedTri_inter_exterior`.**  A hosted triangle covers no outside edge. -/
theorem pairs_hostedTri_inter_outside {u v z : V} (hu : u ∈ A) (hv : v ∈ A) (hz : z ∉ A)
    (hK : pairs (hostedTri u v z) ⊆ G.edgeFinset) :
    pairs (hostedTri u v z) ∩ outsideEdges G A = ∅ := by
  rw [pairs_inter_outsideEdges hK, hostedTri_sdiff_core hu hv hz, ← card_eq_zero, card_pairs]
  simp

/-- A lifted piece covers exactly one outside edge, namely `xy`. -/
theorem pairs_liftedPiece_inter_outside {u v x y : V} (hu : u ∈ A) (hv : v ∈ A)
    (hx : x ∉ A) (hy : y ∉ A) (hxy : x ≠ y)
    (hK : pairs (liftedPiece u v x y) ⊆ G.edgeFinset) :
    pairs (liftedPiece u v x y) ∩ outsideEdges G A = {s(x, y)} := by
  rw [pairs_inter_outsideEdges hK, liftedPiece_sdiff_core hu hv hx hy]
  have : ¬ (s(x, y)).IsDiag := by simpa using hxy
  simpa [Sym2.toFinset_mk_eq] using pairs_toFinset this

end Supports

/-! ## 4. The ledger -/

section Ledger

variable [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj] {A : Finset V}

/-- The three admissible piece types, by `(|K ∩ A|, |K \ A|)`:
hosted triangle `(2,1)`, lifted piece `(2,2)`, exterior triangle `(1,2)`. -/
def AdmissibleType (A K : Finset V) : Prop :=
  ((K ∩ A).card = 2 ∧ ((K \ A).card = 1 ∨ (K \ A).card = 2)) ∨
    ((K ∩ A).card = 1 ∧ (K \ A).card = 2)

/-- Number of lifted pieces (type `(2,2)`) of a packing. -/
def liftCount (A : Finset V) (P : Packing G) : ℕ :=
  (P.pieces.filter fun K => (K ∩ A).card = 2 ∧ (K \ A).card = 2).card

/-- Number of outside edges covered by a packing, counted piece by piece. -/
def outsideCovered (A : Finset V) (P : Packing G) : ℕ :=
  ∑ K ∈ P.pieces, ((K \ A).card).choose 2

omit [Fintype V] in
/-- The gain of an admissible piece: `2·C(|K∩A|,2) + 2·C(|K\A|,2) + [lifted]`. -/
theorem gainOf_of_admissible {K : Finset V} (hK : AdmissibleType A K) :
    gainOf K = 2 * ((K ∩ A).card).choose 2 + 2 * ((K \ A).card).choose 2 +
      (if (K ∩ A).card = 2 ∧ (K \ A).card = 2 then 1 else 0) := by
  have hsplit : (K ∩ A).card + (K \ A).card = K.card := card_inter_add_card_sdiff K A
  unfold gainOf
  rcases hK with ⟨h1, h2 | h2⟩ | ⟨h1, h2⟩ <;> rw [← hsplit, h1, h2] <;> decide

/-- Covering every core pair: the core pairs are shared out among the pieces. -/
theorem sum_choose_inter_eq (P : Packing G) (hcov : rootEdges G A ⊆ P.pieces.biUnion pairs) :
    ∑ K ∈ P.pieces, ((K ∩ A).card).choose 2 = (rootEdges G A).card := by
  have hsub : ∀ K ∈ P.pieces, pairs K ⊆ G.edgeFinset := fun K hK =>
    pairs_subset_edgeFinset (P.isItem K hK)
  have heq : rootEdges G A = P.pieces.biUnion (fun K => pairs K ∩ rootEdges G A) := by
    ext e
    simp only [Finset.mem_biUnion, Finset.mem_inter]
    constructor
    · intro he
      obtain ⟨K, hK, heK⟩ := Finset.mem_biUnion.1 (hcov he)
      exact ⟨K, hK, heK, he⟩
    · rintro ⟨K, -, -, he⟩
      exact he
  have hdisj : (↑P.pieces : Set (Finset V)).PairwiseDisjoint
      (fun K => pairs K ∩ rootEdges G A) := by
    intro K hK L hL hKL
    exact Disjoint.mono inter_subset_left inter_subset_left
      (P.edgeDisjoint K (by simpa using hK) L (by simpa using hL) hKL)
  rw [heq, card_biUnion hdisj]
  refine sum_congr rfl fun K hK => ?_
  rw [pairs_inter_rootEdges (hsub K hK), card_pairs]

/-- The outside edges covered by the pieces are distinct outside edges. -/
theorem outsideCovered_le (P : Packing G) :
    outsideCovered A P ≤ (outsideEdges G A).card := by
  have hsub : ∀ K ∈ P.pieces, pairs K ⊆ G.edgeFinset := fun K hK =>
    pairs_subset_edgeFinset (P.isItem K hK)
  have hdisj : (↑P.pieces : Set (Finset V)).PairwiseDisjoint
      (fun K => pairs K ∩ outsideEdges G A) := by
    intro K hK L hL hKL
    exact Disjoint.mono inter_subset_left inter_subset_left
      (P.edgeDisjoint K (by simpa using hK) L (by simpa using hL) hKL)
  have hle : (P.pieces.biUnion (fun K => pairs K ∩ outsideEdges G A)).card ≤
      (outsideEdges G A).card := by
    apply card_le_card
    intro e he
    obtain ⟨K, -, he⟩ := Finset.mem_biUnion.1 he
    exact (Finset.mem_inter.1 he).2
  rw [card_biUnion hdisj] at hle
  unfold outsideCovered
  calc ∑ K ∈ P.pieces, ((K \ A).card).choose 2
      = ∑ K ∈ P.pieces, (pairs K ∩ outsideEdges G A).card := by
        refine sum_congr rfl fun K hK => ?_
        rw [pairs_inter_outsideEdges (hsub K hK), card_pairs]
    _ ≤ _ := hle

/-- **The exact ledger.**  For a packing of admissible pieces covering every core pair of
the clique `A`, the completion `Q` (one `K₂` per uncovered edge) satisfies
`|Q| + C(a,2) + 2·oc + ℓ + D = m + a·(n − a)`. -/
theorem ledger (hA : G.IsClique (A : Set V)) (P : Packing G)
    (htype : ∀ K ∈ P.pieces, AdmissibleType A K)
    (hcov : rootEdges G A ⊆ P.pieces.biUnion pairs) :
    ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧
      Q.size + A.card.choose 2 + 2 * outsideCovered A P + liftCount A P +
          missingIncidences G A =
        (outsideEdges G A).card + A.card * (Fintype.card V - A.card) := by
  obtain ⟨Q, hQ4, hQ⟩ := exists_cliquePartition_of_packing P
  refine ⟨Q, hQ4, ?_⟩
  have hgain : P.gain = 2 * A.card.choose 2 + 2 * outsideCovered A P + liftCount A P := by
    unfold Packing.gain
    rw [sum_congr rfl fun K hK => gainOf_of_admissible (htype K hK), sum_add_distrib,
      sum_add_distrib, ← mul_sum, ← mul_sum, sum_choose_inter_eq P hcov,
      card_rootEdges G A hA, sum_boole]
    simp [outsideCovered, liftCount]
  have hedge := card_edgeFinset_add_missingIncidences G A
  rw [card_rootEdges G A hA, card_outsideVertices] at hedge
  omega

/-- **The general closing condition.**  If `m ≤ D + 2·oc + ℓ`, the completion stays within
`M(n) = targetSize n`. -/
theorem size_le_targetSize_of_ledger (hA : G.IsClique (A : Set V)) (P : Packing G)
    (htype : ∀ K ∈ P.pieces, AdmissibleType A K)
    (hcov : rootEdges G A ⊆ P.pieces.biUnion pairs)
    (hm : (outsideEdges G A).card ≤
      missingIncidences G A + 2 * outsideCovered A P + liftCount A P) :
    ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ PaperIV.targetSize (Fintype.card V) := by
  obtain ⟨Q, hQ4, hQ⟩ := ledger hA P htype hcov
  refine ⟨Q, hQ4, ?_⟩
  have hb := PaperIV.SplitCompleteRigidity.baseline_le_targetSize (Fintype.card V) A.card
    (by simpa using card_le_univ A)
  unfold PaperIV.SplitCompleteRigidity.baseline at hb
  omega

omit [Fintype V] [DecidableRel G.Adj] in
/-- For hosted triangles and lifted pieces only, each piece covers `[lifted]` outside edges. -/
theorem outsideCovered_eq_liftCount (P : Packing G)
    (htype : ∀ K ∈ P.pieces, (K ∩ A).card = 2 ∧ ((K \ A).card = 1 ∨ (K \ A).card = 2)) :
    outsideCovered A P = liftCount A P := by
  unfold outsideCovered liftCount
  rw [card_eq_sum_ones, sum_filter]
  refine sum_congr rfl fun K hK => ?_
  obtain ⟨h1, h2 | h2⟩ := htype K hK <;> simp [h1, h2]

/-- **Part A, the budget chain.**  Hosted triangles and lifted pieces covering every core
pair, with every outside edge lifted: the completion has exactly
`splitBaseline(n, a) − D − 2m` pieces. -/
theorem size_add_eq_baseline_of_all_lifted (hA : G.IsClique (A : Set V)) (P : Packing G)
    (htype : ∀ K ∈ P.pieces, (K ∩ A).card = 2 ∧ ((K \ A).card = 1 ∨ (K \ A).card = 2))
    (hcov : rootEdges G A ⊆ P.pieces.biUnion pairs)
    (hall : liftCount A P = (outsideEdges G A).card) :
    ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧
      Q.size + missingIncidences G A + 2 * (outsideEdges G A).card =
        PaperIV.SplitCompleteRigidity.baseline (Fintype.card V) A.card := by
  have htype' : ∀ K ∈ P.pieces, AdmissibleType A K := fun K hK => Or.inl (htype K hK)
  obtain ⟨Q, hQ4, hQ⟩ := ledger hA P htype' hcov
  refine ⟨Q, hQ4, ?_⟩
  rw [outsideCovered_eq_liftCount P htype, hall] at hQ
  unfold PaperIV.SplitCompleteRigidity.baseline
  omega

/-- **Part A, closed.**  Under the same hypotheses, `|Q| + D + 2m ≤ M(n)`. -/
theorem size_le_targetSize_of_all_lifted (hA : G.IsClique (A : Set V)) (P : Packing G)
    (htype : ∀ K ∈ P.pieces, (K ∩ A).card = 2 ∧ ((K \ A).card = 1 ∨ (K \ A).card = 2))
    (hcov : rootEdges G A ⊆ P.pieces.biUnion pairs)
    (hall : liftCount A P = (outsideEdges G A).card) :
    ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧
      Q.size + missingIncidences G A + 2 * (outsideEdges G A).card ≤
        PaperIV.targetSize (Fintype.card V) := by
  obtain ⟨Q, hQ4, hQ⟩ := size_add_eq_baseline_of_all_lifted hA P htype hcov hall
  exact ⟨Q, hQ4, hQ ▸ PaperIV.SplitCompleteRigidity.baseline_le_targetSize _ _
    (by simpa using card_le_univ A)⟩

end Ledger

/-! ## 5. The exact obstruction to lifting every outside edge -/

section Obstruction

variable [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj] {A : Finset V}

/-- The number of outside edges at `x`. -/
noncomputable def outsideDegree (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V)
    (x : V) : ℕ :=
  ((outsideEdges G A).filter fun e => x ∈ e).card

/-- The number of core neighbours of `x`. -/
def coreDegree (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) (x : V) : ℕ :=
  (A.filter fun u => G.Adj x u).card

/-- The pieces through the exterior vertex `x` that carry an outside edge. -/
def piecesAt (A : Finset V) (P : Packing G) (x : V) : Finset (Finset V) :=
  P.pieces.filter fun K => x ∈ K ∧ (K \ A).card = 2

omit [Fintype V] in
/-- Links at `x` are private: the core parts of the pieces through `x` are disjoint and
consist of core neighbours of `x`. -/
theorem sum_card_inter_piecesAt_le (P : Packing G) {x : V} (hx : x ∉ A) :
    ∑ K ∈ piecesAt A P x, (K ∩ A).card ≤ coreDegree G A x := by
  have hdisj : (↑(piecesAt A P x) : Set (Finset V)).PairwiseDisjoint (fun K => K ∩ A) := by
    intro K hK L hL hKL
    rw [Function.onFun, Finset.disjoint_left]
    intro u huK huL
    have hK' := (Finset.mem_filter.1 (mem_coe.1 hK))
    have hL' := (Finset.mem_filter.1 (mem_coe.1 hL))
    have hux : u ≠ x := fun h => hx (h ▸ (Finset.mem_inter.1 huK).2)
    have hmem : s(u, x) ∈ pairs K ∩ pairs L := by
      rw [Finset.mem_inter, mk_mem_pairs, mk_mem_pairs]
      exact ⟨⟨(Finset.mem_inter.1 huK).1, hK'.2.1, hux⟩,
        ⟨(Finset.mem_inter.1 huL).1, hL'.2.1, hux⟩⟩
    have := P.edgeDisjoint K hK'.1 L hL'.1 hKL
    exact (Finset.disjoint_left.1 this) (Finset.mem_inter.1 hmem).1 (Finset.mem_inter.1 hmem).2
  rw [← card_biUnion hdisj]
  apply card_le_card
  intro u hu
  obtain ⟨K, hK, huK⟩ := Finset.mem_biUnion.1 hu
  have hK' := Finset.mem_filter.1 hK
  have hux : u ≠ x := fun h => hx (h ▸ (Finset.mem_inter.1 huK).2)
  exact Finset.mem_filter.2 ⟨(Finset.mem_inter.1 huK).2,
    (P.isItem K hK'.1).1 x hK'.2.1 u (Finset.mem_inter.1 huK).1 (Ne.symm hux)⟩

/-- Every covered outside edge at `x` lies in a distinct piece through `x`. -/
theorem outsideDegree_le_card_piecesAt (P : Packing G)
    (htype : ∀ K ∈ P.pieces, AdmissibleType A K) {x : V}
    (hcov : (outsideEdges G A).filter (fun e => x ∈ e) ⊆ P.pieces.biUnion pairs) :
    outsideDegree G A x ≤ (piecesAt A P x).card := by
  have hsub : (outsideEdges G A).filter (fun e => x ∈ e) ⊆
      (piecesAt A P x).biUnion (fun K => pairs (K \ A)) := by
    intro e he
    obtain ⟨heO, hxe⟩ := Finset.mem_filter.1 he
    obtain ⟨K, hK, heK⟩ := Finset.mem_biUnion.1 (hcov he)
    have hKE : pairs K ⊆ G.edgeFinset := pairs_subset_edgeFinset (P.isItem K hK)
    have he' : e ∈ pairs (K \ A) := by
      rw [← pairs_inter_outsideEdges hKE]; exact Finset.mem_inter.2 ⟨heK, heO⟩
    have hxKA : x ∈ K \ A := (mem_pairs.1 he').1 x hxe
    have hcard2 : 2 ≤ (K \ A).card := by
      by_contra hlt
      have : (pairs (K \ A)).card = 0 := by
        rw [card_pairs, Nat.choose_eq_zero_iff]; omega
      rw [Finset.card_eq_zero] at this
      rw [this] at he'
      simp at he'
    have hle2 : (K \ A).card ≤ 2 := by
      rcases htype K hK with ⟨-, h | h⟩ | ⟨-, h⟩ <;> omega
    refine Finset.mem_biUnion.2 ⟨K, Finset.mem_filter.2 ⟨hK, (Finset.mem_sdiff.1 hxKA).1,
      by omega⟩, he'⟩
  calc outsideDegree G A x ≤ ((piecesAt A P x).biUnion (fun K => pairs (K \ A))).card :=
        card_le_card hsub
    _ ≤ ∑ K ∈ piecesAt A P x, (pairs (K \ A)).card := card_biUnion_le
    _ = ∑ K ∈ piecesAt A P x, 1 := by
        refine sum_congr rfl fun K hK => ?_
        rw [card_pairs, (Finset.mem_filter.1 hK).2.2]; rfl
    _ = (piecesAt A P x).card := by simp

/-- **Obstruction, general form.**  With admissible pieces, the covered outside edges at an
exterior vertex never outnumber its core neighbours. -/
theorem outsideDegree_le_coreDegree (P : Packing G)
    (htype : ∀ K ∈ P.pieces, AdmissibleType A K) {x : V} (hx : x ∉ A)
    (hcov : (outsideEdges G A).filter (fun e => x ∈ e) ⊆ P.pieces.biUnion pairs) :
    outsideDegree G A x ≤ coreDegree G A x := by
  refine le_trans (outsideDegree_le_card_piecesAt P htype hcov)
    (le_trans ?_ (sum_card_inter_piecesAt_le P hx))
  rw [card_eq_sum_ones]
  refine sum_le_sum fun K hK => ?_
  rcases htype K (Finset.mem_filter.1 hK).1 with ⟨h, -⟩ | ⟨h, -⟩ <;> omega

/-- **Obstruction for lifted pieces.**  If every outside edge at `x` is covered by hosted
triangles and lifted pieces, each covered edge uses two private links at `x`:
`2·deg_Z(x) ≤ |N(x) ∩ A|`.  In particular a vertex of `Z` with more than `a/2`
outside neighbours makes "lift every outside edge" impossible. -/
theorem two_mul_outsideDegree_le_coreDegree (P : Packing G)
    (htype : ∀ K ∈ P.pieces, (K ∩ A).card = 2 ∧ ((K \ A).card = 1 ∨ (K \ A).card = 2))
    {x : V} (hx : x ∉ A)
    (hcov : (outsideEdges G A).filter (fun e => x ∈ e) ⊆ P.pieces.biUnion pairs) :
    2 * outsideDegree G A x ≤ coreDegree G A x := by
  have htype' : ∀ K ∈ P.pieces, AdmissibleType A K := fun K hK => Or.inl (htype K hK)
  have h1 := outsideDegree_le_card_piecesAt P htype' hcov
  have h2 := sum_card_inter_piecesAt_le P hx
  have h3 : ∑ K ∈ piecesAt A P x, (K ∩ A).card = 2 * (piecesAt A P x).card := by
    rw [card_eq_sum_ones, mul_sum]
    refine sum_congr rfl fun K hK => ?_
    rw [(htype K (Finset.mem_filter.1 hK).1).1]
    rfl
  omega

end Obstruction

end PaperIV.LiftedPieces

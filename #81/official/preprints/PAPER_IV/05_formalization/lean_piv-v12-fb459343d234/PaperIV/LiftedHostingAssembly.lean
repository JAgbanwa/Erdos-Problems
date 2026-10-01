import PaperIV.LiftedPieceGreedy
import PaperIV.DyadicHosting

/-!
# E4 — assembling lifted pieces and Galvin-hosted triangles

Given a lift choice `pick` for **all** outside edges of the clique `A`, host every core
pair not used by a lift as a triangle `{u, v, z}` where `z` is taken from the list

`hostList(uv) = { z ∈ Z : z ~ u, z ~ v, and z lies in no lift through u or v }`.

If every such list has at least `3⌈a/2⌉ − 2` elements, the dyadic Galvin scheme
(`DyadicHosting.dyadic_list_colouring`) colours all core pairs from these lists.  The hosted
triangles are then compatible with each other and with the lifted pieces
(`card_inter_hosted_le_one`, `card_inter_hosted_lift_le_one`), they and the lifts cover all
core pairs, and the part-A ledger closes:

`exists_partition_of_lifts_and_hosting` :
  `∃ Q, Q.OrderAtMost 4 ∧ |Q| + D + 2m = splitBaseline(n, a) ≤ M(n)`.

`card_hostList_add` bounds the host list from below by
`(n − a) − d_u − d_v − 2·usage(u) − 2·usage(v)`, and `hostList_condition_of_bounds` turns
per-vertex bounds `d_u ≤ d`, `usage ≤ cap` into the list condition.
-/

namespace PaperIV.LiftedPieces

open Finset PaperIV.FarRounding PaperIV.RootVocab PaperIV.DyadicHosting

variable {V : Type*} [DecidableEq V] [Fintype V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {A : Finset V}

/-- The admissible hosts of a core pair `p`, avoiding every link used by a lift. -/
def hostList (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) (E : Finset (Sym2 V))
    (pick : Sym2 V → Finset V) (p : Sym2 V) : Finset V :=
  (univ \ A).filter fun z => (∀ u ∈ p.toFinset, G.Adj u z) ∧
    ∀ e ∈ E, (∃ u ∈ p.toFinset, u ∈ pick e) → z ∉ e.toFinset

/-- The hosted triangles of a colouring `c`, for the core pairs not in `PL`. -/
def hostedSet (A : Finset V) (PL : Finset (Finset V)) (c : V → V → V) : Finset (Finset V) :=
  ((A ×ˢ A).filter fun q => q.1 ≠ q.2 ∧ ({q.1, q.2} : Finset V) ∉ PL).image
    fun q => hostedTri q.1 q.2 (c q.1 q.2)

omit [Fintype V] in
/-- A proper colouring of the core pairs: the colour of a pair only depends on the pair. -/
theorem colour_eq_of_pair_eq {L : Sym2 V → Finset V} {c : V → V → V}
    (hc : IsProperListColouring A L c) {u v u' v' : V} (hu' : u' ∈ A) (hv' : v' ∈ A)
    (huv : u ≠ v) (hu'v' : u' ≠ v') (h : ({u, v} : Finset V) = {u', v'}) :
    c u v = c u' v' := by
  have hu : u ∈ ({u', v'} : Finset V) := h ▸ (by simp)
  have hv : v ∈ ({u', v'} : Finset V) := h ▸ (by simp)
  simp only [mem_insert, mem_singleton] at hu hv
  rcases hu with h1 | h1 <;> rcases hv with h2 | h2
  · exact absurd (h1.trans h2.symm) huv
  · rw [h1, h2]
  · rw [h1, h2]; exact (hc.1 v' hv' u' hu' (Ne.symm hu'v')).1
  · exact absurd (h1.trans h2.symm) huv

omit [Fintype V] in
/-- Two core pairs with the same colour and a common vertex are equal. -/
theorem pair_eq_of_colour_eq {L : Sym2 V → Finset V} {c : V → V → V}
    (hc : IsProperListColouring A L c) {u v u' v' : V} (hu : u ∈ A) (hv : v ∈ A)
    (hu' : u' ∈ A) (hv' : v' ∈ A) (huv : u ≠ v) (hu'v' : u' ≠ v')
    (heq : c u v = c u' v') {w : V} (hw : w = u ∨ w = v) (hw' : w = u' ∨ w = v') :
    ({u, v} : Finset V) = {u', v'} := by
  have hsym : ∀ {p q : V}, p ∈ A → q ∈ A → p ≠ q → c p q = c q p := fun hp hq hpq =>
    (hc.1 _ hp _ hq hpq).1
  rcases hw with rfl | rfl <;> rcases hw' with h | h
  · subst h
    by_contra hne
    have hvv : v ≠ v' := fun h => hne (by rw [h])
    exact hc.2 w hu v hv v' hv' huv hu'v' hvv heq
  · subst h
    by_contra hne
    have hvv : v ≠ u' := fun h => hne (by rw [h, pair_comm])
    exact hc.2 w hu v hv u' hu' huv (Ne.symm hu'v') hvv (heq.trans (hsym hu' hu hu'v'))
  · subst h
    by_contra hne
    have huv' : u ≠ v' := fun h => hne (by rw [h, pair_comm])
    exact hc.2 w hv u hu v' hv' (Ne.symm huv) hu'v' huv'
      ((hsym hv hu (Ne.symm huv)).trans heq)
  · subst h
    by_contra hne
    have huu : u ≠ u' := fun h => hne (by rw [h])
    exact hc.2 w hv u hu u' hu' (Ne.symm huv) (Ne.symm hu'v') huu
      ((hsym hv hu (Ne.symm huv)).trans (heq.trans (hsym hu' hv hu'v')))

omit [Fintype V] in
theorem hostedTri_inter_subset {u v z u' v' z' : V} (hu : u ∈ A) (hv : v ∈ A) (hz : z ∉ A)
    (hu' : u' ∈ A) (hv' : v' ∈ A) (hz' : z' ∉ A) :
    hostedTri u v z ∩ hostedTri u' v' z' ⊆ ({u, v} ∩ {u', v'}) ∪ ({z} ∩ {z'}) := by
  intro w hw
  simp only [hostedTri, mem_inter, mem_insert, mem_singleton, mem_union] at hw ⊢
  obtain ⟨h1, h2⟩ := hw
  rcases h1 with rfl | rfl | rfl <;> rcases h2 with h2 | h2 | h2 <;>
    first
    | (left; constructor <;> tauto)
    | (right; exact ⟨rfl, h2⟩)
    | (exfalso; subst h2; contradiction)

omit [Fintype V] in
theorem hostedTri_eq_insert (a b z : V) : hostedTri a b z = insert z {a, b} := by
  ext w; simp [hostedTri]; tauto

omit [Fintype V] in
/-- **Hosted triangles are pairwise compatible.** -/
theorem card_inter_hosted_le_one {L : Sym2 V → Finset V} {c : V → V → V}
    (hc : IsProperListColouring A L c) {u v u' v' : V} (hu : u ∈ A) (hv : v ∈ A)
    (hu' : u' ∈ A) (hv' : v' ∈ A) (huv : u ≠ v) (hu'v' : u' ≠ v')
    (hz : c u v ∉ A) (hz' : c u' v' ∉ A)
    (hne : hostedTri u v (c u v) ≠ hostedTri u' v' (c u' v')) :
    (hostedTri u v (c u v) ∩ hostedTri u' v' (c u' v')).card ≤ 1 := by
  have hpair : ({u, v} : Finset V) ≠ {u', v'} := by
    intro h
    apply hne
    rw [colour_eq_of_pair_eq hc hu' hv' huv hu'v' h, hostedTri_eq_insert,
      hostedTri_eq_insert, h]
  refine le_trans (card_le_card (hostedTri_inter_subset hu hv hz hu' hv' hz'))
    (le_trans (card_union_le _ _) ?_)
  by_cases hzz : c u v = c u' v'
  · have : ({u, v} : Finset V) ∩ {u', v'} = ∅ := by
      ext w
      simp only [mem_inter, mem_insert, mem_singleton, notMem_empty, iff_false, not_and]
      intro hw hw'
      exact hpair (pair_eq_of_colour_eq hc hu hv hu' hv' huv hu'v' hzz hw hw')
    rw [this, card_empty, zero_add]
    exact le_trans (card_le_card inter_subset_left) (by simp)
  · have : ({c u v} : Finset V) ∩ {c u' v'} = ∅ := by
      ext w; simp only [mem_inter, mem_singleton, notMem_empty, iff_false, not_and]
      rintro rfl h; exact hzz h
    rw [this, card_empty, add_zero]
    exact card_inter_le_one_of_ne (card_pair huv) (card_pair hu'v') hpair

/-- **Hosted triangles are compatible with the lifted pieces.** -/
theorem card_inter_hosted_lift_le_one {E : Finset (Sym2 V)} (hE : E ⊆ outsideEdges G A)
    {pick : Sym2 V → Finset V} {cap : ℕ} (hP : GoodLifts G A E pick cap)
    {u v z : V} (hu : u ∈ A) (hv : v ∈ A) (huv : u ≠ v)
    (hz : z ∈ hostList G A E pick s(u, v)) (hnot : ∀ f ∈ E, pick f ≠ {u, v})
    {e : Sym2 V} (he : e ∈ E) :
    (hostedTri u v z ∩ liftOf pick e).card ≤ 1 := by
  obtain ⟨hzZ, hzadj, hzfree⟩ : z ∉ A ∧ _ ∧ _ := by
    simp only [hostList, mem_filter, mem_sdiff, mem_univ, true_and] at hz
    exact ⟨hz.1, hz.2.1, hz.2.2⟩
  have hZ : ∀ w ∈ e.toFinset, w ∉ A := by
    intro w hw
    obtain ⟨p, rfl⟩ := Quot.exists_rep e
    obtain ⟨x, y⟩ := p
    have hO := mem_outsideEdges_iff.1 (hE he)
    have : w = x ∨ w = y := by simpa [Sym2.toFinset_mk_eq] using hw
    rcases this with rfl | rfl
    · exact hO.2.1
    · exact hO.2.2
  have hsplit : hostedTri u v z ∩ liftOf pick e ⊆
      (({u, v} : Finset V) ∩ pick e) ∪ ({z} ∩ e.toFinset) := by
    intro w hw
    simp only [hostedTri, liftOf, mem_inter, mem_insert, mem_singleton, mem_union] at hw ⊢
    obtain ⟨h1, h2 | h2⟩ := hw
    · rcases h1 with rfl | rfl | rfl
      · exact Or.inl ⟨Or.inl rfl, h2⟩
      · exact Or.inl ⟨Or.inr rfl, h2⟩
      · exact absurd ((hP.1 e he).1 h2) hzZ
    · rcases h1 with rfl | rfl | rfl
      · exact absurd hu (hZ w h2)
      · exact absurd hv (hZ w h2)
      · exact Or.inr ⟨rfl, h2⟩
  refine le_trans (card_le_card hsplit) (le_trans (card_union_le _ _) ?_)
  by_cases hze : z ∈ e.toFinset
  · have : ({u, v} : Finset V) ∩ pick e = ∅ := by
      ext w
      simp only [mem_inter, mem_insert, mem_singleton, notMem_empty, iff_false, not_and]
      intro hw hwp
      exact hzfree e he ⟨w, by simpa [Sym2.toFinset_mk_eq] using hw, hwp⟩ hze
    rw [this, card_empty, zero_add]
    exact le_trans (card_le_card inter_subset_left) (by simp)
  · have : ({z} : Finset V) ∩ e.toFinset = ∅ := by
      ext w; simp only [mem_inter, mem_singleton, notMem_empty, iff_false, not_and]
      rintro rfl; exact hze
    rw [this, card_empty, add_zero]
    exact card_inter_le_one_of_ne (card_pair huv) (hP.1 e he).2.1 (fun h => hnot e he h.symm)

theorem mem_hostList_mk {E : Finset (Sym2 V)} {pick : Sym2 V → Finset V} {u v z : V} :
    z ∈ hostList G A E pick s(u, v) ↔ z ∉ A ∧ (G.Adj u z ∧ G.Adj v z) ∧
      ∀ e ∈ E, (u ∈ pick e ∨ v ∈ pick e) → z ∉ e.toFinset := by
  simp [hostList, Sym2.toFinset_mk_eq]

theorem liftOf_sdiff {E : Finset (Sym2 V)} (hE : E ⊆ outsideEdges G A)
    {pick : Sym2 V → Finset V} {cap : ℕ} (hP : GoodLifts G A E pick cap)
    {e : Sym2 V} (he : e ∈ E) : liftOf pick e \ A = e.toFinset := by
  obtain ⟨p, rfl⟩ := Quot.exists_rep e
  obtain ⟨x, y⟩ := p
  have hO := mem_outsideEdges_iff.1 (hE he)
  have hsub := (hP.1 _ he).1
  ext w
  simp only [liftOf, mem_sdiff, mem_union]
  constructor
  · rintro ⟨h | h, hw⟩
    · exact absurd (hsub h) hw
    · exact h
  · intro h
    refine ⟨Or.inr h, ?_⟩
    have : w = x ∨ w = y := by simpa [Sym2.toFinset_mk_eq] using h
    rcases this with rfl | rfl
    · exact hO.2.1
    · exact hO.2.2

/-- **E4 assembled: lifted pieces plus Galvin-hosted triangles close the budget.**
Given a lift choice for every outside edge and host lists of size `3⌈a/2⌉ − 2`, there is a
clique partition of order at most four with exactly `splitBaseline(n, a) − D − 2m` pieces. -/
theorem exists_partition_of_lifts_and_hosting (hA : G.IsClique (A : Set V))
    {pick : Sym2 V → Finset V} {cap : ℕ}
    (hP : GoodLifts G A (outsideEdges G A) pick cap)
    (hlist : ∀ u ∈ A, ∀ v ∈ A, u ≠ v →
      3 * ((A.card + 1) / 2) ≤ (hostList G A (outsideEdges G A) pick s(u, v)).card + 2) :
    ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧
      Q.size + missingIncidences G A + 2 * (outsideEdges G A).card =
        PaperIV.SplitCompleteRigidity.baseline (Fintype.card V) A.card := by
  classical
  set E := outsideEdges G A with hEdef
  have hE : E ⊆ outsideEdges G A := subset_rfl
  obtain ⟨c, hc⟩ : ∃ c : V → V → V, IsProperListColouring A (hostList G A E pick) c := by
    rcases isEmpty_or_nonempty V with hV | hV
    · exact ⟨fun u _ => u, fun u _ => isEmptyElim u, fun u _ => isEmptyElim u⟩
    · exact dyadic_list_colouring A _ hlist
  have hcL : ∀ u ∈ A, ∀ v ∈ A, u ≠ v → c u v ∉ A ∧ (G.Adj u (c u v) ∧ G.Adj v (c u v)) ∧
      ∀ e ∈ E, (u ∈ pick e ∨ v ∈ pick e) → c u v ∉ e.toFinset :=
    fun u hu v hv huv => mem_hostList_mk.1 (hc.1 u hu v hv huv).2
  set PL := E.image pick with hPL
  set T := hostedSet A PL c with hT
  set Lf := E.image (liftOf pick) with hLf
  have hTmem : ∀ K ∈ T, ∃ u ∈ A, ∃ v ∈ A, u ≠ v ∧ ({u, v} : Finset V) ∉ PL ∧
      K = hostedTri u v (c u v) := by
    intro K hK
    obtain ⟨q, hq, rfl⟩ := mem_image.1 hK
    obtain ⟨hqA, hq1, hq2⟩ := mem_filter.1 hq
    exact ⟨q.1, (mem_product.1 hqA).1, q.2, (mem_product.1 hqA).2, hq1, hq2, rfl⟩
  have hLmem : ∀ K ∈ Lf, ∃ e ∈ E, K = liftOf pick e := by
    intro K hK
    obtain ⟨e, he, rfl⟩ := mem_image.1 hK
    exact ⟨e, he, rfl⟩
  have hTtype : ∀ K ∈ T, (K ∩ A).card = 2 ∧ (K \ A).card = 1 := by
    intro K hK
    obtain ⟨u, hu, v, hv, huv, -, rfl⟩ := hTmem K hK
    have hz := (hcL u hu v hv huv).1
    rw [hostedTri_inter_core hu hv hz, hostedTri_sdiff_core hu hv hz, card_pair huv,
      card_singleton]
    exact ⟨rfl, rfl⟩
  have hLtype : ∀ K ∈ Lf, IsItem G K ∧ (K ∩ A).card = 2 ∧ (K \ A).card = 2 := by
    intro K hK
    obtain ⟨e, he, rfl⟩ := hLmem K hK
    exact liftOf_isItem hA hE hP he
  have hTT : ∀ K ∈ T, ∀ K' ∈ T, K ≠ K' → (K ∩ K').card ≤ 1 := by
    intro K hK K' hK' hne
    obtain ⟨u, hu, v, hv, huv, -, rfl⟩ := hTmem K hK
    obtain ⟨u', hu', v', hv', hu'v', -, rfl⟩ := hTmem K' hK'
    exact card_inter_hosted_le_one hc hu hv hu' hv' huv hu'v' (hcL u hu v hv huv).1
      (hcL u' hu' v' hv' hu'v').1 hne
  have hTL : ∀ K ∈ T, ∀ K' ∈ Lf, (K ∩ K').card ≤ 1 := by
    intro K hK K' hK'
    obtain ⟨u, hu, v, hv, huv, hnot, rfl⟩ := hTmem K hK
    obtain ⟨e, he, rfl⟩ := hLmem K' hK'
    refine card_inter_hosted_lift_le_one hE hP hu hv huv (hc.1 u hu v hv huv).2
      (fun f hf h => hnot (mem_image.2 ⟨f, hf, h⟩)) he
  have hLL : ∀ K ∈ Lf, ∀ K' ∈ Lf, K ≠ K' → (K ∩ K').card ≤ 1 := by
    intro K hK K' hK' hne
    obtain ⟨e, he, rfl⟩ := hLmem K hK
    obtain ⟨f, hf, rfl⟩ := hLmem K' hK'
    exact card_inter_liftOf_le_one hE hP he hf (fun h => hne (by rw [h]))
  let P : Packing G :=
    { pieces := T ∪ Lf
      isItem := by
        intro K hK
        rcases mem_union.1 hK with hK | hK
        · obtain ⟨u, hu, v, hv, huv, -, rfl⟩ := hTmem K hK
          obtain ⟨hz, ⟨hzu, hzv⟩, -⟩ := hcL u hu v hv huv
          exact (hostedTri_isItem hA hu hv huv hz hzu hzv).1
        · exact (hLtype K hK).1
      edgeDisjoint := by
        intro K hK K' hK' hne
        rw [disjoint_pairs_iff]
        rcases mem_union.1 hK with hK | hK <;> rcases mem_union.1 hK' with hK' | hK'
        · exact hTT K hK K' hK' hne
        · exact hTL K hK K' hK'
        · rw [inter_comm]; exact hTL K' hK' K hK
        · exact hLL K hK K' hK' hne }
  have htype : ∀ K ∈ P.pieces, (K ∩ A).card = 2 ∧ ((K \ A).card = 1 ∨ (K \ A).card = 2) := by
    intro K hK
    rcases mem_union.1 hK with hK | hK
    · exact ⟨(hTtype K hK).1, Or.inl (hTtype K hK).2⟩
    · exact ⟨(hLtype K hK).2.1, Or.inr (hLtype K hK).2.2⟩
  have hcov : rootEdges G A ⊆ P.pieces.biUnion pairs := by
    intro e he
    obtain ⟨p, rfl⟩ := Quot.exists_rep e
    obtain ⟨u, v⟩ := p
    have he' : s(u, v) ∈ rootEdges G A := he
    simp only [rootEdges, mem_filter, Sym2.toFinset_mk_eq, insert_subset_iff,
      singleton_subset_iff, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he'
    obtain ⟨hadj, hu, hv⟩ := he'
    have huv : u ≠ v := G.ne_of_adj hadj
    show s(u, v) ∈ P.pieces.biUnion pairs
    by_cases hin : ({u, v} : Finset V) ∈ PL
    · obtain ⟨f, hf, hpf⟩ := mem_image.1 hin
      refine mem_biUnion.2 ⟨liftOf pick f, mem_union_right _ (mem_image.2 ⟨f, hf, rfl⟩), ?_⟩
      rw [mk_mem_pairs]
      refine ⟨mem_union_left _ (hpf ▸ by simp), mem_union_left _ (hpf ▸ by simp), huv⟩
    · refine mem_biUnion.2 ⟨hostedTri u v (c u v), mem_union_left _ ?_, ?_⟩
      · exact mem_image.2 ⟨(u, v), mem_filter.2 ⟨mem_product.2 ⟨hu, hv⟩, huv, hin⟩, rfl⟩
      · rw [mk_mem_pairs]
        exact ⟨by simp [hostedTri], by simp [hostedTri], huv⟩
  have hall : liftCount A P = E.card := by
    have hfilt : P.pieces.filter (fun K => (K ∩ A).card = 2 ∧ (K \ A).card = 2) = Lf := by
      ext K
      simp only [mem_filter]
      constructor
      · rintro ⟨hK, -, h2⟩
        rcases mem_union.1 hK with hK | hK
        · have := (hTtype K hK).2; omega
        · exact hK
      · intro hK
        exact ⟨mem_union_right _ hK, (hLtype K hK).2.1, (hLtype K hK).2.2⟩
    unfold liftCount
    rw [hfilt, hLf, card_image_of_injOn]
    intro e he f hf hef
    have h1 := liftOf_sdiff hE hP (mem_coe.1 he)
    have h2 := liftOf_sdiff hE hP (mem_coe.1 hf)
    have : liftOf pick e \ A = liftOf pick f \ A := by rw [hef]
    rw [h1, h2] at this
    exact toFinset_injective_sym2 this
  exact size_add_eq_baseline_of_all_lifted hA P htype hcov hall

/-- **E4, closed form.**  Same hypotheses: `|Q| + D + 2m ≤ M(n)`. -/
theorem exists_partition_le_targetSize_of_lifts_and_hosting (hA : G.IsClique (A : Set V))
    {pick : Sym2 V → Finset V} {cap : ℕ}
    (hP : GoodLifts G A (outsideEdges G A) pick cap)
    (hlist : ∀ u ∈ A, ∀ v ∈ A, u ≠ v →
      3 * ((A.card + 1) / 2) ≤ (hostList G A (outsideEdges G A) pick s(u, v)).card + 2) :
    ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧
      Q.size + missingIncidences G A + 2 * (outsideEdges G A).card ≤
        PaperIV.targetSize (Fintype.card V) := by
  obtain ⟨Q, hQ4, hQ⟩ := exists_partition_of_lifts_and_hosting hA hP hlist
  exact ⟨Q, hQ4, hQ ▸ PaperIV.SplitCompleteRigidity.baseline_le_targetSize _ _
    (by simpa using card_le_univ A)⟩

/-! ## The size of the host lists -/

omit [Fintype V] in
theorem card_toFinset_sym2_le (e : Sym2 V) : e.toFinset.card ≤ 2 := by
  obtain ⟨p, rfl⟩ := Quot.exists_rep e
  obtain ⟨x, y⟩ := p
  show (s(x, y)).toFinset.card ≤ 2
  rw [Sym2.toFinset_mk_eq]
  exact card_le_two

/-- **Host lists are long.**  Every exterior vertex is a host of `uv` unless it misses `u`
or `v`, or lies in a lift through `u` or `v`:
`|hostList(uv)| + d_u + d_v + 2·usage(u) + 2·usage(v) ≥ n − a`. -/
theorem card_hostList_add (E : Finset (Sym2 V)) (pick : Sym2 V → Finset V) (u v : V) :
    Fintype.card V - A.card ≤ (hostList G A E pick s(u, v)).card +
      (missingColumn G A u).card + (missingColumn G A v).card +
        2 * usage E pick u + 2 * usage E pick v := by
  have hB : ∀ w, ((E.filter fun e => w ∈ pick e).biUnion Sym2.toFinset).card ≤
      2 * usage E pick w := by
    intro w
    refine le_trans card_biUnion_le ?_
    unfold usage
    rw [mul_comm, card_eq_sum_ones, sum_mul]
    exact sum_le_sum fun e _ => by rw [one_mul]; exact card_toFinset_sym2_le e
  have hsub : univ \ A ⊆ hostList G A E pick s(u, v) ∪ missingColumn G A u ∪
      missingColumn G A v ∪ (E.filter fun e => u ∈ pick e).biUnion Sym2.toFinset ∪
        (E.filter fun e => v ∈ pick e).biUnion Sym2.toFinset := by
    intro z hz
    have hzA : z ∉ A := (mem_sdiff.1 hz).2
    by_cases h1 : z ∈ hostList G A E pick s(u, v)
    · simp [h1]
    rw [mem_hostList_mk] at h1
    simp only [mem_union, missingColumn, mem_filter, mem_outsideVertices, mem_biUnion]
    by_cases hu : G.Adj u z
    · by_cases hv : G.Adj v z
      · have : ¬ ∀ e ∈ E, (u ∈ pick e ∨ v ∈ pick e) → z ∉ e.toFinset := fun h =>
          h1 ⟨hzA, ⟨hu, hv⟩, h⟩
        push_neg at this
        obtain ⟨e, he, huv, hze⟩ := this
        rcases huv with h | h
        · exact Or.inl (Or.inr ⟨e, ⟨he, h⟩, hze⟩)
        · exact Or.inr ⟨e, ⟨he, h⟩, hze⟩
      · exact Or.inl (Or.inl (Or.inr ⟨hzA, hv⟩))
    · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨hzA, hu⟩)))
  have hZ : (univ \ A).card = Fintype.card V - A.card := by
    rw [card_sdiff_of_subset (subset_univ A), card_univ]
  have h := card_le_card hsub
  have hu := hB u
  have hv := hB v
  have h1 := card_union_le (hostList G A E pick s(u, v) ∪ missingColumn G A u ∪
      missingColumn G A v ∪ (E.filter fun e => u ∈ pick e).biUnion Sym2.toFinset)
    ((E.filter fun e => v ∈ pick e).biUnion Sym2.toFinset)
  have h2 := card_union_le (hostList G A E pick s(u, v) ∪ missingColumn G A u ∪
      missingColumn G A v) ((E.filter fun e => u ∈ pick e).biUnion Sym2.toFinset)
  have h3 := card_union_le (hostList G A E pick s(u, v) ∪ missingColumn G A u)
    (missingColumn G A v)
  have h4 := card_union_le (hostList G A E pick s(u, v)) (missingColumn G A u)
  omega

/-- **The list condition from per-vertex bounds.**  If every core vertex misses at most
`d` exterior vertices, every core vertex lies in at most `cap` lifts, and
`3⌈a/2⌉ + 2d + 4·cap ≤ (n − a) + 2`, the host lists satisfy the dyadic condition. -/
theorem hostList_condition_of_bounds {E : Finset (Sym2 V)} {pick : Sym2 V → Finset V}
    {d cap : ℕ} (hd : ∀ u ∈ A, (missingColumn G A u).card ≤ d)
    (hcap : ∀ u, usage E pick u ≤ cap)
    (harith : 3 * ((A.card + 1) / 2) + 2 * d + 4 * cap ≤ Fintype.card V - A.card + 2) :
    ∀ u ∈ A, ∀ v ∈ A, u ≠ v →
      3 * ((A.card + 1) / 2) ≤ (hostList G A E pick s(u, v)).card + 2 := by
  intro u hu v hv _
  have h := card_hostList_add (G := G) (A := A) E pick u v
  have := hd u hu
  have := hd v hv
  have := hcap u
  have := hcap v
  omega

/-- **The arithmetic of the window.**  With `a ≤ n/3 + εn`, per-vertex deficiency
`d ≤ n/24` and usage cap `cap ≤ κn`, the list condition holds as soon as
`(5/2)ε + 4κ ≤ 1/12`.  (With the E3 threshold `n/12` in place of `n/24` the same
computation has no room left: `2·(n/12) = n/6` already uses the whole margin
`n − a − (3/2)a` at `a = n/3`.) -/
theorem list_arith {n a d cap : ℕ} {eps kappa : ℚ} (han : a ≤ n)
    (ha : (a : ℚ) ≤ n / 3 + eps * n) (hd : (d : ℚ) ≤ n / 24) (hcap : (cap : ℚ) ≤ kappa * n)
    (hek : 5 / 2 * eps + 4 * kappa ≤ 1 / 12) :
    3 * ((a + 1) / 2) + 2 * d + 4 * cap ≤ n - a + 2 := by
  have h1 : 2 * ((a + 1) / 2) ≤ a + 1 := Nat.mul_div_le (a + 1) 2
  have h1q : (2 : ℚ) * (((a + 1) / 2 : ℕ) : ℚ) ≤ a + 1 := by exact_mod_cast h1
  have hn : (0 : ℚ) ≤ n := Nat.cast_nonneg n
  have key : (3 * ((a + 1) / 2) + 2 * d + 4 * cap : ℕ) + (a : ℚ) ≤ n + 2 := by
    push_cast
    nlinarith
  have key' : 3 * ((a + 1) / 2) + 2 * d + 4 * cap + a ≤ n + 2 := by exact_mod_cast key
  omega

/-- **E4 from explicit per-vertex hypotheses.**  Greedy lifts for every outside edge
(`hcap`, `hroom`, the hypotheses of `exists_goodLifts`) together with the core deficiency
bound `d` and the window arithmetic give a clique partition of order at most four with
`|Q| + D + 2m ≤ M(n)`.  `hroom` is a condition on the **exterior** side (common core
neighbourhoods and exterior degrees) which the localization does not provide; see
`two_mul_outsideDegree_le_coreDegree` for why some such condition is unavoidable when every
outside edge is to be lifted. -/
theorem exists_partition_of_greedy_bounds (hA : G.IsClique (A : Set V)) (cap s d : ℕ)
    (hcap : 2 * (outsideEdges G A).card ≤ cap * (s + 1))
    (hroom : ∀ x y, s(x, y) ∈ outsideEdges G A →
      (outsideEdges G A).card ≤ ((commonCore G A x y).card -
        2 * (edgeDeg (outsideEdges G A) x + edgeDeg (outsideEdges G A) y) - s).choose 2)
    (hd : ∀ u ∈ A, (missingColumn G A u).card ≤ d)
    (harith : 3 * ((A.card + 1) / 2) + 2 * d + 4 * cap ≤ Fintype.card V - A.card + 2) :
    ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧
      Q.size + missingIncidences G A + 2 * (outsideEdges G A).card ≤
        PaperIV.targetSize (Fintype.card V) := by
  obtain ⟨pick, hP⟩ := exists_goodLifts (outsideEdges G A) subset_rfl cap s hcap hroom
  exact exists_partition_le_targetSize_of_lifts_and_hosting hA hP
    (hostList_condition_of_bounds hd hP.2.2.2 harith)

end PaperIV.LiftedPieces

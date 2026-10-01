import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan
import PaperIV.RootedSimplicialDefect

/-!
# Edit route, Lemmas B and C: no long-cycle blow-ups, and clique recovery

Both lemmas are about the literal `RootedDefectAt G s` of
`PaperIV.RootedSimplicialDefect`.

* **Lemma C** (`clique_of_rootedDefect_of_few_nonedges`).  If `G` has rooted defect
  `≤ s` and `W` is any vertex set with `ē` non-adjacent pairs, then `W` contains a
  real clique `C` of `G` with `|W| ≤ |C| + 2ν`, where
  `ν² + (s+1)ν ≤ 2(s+1)ē`.  Here `ν` is the size of a maximum matching of
  non-edges inside `W`.  (This is slightly sharper than `ν² ≤ 2(s+1)ē + (s+1)ν`.)
* **Lemma B** (`noBlowup_of_rootedDefect`).  A blow-up of a cycle of length `k ≥ 4`
  with parts of size `≥ s+1` (arbitrary edges inside the parts) violates
  `RootedDefectAt G s`.
-/

namespace PaperIV.EditRoute

open Finset
open PaperIV.RootedSimplicialDefect

/-! ## Turán, in the form used here -/

/-- Turán's theorem, loose form: a `K_{r+1}`-free graph on `N` vertices has
`2 r e ≤ (r-1) N²`. -/
theorem two_mul_card_edgeFinset_le_of_cliqueFree {α : Type*} [Fintype α]
    (H : SimpleGraph α) [DecidableRel H.Adj] {r : ℕ}
    (hr : 0 < r) (cf : H.CliqueFree (r + 1)) :
    2 * r * #H.edgeFinset ≤ (r - 1) * (Fintype.card α) ^ 2 := by
  obtain ⟨H', _, maxH⟩ := SimpleGraph.exists_isTuranMaximal (V := α) hr
  have h1 : #H.edgeFinset ≤ #H'.edgeFinset := maxH.2 cf
  have h2 := ((SimpleGraph.isTuranMaximal_iff_nonempty_iso_turanGraph hr).mp
    maxH).some.card_edgeFinset_eq
  have h3 := SimpleGraph.mul_card_edgeFinset_turanGraph_le (n := Fintype.card α) (r := r)
  rw [← h2] at h3
  calc 2 * r * #H.edgeFinset ≤ 2 * r * #H'.edgeFinset := by gcongr
    _ ≤ _ := h3

theorem card_dart_eq_card_filter {α : Type*} [Fintype α] [DecidableEq α]
    (H : SimpleGraph α) [DecidableRel H.Adj] :
    Fintype.card H.Dart = #((univ : Finset (α × α)).filter (fun p => H.Adj p.1 p.2)) := by
  rw [← Fintype.card_subtype]
  exact Fintype.card_congr
    { toFun := fun d => ⟨d.toProd, d.adj⟩
      invFun := fun p => ⟨p.1, p.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## Non-edges and matchings of non-edges -/

/-- The non-adjacent (unordered, distinct) pairs inside `W`. -/
def nonEdgesIn (W : Finset V) : Finset (Sym2 V) :=
  W.sym2.filter fun e => ¬ e.IsDiag ∧ e ∉ G.edgeFinset

/-- The two ends of an ordered pair. -/
def pairVerts (p : V × V) : Finset V := {p.1, p.2}

omit [Fintype V] in
theorem mem_pairVerts {p : V × V} {x : V} : x ∈ pairVerts p ↔ x = p.1 ∨ x = p.2 := by
  simp [pairVerts]

/-- A matching of non-edges of `G` inside `W`. -/
def IsNonEdgeMatching (W : Finset V) (M : Finset (V × V)) : Prop :=
  (∀ p ∈ M, p.1 ∈ W ∧ p.2 ∈ W ∧ p.1 ≠ p.2 ∧ ¬ G.Adj p.1 p.2) ∧
    (M : Set (V × V)).PairwiseDisjoint pairVerts

variable {G}

omit [Fintype V] [DecidableRel G.Adj] in
theorem card_pairVerts {p : V × V} (h : p.1 ≠ p.2) : #(pairVerts p) = 2 := by
  simp [pairVerts, Finset.card_pair h]

omit [Fintype V] [DecidableRel G.Adj] in
theorem card_biUnion_pairVerts {W : Finset V} {M : Finset (V × V)}
    (hM : IsNonEdgeMatching G W M) : #(M.biUnion pairVerts) = 2 * #M := by
  rw [card_biUnion hM.2, Finset.sum_congr rfl (fun p hp => card_pairVerts (hM.1 p hp).2.2.1)]
  simp [mul_comm]

omit [Fintype V] in
/-- (ii) For a maximum matching of non-edges, the unmatched part of `W` is a clique. -/
theorem isClique_sdiff_of_maximum {W : Finset V} {M : Finset (V × V)}
    (hM : IsNonEdgeMatching G W M)
    (hmax : ∀ M', IsNonEdgeMatching G W M' → #M' ≤ #M) :
    G.IsClique ((W \ M.biUnion pairVerts : Finset V) : Set V) := by
  intro a ha b hb hab
  simp only [coe_sdiff, Set.mem_diff, mem_coe, mem_biUnion, not_exists, not_and] at ha hb
  by_contra hnadj
  have hnotM : (a, b) ∉ M := fun h => ha.2 (a, b) h (by simp [pairVerts])
  have hM' : IsNonEdgeMatching G W (insert (a, b) M) := by
    refine ⟨?_, ?_⟩
    · intro p hp
      rcases mem_insert.1 hp with rfl | hp
      · exact ⟨ha.1, hb.1, hab, hnadj⟩
      · exact hM.1 p hp
    · rw [coe_insert]
      refine hM.2.insert ?_
      intro q hq _
      rw [Finset.disjoint_left]
      intro x hx hxq
      rcases mem_pairVerts.1 hx with rfl | rfl
      · exact ha.2 q hq hxq
      · exact hb.2 q hq hxq
  have := hmax _ hM'
  rw [card_insert_of_notMem hnotM] at this
  omega

omit [Fintype V] in
/-- (i) No `s+2` matching non-edges are pairwise completely joined: that would be an
induced `(s+2)K₂` in the complement, violating the rooted defect with an empty root. -/
theorem false_of_joined_matching {s : ℕ} (hG : RootedDefectAt G s) {T : Finset (V × V)}
    (hnon : ∀ p ∈ T, p.1 ≠ p.2 ∧ ¬ G.Adj p.1 p.2)
    (hdisj : (T : Set (V × V)).PairwiseDisjoint pairVerts)
    (hcard : #T = s + 2)
    (hjoin : ∀ p ∈ T, ∀ q ∈ T, p ≠ q → ∀ x ∈ pairVerts p, ∀ y ∈ pairVerts q, G.Adj x y) :
    False := by
  set U := T.biUnion pairVerts with hU
  have hTne : T.Nonempty := by
    rw [← Finset.card_pos]; omega
  have hUne : (U \ ∅).Nonempty := by
    obtain ⟨p, hp⟩ := hTne
    exact ⟨p.1, by simp [hU]; exact ⟨p.1, p.2, hp, by simp [pairVerts]⟩⟩
  obtain ⟨v, hv, C, hCsub, hCcl, hCcard⟩ :=
    hG U ∅ (empty_subset _) (by simp) hUne
  rw [sdiff_empty] at hv
  obtain ⟨p0, hp0, hvp0⟩ := mem_biUnion.1 hv
  have hN : neighborsIn G U v = (T.erase p0).biUnion pairVerts := by
    ext w
    simp only [neighborsIn, mem_filter, mem_biUnion, mem_erase]
    constructor
    · rintro ⟨hwU, hadj⟩
      obtain ⟨q, hq, hwq⟩ := mem_biUnion.1 hwU
      refine ⟨q, ⟨?_, hq⟩, hwq⟩
      rintro rfl
      have hne := G.ne_of_adj hadj
      have hq2 := (hnon q hq).2
      rcases mem_pairVerts.1 hvp0 with h1 | h1 <;> rcases mem_pairVerts.1 hwq with h2 | h2
      · exact hne (h1.trans h2.symm)
      · exact hq2 (h1 ▸ h2 ▸ hadj)
      · exact hq2 (h1 ▸ h2 ▸ hadj.symm)
      · exact hne (h1.trans h2.symm)
    · rintro ⟨q, ⟨hqp, hq⟩, hwq⟩
      exact ⟨mem_biUnion.2 ⟨q, hq, hwq⟩, hjoin p0 hp0 q hq (Ne.symm hqp) v hvp0 w hwq⟩
  have hdisj' : ((T.erase p0 : Finset (V × V)) : Set (V × V)).PairwiseDisjoint pairVerts :=
    hdisj.subset (by intro x hx; exact mem_of_mem_erase hx)
  have hNcard : #(neighborsIn G U v) = 2 * (s + 1) := by
    rw [hN, card_biUnion hdisj',
      Finset.sum_congr rfl (fun q hq => card_pairVerts (hnon q (mem_of_mem_erase hq)).1)]
    simp [card_erase_of_mem hp0, hcard, mul_comm]
  have hCle : #C ≤ s + 1 := by
    have hsub : C ⊆ (T.erase p0).biUnion (fun q => C ∩ pairVerts q) := by
      intro x hx
      have hx' := hCsub hx
      rw [hN, mem_biUnion] at hx'
      obtain ⟨q, hq, hxq⟩ := hx'
      exact mem_biUnion.2 ⟨q, hq, mem_inter.2 ⟨hx, hxq⟩⟩
    have hone : ∀ q ∈ T.erase p0, #(C ∩ pairVerts q) ≤ 1 := by
      intro q hq
      rw [Finset.card_le_one]
      intro a ha b hb
      by_contra hab
      rw [mem_inter] at ha hb
      have hadj := hCcl ha.1 hb.1 hab
      have hq2 := (hnon q (mem_of_mem_erase hq)).2
      rcases mem_pairVerts.1 ha.2 with h1 | h1 <;> rcases mem_pairVerts.1 hb.2 with h2 | h2
      · exact hab (h1.trans h2.symm)
      · exact hq2 (h1 ▸ h2 ▸ hadj)
      · exact hq2 (h1 ▸ h2 ▸ hadj.symm)
      · exact hab (h1.trans h2.symm)
    calc #C ≤ #((T.erase p0).biUnion (fun q => C ∩ pairVerts q)) := card_le_card hsub
      _ ≤ ∑ q ∈ T.erase p0, #(C ∩ pairVerts q) := card_biUnion_le
      _ ≤ ∑ q ∈ T.erase p0, 1 := sum_le_sum hone
      _ = s + 1 := by simp [card_erase_of_mem hp0, hcard]
  omega

/-! ## (iii) Counting non-edges against the conflict structure of the matching -/

/-- The ordered non-adjacent pairs of distinct vertices of `W`. -/
def ordNonEdgesIn (G : SimpleGraph V) [DecidableRel G.Adj] (W : Finset V) : Finset (V × V) :=
  (W ×ˢ W).filter fun xy => xy.1 ≠ xy.2 ∧ ¬ G.Adj xy.1 xy.2

theorem card_ordNonEdgesIn_le (W : Finset V) :
    #(ordNonEdgesIn G W) ≤ 2 * #(nonEdgesIn G W) := by
  classical
  have h1 := Finset.card_le_mul_card_image (ordNonEdgesIn G W) 2
    (f := fun xy : V × V => s(xy.1, xy.2)) (by
      intro e he
      obtain ⟨⟨a, b⟩, -, rfl⟩ := mem_image.1 he
      calc #((ordNonEdgesIn G W).filter (fun xy : V × V => s(xy.1, xy.2) = s(a, b)))
          ≤ #({(a, b), (b, a)} : Finset (V × V)) := by
            apply card_le_card
            intro xy hxy
            rw [mem_filter] at hxy
            rcases Sym2.eq_iff.1 hxy.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · simp [Prod.ext_iff, h1, h2]
            · simp [Prod.ext_iff, h1, h2]
        _ ≤ 2 := card_le_two)
  have h2 : (ordNonEdgesIn G W).image (fun xy : V × V => s(xy.1, xy.2)) ⊆ nonEdgesIn G W := by
    intro e he
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := mem_image.1 he
    simp only [ordNonEdgesIn, mem_filter, mem_product] at hab
    simp only [nonEdgesIn, mem_filter, Finset.mk_mem_sym2_iff, Sym2.mk_isDiag_iff,
      SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact ⟨⟨hab.1.1, hab.1.2⟩, hab.2.1, hab.2.2⟩
  calc #(ordNonEdgesIn G W) ≤ 2 * #((ordNonEdgesIn G W).image
        (fun xy : V × V => s(xy.1, xy.2))) := h1
    _ ≤ 2 * #(nonEdgesIn G W) := by gcongr

variable (G) in
/-- The non-conflict graph on the matching: two matching non-edges are adjacent when
all four cross pairs are edges of `G`. -/
def joinGraph (M : Finset (V × V)) : SimpleGraph M where
  Adj p q := p ≠ q ∧ ∀ x ∈ pairVerts p.1, ∀ y ∈ pairVerts q.1, G.Adj x y
  symm := fun _ _ h => ⟨h.1.symm, fun x hx y hy => (h.2 y hy x hx).symm⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

omit [Fintype V] in
theorem joinGraph_cliqueFree {s : ℕ} (hG : RootedDefectAt G s) {W : Finset V}
    {M : Finset (V × V)} (hM : IsNonEdgeMatching G W M) :
    (joinGraph G M).CliqueFree (s + 2) := by
  intro t ht
  classical
  refine false_of_joined_matching hG (T := t.map (Function.Embedding.subtype _)) ?_ ?_ ?_ ?_
  · intro p hp
    obtain ⟨a, -, rfl⟩ := mem_map.1 hp
    exact ⟨(hM.1 a.1 a.2).2.2.1, (hM.1 a.1 a.2).2.2.2⟩
  · refine hM.2.subset ?_
    intro p hp
    obtain ⟨a, -, rfl⟩ := mem_map.1 (mem_coe.1 hp)
    exact a.2
  · rw [card_map, ht.card_eq]
  · intro p hp q hq hpq
    obtain ⟨a, ha, rfl⟩ := mem_map.1 hp
    obtain ⟨b, hb, rfl⟩ := mem_map.1 hq
    have hab : a ≠ b := fun h => hpq (h ▸ rfl)
    exact (ht.isClique ha hb hab).2

omit [Fintype V] in
theorem sum_lower_le_card_ordNonEdgesIn {W : Finset V} {M : Finset (V × V)}
    (hM : IsNonEdgeMatching G W M) [DecidableRel (joinGraph G M).Adj] :
    ∑ pq : M × M, (if pq.1 = pq.2 then 2 else if (joinGraph G M).Adj pq.1 pq.2 then 0 else 1)
      ≤ #(ordNonEdgesIn G W) := by
  classical
  set g : M × M → Finset (V × V) := fun pq =>
    (pairVerts pq.1.1 ×ˢ pairVerts pq.2.1).filter (fun xy => xy.1 ≠ xy.2 ∧ ¬ G.Adj xy.1 xy.2)
    with hg
  have hvW : ∀ p ∈ M, pairVerts p ⊆ W := by
    intro p hp x hx
    rcases mem_pairVerts.1 hx with rfl | rfl
    · exact (hM.1 p hp).1
    · exact (hM.1 p hp).2.1
  have hsub : (univ : Finset (M × M)).biUnion g ⊆ ordNonEdgesIn G W := by
    intro xy hxy
    obtain ⟨pq, -, hxy⟩ := mem_biUnion.1 hxy
    rw [hg, mem_filter, mem_product] at hxy
    rw [ordNonEdgesIn, mem_filter, mem_product]
    exact ⟨⟨hvW _ pq.1.2 hxy.1.1, hvW _ pq.2.2 hxy.1.2⟩, hxy.2⟩
  have hdisj : ((univ : Finset (M × M)) : Set (M × M)).PairwiseDisjoint g := by
    intro a _ b _ hab
    simp only [Function.onFun, hg]
    apply Finset.disjoint_filter_filter
    rw [Finset.disjoint_product]
    by_cases h1 : a.1 = b.1
    · right
      have h2 : a.2 ≠ b.2 := fun h2 => hab (Prod.ext h1 h2)
      exact hM.2 a.2.2 b.2.2 (fun h => h2 (Subtype.ext h))
    · left
      exact hM.2 a.1.2 b.1.2 (fun h => h1 (Subtype.ext h))
  have hpt : ∀ pq : M × M,
      (if pq.1 = pq.2 then 2 else if (joinGraph G M).Adj pq.1 pq.2 then 0 else 1) ≤ #(g pq) := by
    rintro ⟨p, q⟩
    have hp := hM.1 p.1 p.2
    by_cases hpq : p = q
    · subst hpq
      simp only [if_true]
      have : ({(p.1.1, p.1.2), (p.1.2, p.1.1)} : Finset (V × V)) ⊆ g (p, p) := by
        intro xy hxy
        simp only [hg, mem_filter, mem_product, mem_insert, mem_singleton] at hxy ⊢
        rcases hxy with rfl | rfl
        · exact ⟨⟨by simp [pairVerts], by simp [pairVerts]⟩, hp.2.2.1,
            hp.2.2.2⟩
        · exact ⟨⟨by simp [pairVerts], by simp [pairVerts]⟩, fun h => hp.2.2.1 h.symm,
            fun h => hp.2.2.2 h.symm⟩
      calc 2 = #({(p.1.1, p.1.2), (p.1.2, p.1.1)} : Finset (V × V)) := by
            rw [card_pair]; intro h; exact hp.2.2.1 (Prod.ext_iff.1 h).1
        _ ≤ _ := card_le_card this
    · simp only [hpq, if_false]
      split_ifs with hadj
      · exact Nat.zero_le _
      · have : ¬ ∀ x ∈ pairVerts p.1, ∀ y ∈ pairVerts q.1, G.Adj x y :=
          fun h => hadj ⟨hpq, h⟩
        push_neg at this
        obtain ⟨x, hx, y, hy, hxy⟩ := this
        have hne : x ≠ y := by
          intro h
          subst h
          exact Finset.disjoint_left.1 (hM.2 p.2 q.2 (fun h => hpq (Subtype.ext h))) hx hy
        rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, card_pos]
        exact ⟨(x, y), by simp only [hg, mem_filter, mem_product]; exact ⟨⟨hx, hy⟩, hne, hxy⟩⟩
  calc _ ≤ ∑ pq : M × M, #(g pq) := sum_le_sum fun pq _ => hpt pq
    _ = #((univ : Finset (M × M)).biUnion g) := (card_biUnion hdisj).symm
    _ ≤ _ := card_le_card hsub

omit [Fintype V] [DecidableRel G.Adj] in
theorem sum_lower_add_card_adj (M : Finset (V × V)) [DecidableRel (joinGraph G M).Adj] :
    (∑ pq : M × M, (if pq.1 = pq.2 then 2 else if (joinGraph G M).Adj pq.1 pq.2 then 0 else 1))
      + 2 * #(joinGraph G M).edgeFinset = #M * #M + #M := by
  classical
  rw [← SimpleGraph.dart_card_eq_twice_card_edges, card_dart_eq_card_filter, card_filter,
    ← sum_add_distrib]
  have hpt : ∀ pq : M × M,
      ((if pq.1 = pq.2 then 2 else if (joinGraph G M).Adj pq.1 pq.2 then 0 else 1) +
        if (joinGraph G M).Adj pq.1 pq.2 then 1 else 0) =
        1 + if pq.1 = pq.2 then 1 else 0 := by
    intro pq
    by_cases h : pq.1 = pq.2
    · simp [h]
    · by_cases ha : (joinGraph G M).Adj pq.1 pq.2 <;> simp [h, ha]
  rw [sum_congr rfl (fun pq _ => hpt pq), sum_add_distrib]
  have e1 : ∑ _pq : M × M, (1 : ℕ) = #M * #M := by simp
  have e2 : ∑ pq : M × M, (if pq.1 = pq.2 then 1 else 0 : ℕ) = #M := by
    rw [Fintype.sum_prod_type]; simp
  rw [e1, e2]

/-! ## Lemma C -/

/-- **Lemma C (clique recovery).**  If `G` has rooted defect `≤ s`, every vertex set `W`
contains a real clique `C` of `G` with `|W| ≤ |C| + 2ν`, where `ν` (the size of a
maximum matching of non-edges inside `W`) satisfies `ν² + (s+1)ν ≤ 2(s+1)·ē(W)`. -/
theorem clique_of_rootedDefect_of_few_nonedges {s : ℕ} (hG : RootedDefectAt G s)
    (W : Finset V) :
    ∃ C ⊆ W, G.IsClique (C : Set V) ∧ ∃ nu : ℕ, #W ≤ #C + 2 * nu ∧
      nu ^ 2 + (s + 1) * nu ≤ 2 * (s + 1) * #(nonEdgesIn G W) := by
  classical
  set cands := (W ×ˢ W).powerset.filter (IsNonEdgeMatching G W) with hcands
  have hne : cands.Nonempty := ⟨∅, by
    rw [hcands, mem_filter]
    exact ⟨empty_mem_powerset _, by simp [IsNonEdgeMatching]⟩⟩
  obtain ⟨M, hMc, hMmax⟩ := exists_max_image cands card hne
  rw [hcands, mem_filter] at hMc
  have hM := hMc.2
  have hmax : ∀ M', IsNonEdgeMatching G W M' → #M' ≤ #M := by
    intro M' hM'
    apply hMmax
    rw [hcands, mem_filter, mem_powerset]
    refine ⟨?_, hM'⟩
    intro p hp
    exact mem_product.2 ⟨(hM'.1 p hp).1, (hM'.1 p hp).2.1⟩
  refine ⟨W \ M.biUnion pairVerts, sdiff_subset, isClique_sdiff_of_maximum hM hmax, #M, ?_, ?_⟩
  · have := card_le_card_sdiff_add_card (s := W) (t := M.biUnion pairVerts)
    rw [card_biUnion_pairVerts hM] at this
    exact this
  · have hA := card_ordNonEdgesIn_le (G := G) W
    have hB := sum_lower_le_card_ordNonEdgesIn hM
    have hC := sum_lower_add_card_adj (G := G) M
    have hD := two_mul_card_edgeFinset_le_of_cliqueFree (joinGraph G M) (r := s + 1)
      (Nat.succ_pos s) (joinGraph_cliqueFree hG hM)
    simp only [Fintype.card_coe, Nat.add_sub_cancel] at hD
    set S := ∑ pq : M × M,
      (if pq.1 = pq.2 then 2 else if (joinGraph G M).Adj pq.1 pq.2 then 0 else 1)
    set e := #(joinGraph G M).edgeFinset
    set nu := #M
    set E := #(nonEdgesIn G W)
    have h1 : (s + 1) * S + (s + 1) * (2 * e) = (s + 1) * (nu * nu + nu) := by
      rw [← mul_add, hC]
    have h2 : (s + 1) * S ≤ 2 * (s + 1) * E := by
      calc (s + 1) * S ≤ (s + 1) * (2 * E) := by gcongr; omega
        _ = 2 * (s + 1) * E := by ring
    nlinarith

/-! ## Lemma B -/

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem mod_eq_ite_of_lt_two_mul {x k : ℕ} (hx : x < 2 * k) :
    x % k = if x < k then x else x - k := by
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

omit [Fintype V] in
/-- **Lemma B (no blow-ups of long cycles).**  Let `k ≥ 4` and let `P 0, …, P (k-1)` be
pairwise disjoint vertex sets, each of size at least `s + 1`, such that `P i` is complete
to `P ((i+1) mod k)` and there are no edges between non-consecutive parts (edges inside
the parts are arbitrary).  Then `G` does not have rooted defect `≤ s`: with
`U = ⋃ P i` and empty root, no vertex of `U` is defect-simplicial. -/
theorem noBlowup_of_rootedDefect {s k : ℕ} (hk : 4 ≤ k) (P : ℕ → Finset V)
    (hcard : ∀ i < k, s + 1 ≤ #(P i))
    (hdisj : ∀ i < k, ∀ j < k, i ≠ j → Disjoint (P i) (P j))
    (hcons : ∀ i < k, ∀ x ∈ P i, ∀ y ∈ P ((i + 1) % k), G.Adj x y)
    (hnon : ∀ i < k, ∀ j < k, i ≠ j → (i + 1) % k ≠ j → (j + 1) % k ≠ i →
      ∀ x ∈ P i, ∀ y ∈ P j, ¬ G.Adj x y) :
    ¬ RootedDefectAt G s := by
  intro hG
  set U := (range k).biUnion P with hU
  have hUne : (U \ ∅).Nonempty := by
    have h0 := hcard 0 (by omega)
    obtain ⟨x, hx⟩ : (P 0).Nonempty := by rw [← card_pos]; omega
    exact ⟨x, by rw [sdiff_empty, hU, mem_biUnion]; exact ⟨0, mem_range.2 (by omega), hx⟩⟩
  obtain ⟨v, hv, C, hCsub, hCcl, hCcard⟩ := hG U ∅ (empty_subset _) (by simp) hUne
  rw [sdiff_empty, hU, mem_biUnion] at hv
  obtain ⟨i, hi, hvi⟩ := hv
  rw [mem_range] at hi
  set a := (i + 1) % k with ha
  set b := (i + k - 1) % k with hb
  have ha' := mod_eq_ite_of_lt_two_mul (x := i + 1) (k := k) (by omega)
  have hb' := mod_eq_ite_of_lt_two_mul (x := i + k - 1) (k := k) (by omega)
  have hak : a < k := Nat.mod_lt _ (by omega)
  have hbk : b < k := Nat.mod_lt _ (by omega)
  have ha1 := mod_eq_ite_of_lt_two_mul (x := a + 1) (k := k) (by omega)
  have hb1 := mod_eq_ite_of_lt_two_mul (x := b + 1) (k := k) (by omega)
  rw [← ha] at ha'
  rw [← hb] at hb'
  have hbi : (b + 1) % k = i := by
    rw [hb1]; split_ifs at hb' hb1 ⊢ <;> omega
  have hab : a ≠ b := by split_ifs at ha' hb' <;> omega
  have hab1 : (a + 1) % k ≠ b := by
    rw [ha1]; split_ifs at ha' hb' ha1 ⊢ <;> omega
  have hba1 : (b + 1) % k ≠ a := by
    rw [hbi]; split_ifs at ha' <;> omega
  -- a part complete to `v` and disjoint from `C` is too large
  have key : ∀ c < k, (∀ y ∈ P c, G.Adj v y) → Disjoint C (P c) → False := by
    intro c hc hadj hdC
    have hsub : C ∪ P c ⊆ neighborsIn G U v := by
      intro y hy
      rcases mem_union.1 hy with hy | hy
      · exact hCsub hy
      · simp only [neighborsIn, mem_filter, hU, mem_biUnion, mem_range]
        exact ⟨⟨c, hc, hy⟩, hadj y hy⟩
    have := card_le_card hsub
    rw [card_union_of_disjoint hdC] at this
    have := hcard c hc
    omega
  by_cases hdA : Disjoint C (P a)
  · exact key a hak (fun y hy => hcons i hi v hvi y hy) hdA
  · apply key b hbk (fun y hy => (hcons b hbk y hy v (hbi ▸ hvi)).symm)
    rw [Finset.disjoint_left]
    intro y hyC hyb
    rw [Finset.not_disjoint_iff] at hdA
    obtain ⟨x, hxC, hxa⟩ := hdA
    have hxy : x ≠ y := by
      rintro rfl
      exact Finset.disjoint_left.1 (hdisj a hak b hbk hab) hxa hyb
    exact hnon a hak b hbk hab hab1 hba1 x hxa y hyb (hCcl hxC hyC hxy)

end PaperIV.EditRoute

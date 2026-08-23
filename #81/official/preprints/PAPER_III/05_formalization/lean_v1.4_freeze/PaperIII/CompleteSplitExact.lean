import PaperIII.Addenda
import PaperIII.CliquePartition
import PaperIII.Counting

/-!
# Complete-split exact clique-partition benchmark

This module proves the lower half of the exact value for the complete-split family
`K_p ∨ K̄_{2p}`.  The proof is the standard edge-weight argument: give every cross
edge weight `+1` and every clique edge weight `-1`; each clique block has total weight
at most `1`, while the whole graph has weight `2p² - C(p,2)`.
-/

namespace PaperIII

open SplitGraph Finset
open scoped Classical

private def csCovered {p : ℕ} (c : Finset (completeSplit p).V)
    (e : Sym2 (completeSplit p).V) : Bool :=
  decide (e.toFinset ⊆ c)

private def csLeftSet (p : ℕ) (c : Finset (completeSplit p).V) : Finset (Fin p) :=
  Finset.univ.filter fun a => Sum.inl a ∈ c

private def csRightSet (p : ℕ) (c : Finset (completeSplit p).V) : Finset (Fin (2 * p)) :=
  Finset.univ.filter fun i => Sum.inr i ∈ c

private def csEdgeWeight (p : ℕ) (e : Sym2 (completeSplit p).V) : ℤ :=
  if e ∈ (completeSplit p).crossEdges then 1 else -1

private def csBlockWeight (p : ℕ) (c : Finset (completeSplit p).V) : ℤ :=
  ∑ e ∈ (completeSplit p).graph.edgeFinset,
    if csCovered c e then csEdgeWeight p e else 0

private lemma csCovered_iff {p : ℕ} (c : Finset (completeSplit p).V)
    (e : Sym2 (completeSplit p).V) :
    csCovered c e = true ↔ ∀ v ∈ e, v ∈ c := by
  simp [csCovered, Finset.subset_iff]

private lemma csEdgeWeight_cross (p : ℕ) (a : Fin p) (i : Fin (2 * p)) :
    csEdgeWeight p s(Sum.inl a, Sum.inr i) = 1 := by
  simp [csEdgeWeight, completeSplit, SplitGraph.crossEdges]

private lemma csEdgeWeight_clique (p : ℕ) (e : Sym2 (Fin p)) :
    csEdgeWeight p (e.map Sum.inl) = -1 := by
  simp [csEdgeWeight, completeSplit, SplitGraph.crossEdges]
  intro a b h
  revert h
  refine Sym2.ind ?_ e
  intro x y h
  rw [Sym2.map_pair_eq, Sym2.eq_iff] at h
  rcases h with h | h <;> simp at h

private lemma csCovered_cross (p : ℕ) (c : Finset (completeSplit p).V) (a : Fin p)
    (i : Fin (2 * p)) :
    csCovered c s(Sum.inl a, Sum.inr i) = true ↔ Sum.inl a ∈ c ∧ Sum.inr i ∈ c := by
  simp [csCovered, Finset.subset_iff, Sym2.toFinset, Sym2.toMultiset]

private lemma csCovered_map_inl (p : ℕ) (c : Finset (completeSplit p).V) (e : Sym2 (Fin p)) :
    csCovered c (e.map Sum.inl) = true ↔ ∀ v ∈ e, Sum.inl v ∈ c := by
  revert e
  refine Sym2.ind ?_
  intro a b
  simp [csCovered, Finset.subset_iff, Sym2.toFinset, Sym2.toMultiset, Sym2.map_pair_eq]

private lemma cs_right_card_le_one (p : ℕ) (c : Finset (completeSplit p).V)
    (hc : (completeSplit p).graph.IsClique (c : Set (completeSplit p).V)) :
    (csRightSet p c).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro i hi j hj
  have hci : (Sum.inr i : (completeSplit p).V) ∈ c := by simpa [csRightSet] using hi
  have hcj : (Sum.inr j : (completeSplit p).V) ∈ c := by simpa [csRightSet] using hj
  by_contra hne
  rw [SimpleGraph.isClique_iff] at hc
  have hPair := hc hci hcj ?_
  · simpa [completeSplit, SplitGraph.graph, SplitGraph.Adj] using hPair
  · intro hEq
    apply hne
    exact Sum.inr.inj hEq

private lemma cs_cross_sum (p : ℕ) (c : Finset (completeSplit p).V) :
    (∑ i : Fin (2 * p), ∑ a : Fin p,
      (if csCovered c s(Sum.inl a, Sum.inr i) then (1 : ℤ) else 0))
      = ((csLeftSet p c).card * (csRightSet p c).card : ℕ) := by
  classical
  rw [Finset.sum_comm]
  have hinner : ∀ a : Fin p,
      (∑ i : Fin (2 * p), if Sum.inl a ∈ c ∧ Sum.inr i ∈ c then (1 : ℤ) else 0)
        = if Sum.inl a ∈ c then ((csRightSet p c).card : ℤ) else 0 := by
    intro a
    by_cases ha : Sum.inl a ∈ c
    · simp [ha, csRightSet]
    · simp [ha]
  calc
    (∑ a : Fin p, ∑ i : Fin (2 * p), if csCovered c s(Sum.inl a, Sum.inr i) then
        (1 : ℤ) else 0)
        = ∑ a : Fin p, if Sum.inl a ∈ c then ((csRightSet p c).card : ℤ) else 0 := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [← hinner a]
          simp [csCovered_cross]
    _ = ((csLeftSet p c).card : ℤ) * ((csRightSet p c).card : ℤ) := by
          rw [← Finset.sum_filter]
          simp [csLeftSet]
    _ = ((csLeftSet p c).card * (csRightSet p c).card : ℕ) := by norm_num

private lemma cs_clique_sum (p : ℕ) (c : Finset (completeSplit p).V) :
    (∑ e ∈ (⊤ : SimpleGraph (Fin p)).edgeFinset,
      (if csCovered c (e.map Sum.inl) then (-1 : ℤ) else 0))
      = -(((csLeftSet p c).card.choose 2 : ℕ) : ℤ) := by
  classical
  have hfilter :
      ((⊤ : SimpleGraph (Fin p)).edgeFinset.filter fun e => csCovered c (e.map Sum.inl) = true)
        = ((⊤ : SimpleGraph (Fin p)).edgeFinset.filter fun e => ∀ v ∈ e, v ∈ csLeftSet p c) := by
    ext e
    simp [csCovered_map_inl, csLeftSet]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [hfilter]
  have hcard := card_top_edges_within (csLeftSet p c)
  change (((⊤ : SimpleGraph (Fin p)).edgeFinset.filter fun e => ∀ v ∈ e, v ∈ csLeftSet p c).card : ℤ) * -1 =
    -(((csLeftSet p c).card.choose 2 : ℕ) : ℤ)
  norm_num [← hcard]
  congr 1
  ext e
  simp

private lemma csBlockWeight_eq (p : ℕ) (c : Finset (completeSplit p).V) :
    csBlockWeight p c =
      ((csLeftSet p c).card * (csRightSet p c).card : ℕ) -
        ((csLeftSet p c).card.choose 2 : ℕ) := by
  classical
  unfold csBlockWeight
  rw [SplitGraph.sum_edgeFinset]
  have hleft :
      (∑ e ∈ (⊤ : SimpleGraph (Fin p)).edgeFinset,
        (if csCovered c (e.map Sum.inl) then csEdgeWeight p (e.map Sum.inl) else 0)) =
      ∑ e ∈ (⊤ : SimpleGraph (Fin p)).edgeFinset,
        (if csCovered c (e.map Sum.inl) then (-1 : ℤ) else 0) := by
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [csEdgeWeight_clique]
  have hcross :
      (∑ i : Fin (completeSplit p).q, ∑ a ∈ (completeSplit p).N i,
        (if csCovered c s(Sum.inl a, Sum.inr i) then csEdgeWeight p s(Sum.inl a, Sum.inr i) else 0)) =
      ∑ i : Fin (2 * p), ∑ a : Fin p,
        (if csCovered c s(Sum.inl a, Sum.inr i) then (1 : ℤ) else 0) := by
    change (∑ i : Fin (2 * p), ∑ a ∈ (Finset.univ : Finset (Fin p)),
        (if csCovered c s(Sum.inl a, Sum.inr i) then csEdgeWeight p s(Sum.inl a, Sum.inr i) else 0)) =
      ∑ i : Fin (2 * p), ∑ a : Fin p,
        (if csCovered c s(Sum.inl a, Sum.inr i) then (1 : ℤ) else 0)
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [csEdgeWeight_cross]
  calc
    ((∑ e ∈ (⊤ : SimpleGraph (Fin p)).edgeFinset,
        (if csCovered c (e.map Sum.inl) then csEdgeWeight p (e.map Sum.inl) else 0)) +
      ∑ i : Fin (completeSplit p).q, ∑ a ∈ (completeSplit p).N i,
        (if csCovered c s(Sum.inl a, Sum.inr i) then csEdgeWeight p s(Sum.inl a, Sum.inr i) else 0))
        = (∑ e ∈ (⊤ : SimpleGraph (Fin p)).edgeFinset,
            (if csCovered c (e.map Sum.inl) then (-1 : ℤ) else 0)) +
          ∑ i : Fin (2 * p), ∑ a : Fin p,
            (if csCovered c s(Sum.inl a, Sum.inr i) then (1 : ℤ) else 0) := by
          rw [hleft, hcross]
    _ = ((csLeftSet p c).card * (csRightSet p c).card : ℕ) -
        ((csLeftSet p c).card.choose 2 : ℕ) := by
          rw [cs_clique_sum, cs_cross_sum]
          ring

private lemma nat_le_choose_two_add_one_of_three_le (n : ℕ) (h : 3 ≤ n) :
    n ≤ n.choose 2 + 1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.choose_two_right]
  rw [← Nat.sub_le_iff_le_add]
  rw [Nat.le_div_iff_mul_le (by omega : 0 < 2)]
  nlinarith

private lemma csBlockWeight_le_one (p : ℕ) (c : Finset (completeSplit p).V)
    (hc : (completeSplit p).graph.IsClique (c : Set (completeSplit p).V)) :
    csBlockWeight p c ≤ 1 := by
  classical
  rw [csBlockWeight_eq]
  have hr := cs_right_card_le_one p c hc
  interval_cases hrc : (csRightSet p c).card
  · simp
  · simp
    have hcases : (csLeftSet p c).card ≤ 2 ∨ 3 ≤ (csLeftSet p c).card := by omega
    rcases hcases with hle | hge
    · interval_cases (csLeftSet p c).card <;> norm_num
    · have hnat := nat_le_choose_two_add_one_of_three_le (csLeftSet p c).card hge
      have hint : ((csLeftSet p c).card : ℤ) ≤
          (((csLeftSet p c).card.choose 2 : ℕ) : ℤ) + 1 := by
        exact_mod_cast hnat
      linarith

private lemma csBlockWeight_univ (p : ℕ) :
    csBlockWeight p Finset.univ = (2 * p * p : ℤ) - (p.choose 2 : ℤ) := by
  rw [csBlockWeight_eq]
  simp [csLeftSet, csRightSet]
  ring

private lemma cs_partition_sum_eq_total (p : ℕ) {P : Finset (Finset (completeSplit p).V)}
    (hcover : ∀ e ∈ (completeSplit p).graph.edgeFinset,
      ∃! c, c ∈ P ∧ ∀ v ∈ e, v ∈ c) :
    (∑ c ∈ P, csBlockWeight p c) = csBlockWeight p Finset.univ := by
  classical
  unfold csBlockWeight
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e he => ?_
  obtain ⟨c₀, hc₀, huniq⟩ := hcover e he
  calc
    (∑ c ∈ P, if csCovered c e then csEdgeWeight p e else 0) = csEdgeWeight p e := by
      rw [Finset.sum_eq_single c₀]
      · have hcov₀ : csCovered c₀ e = true := (csCovered_iff c₀ e).mpr hc₀.2
        simp [hcov₀]
      · intro c hcP hne
        have hnot : csCovered c e ≠ true := by
          intro hcov
          have hcProp : c ∈ P ∧ ∀ v ∈ e, v ∈ c := ⟨hcP, (csCovered_iff c e).mp hcov⟩
          exact hne (huniq c hcProp)
        simp [hnot]
      · intro hcnot
        exact False.elim (hcnot hc₀.1)
    _ = (if csCovered (Finset.univ : Finset (completeSplit p).V) e then csEdgeWeight p e else 0) := by
      simp [csCovered]

private lemma cs_partition_total_le_card (p : ℕ) {P : Finset (Finset (completeSplit p).V)}
    (hclique : ∀ c ∈ P, (completeSplit p).graph.IsClique (c : Set (completeSplit p).V))
    (hcover : ∀ e ∈ (completeSplit p).graph.edgeFinset,
      ∃! c, c ∈ P ∧ ∀ v ∈ e, v ∈ c) :
    csBlockWeight p Finset.univ ≤ (P.card : ℤ) := by
  rw [← cs_partition_sum_eq_total p hcover]
  calc
    (∑ c ∈ P, csBlockWeight p c) ≤ ∑ c ∈ P, (1 : ℤ) := by
      exact Finset.sum_le_sum fun c hc => csBlockWeight_le_one p c (hclique c hc)
    _ = (P.card : ℤ) := by simp

private lemma edge_singletons_clique_partition (G : SplitGraph) :
    ∃ P : Finset (Finset G.V),
      (∀ c ∈ P, G.graph.IsClique (c : Set G.V)) ∧
      P.card = G.edgeCount ∧
      ∀ e ∈ G.graph.edgeFinset, ∃! c, c ∈ P ∧ ∀ v ∈ e, v ∈ c := by
  classical
  refine ⟨G.graph.edgeFinset.image (fun e => e.toFinset), ?_, ?_, ?_⟩
  · intro c hc
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hc
    revert he
    refine Sym2.ind (fun x y he => ?_) e
    rw [SimpleGraph.isClique_iff]
    intro a ha b hb hne
    have hxy : G.graph.Adj x y := by simpa [SimpleGraph.mem_edgeFinset] using he
    have ha' : a = x ∨ a = y := by simpa [Sym2.mem_iff] using ha
    have hb' : b = x ∨ b = y := by simpa [Sym2.mem_iff] using hb
    rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
    · exact False.elim (hne rfl)
    · exact hxy
    · exact hxy.symm
    · exact False.elim (hne rfl)
  · rw [SplitGraph.edgeCount, Finset.card_image_of_injOn]
    intro e he e' he' h
    cases e
    cases e'
    simp_all +decide [Sym2.ext_iff, Finset.ext_iff]
  · intro e he
    refine ⟨e.toFinset, ?_, ?_⟩
    · constructor
      · exact Finset.mem_image.mpr ⟨e, he, rfl⟩
      · intro v hv
        simpa using hv
    · intro c hc
      obtain ⟨e', he', rfl⟩ := Finset.mem_image.mp hc.1
      revert hc
      revert he he'
      refine Sym2.ind (fun x y he => ?_) e
      refine Sym2.ind (fun x' y' he' hc => ?_) e'
      have hxy : G.graph.Adj x y := by simpa [SimpleGraph.mem_edgeFinset] using he
      have hx'y' : G.graph.Adj x' y' := by simpa [SimpleGraph.mem_edgeFinset] using he'
      have hx : x ∈ s(x, y) := by simp [Sym2.mem_iff]
      have hy : y ∈ s(x, y) := by simp [Sym2.mem_iff]
      have hxmem : x = x' ∨ x = y' := by simpa [Sym2.mem_iff] using hc.2 x hx
      have hymem : y = x' ∨ y = y' := by simpa [Sym2.mem_iff] using hc.2 y hy
      rcases hxmem with rfl | rfl <;> rcases hymem with rfl | rfl
      · exact False.elim (G.graph.loopless hx'y')
      · simp [Sym2.toFinset, Sym2.toMultiset]
      · ext z
        simp [eq_comm, or_comm]
      · exact False.elim (G.graph.loopless hx'y')

private lemma cs_cp_feasible_nonempty (p : ℕ) :
    ({k | ∃ P : Finset (Finset (completeSplit p).V),
      (∀ c ∈ P, (completeSplit p).graph.IsClique (c : Set (completeSplit p).V)) ∧
      P.card = k ∧
      ∀ e ∈ (completeSplit p).graph.edgeFinset, ∃! c, c ∈ P ∧ ∀ v ∈ e, v ∈ c} :
        Set ℕ).Nonempty := by
  obtain ⟨P, hP⟩ := edge_singletons_clique_partition (completeSplit p)
  exact ⟨(completeSplit p).edgeCount, ⟨P, hP.1, hP.2.1, hP.2.2⟩⟩

private lemma cs_feasible_card_lower (p : ℕ) {k : ℕ}
    (hk : k ∈ {k | ∃ P : Finset (Finset (completeSplit p).V),
      (∀ c ∈ P, (completeSplit p).graph.IsClique (c : Set (completeSplit p).V)) ∧
      P.card = k ∧
      ∀ e ∈ (completeSplit p).graph.edgeFinset, ∃! c, c ∈ P ∧ ∀ v ∈ e, v ∈ c}) :
    (2 * p * p : ℤ) - (p.choose 2 : ℤ) ≤ (k : ℤ) := by
  obtain ⟨P, hclique, hcard, hcover⟩ := hk
  calc
    (2 * p * p : ℤ) - (p.choose 2 : ℤ) = csBlockWeight p Finset.univ := by
      rw [csBlockWeight_univ]
    _ ≤ (P.card : ℤ) := cs_partition_total_le_card p hclique hcover
    _ = (k : ℤ) := by rw [hcard]

/-- Exact lower bound for the complete-split benchmark:
every clique partition of `K_p ∨ K̄_{2p}` has at least `2p² - C(p,2)` blocks. -/
theorem Byproduct_completeSplit_cp_ge_exact_value (p : ℕ) :
    (2 * p * p : ℤ) - (p.choose 2 : ℤ) ≤ ((completeSplit p).cp : ℤ) := by
  classical
  unfold SplitGraph.cp
  let S : Set ℕ := {k | ∃ P : Finset (Finset (completeSplit p).V),
      (∀ c ∈ P, (completeSplit p).graph.IsClique (c : Set (completeSplit p).V)) ∧
      P.card = k ∧
      ∀ e ∈ (completeSplit p).graph.edgeFinset, ∃! c, c ∈ P ∧ ∀ v ∈ e, v ∈ c}
  have hmem : sInf S ∈ S := Nat.sInf_mem (cs_cp_feasible_nonempty p)
  exact cs_feasible_card_lower p hmem

end PaperIII

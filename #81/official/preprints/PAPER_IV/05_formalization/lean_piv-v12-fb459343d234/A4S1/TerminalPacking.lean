import PaperIV.LiftedHostingAssembly

/-!
# Terminal packing infrastructure

General tools for the terminal constructions of `A4_S1_TERMINAL_QUANTITATIVE_20260924.md`:

* `exists_partition_of_triangles` — a family of pairwise edge-disjoint triangles of `G`
  (real cliques of order three, pairwise sharing at most one vertex) completes to a clique
  partition of order at most four with `|Q| + 2|T| = e(G)`;
* `inEdges`, `crossCount` and `card_inEdges_union` — the split of the edges of a vertex set
  `C ⊔ H` into the edges inside `C`, the `C`–`H` links and the edges inside `H`;
* `edgeFinset_card_le_of_independent` — **the valuable-edge lower bound**: if `V = C ⊔ H`
  and `H` is independent, every clique partition (of any order) has
  `e(G) ≤ |Q| + 2 e(G[C])`;
* `hostedTriangles` and its properties — hosting every edge of `G[C]` by a triangle through
  an exterior host, from a symmetric proper host assignment.
-/

namespace A4S1.TerminalPacking

open Finset PaperIV.FarRounding PaperIV.LiftedPieces

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ## 1. Triangle families complete to clique partitions -/

/-- **Packing of triangles.**  A family of triangles of `G` pairwise sharing at most one
vertex completes to a clique partition of order at most four of size `e(G) − 2|T|`. -/
theorem exists_partition_of_triangles (T : Finset (Finset V))
    (hclique : ∀ K ∈ T, ∀ a ∈ K, ∀ b ∈ K, a ≠ b → G.Adj a b)
    (hcard : ∀ K ∈ T, K.card = 3)
    (hinter : ∀ K ∈ T, ∀ L ∈ T, K ≠ L → (K ∩ L).card ≤ 1) :
    ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size + 2 * T.card = G.edgeFinset.card := by
  let P : Packing G :=
    { pieces := T
      isItem := fun K hK => ⟨hclique K hK, Or.inl (hcard K hK)⟩
      edgeDisjoint := fun K hK L hL hKL => (disjoint_pairs_iff K L).2 (hinter K hK L hL hKL) }
  obtain ⟨Q, hQ4, hQ⟩ := exists_cliquePartition_of_packing P
  refine ⟨Q, hQ4, ?_⟩
  have hgain : P.gain = 2 * T.card := by
    change ∑ K ∈ T, gainOf K = 2 * T.card
    rw [Finset.sum_congr rfl (fun K hK => gainOf_of_card_eq_three (hcard K hK))]
    simp [mul_comm]
  omega

/-! ## 2. Splitting the edge set -/

variable (G) in
/-- The edges of `G` with both ends in `S`. -/
def inEdges (S : Finset V) : Finset (Sym2 V) := G.edgeFinset.filter fun e => ∀ v ∈ e, v ∈ S

variable (G) in
/-- The number of links of `G` between `C` and `H` (ordered as `C × H`). -/
def crossCount (C H : Finset V) : ℕ := ((C ×ˢ H).filter fun p => G.Adj p.1 p.2).card

theorem mk_mem_inEdges {S : Finset V} {a b : V} :
    s(a, b) ∈ inEdges G S ↔ G.Adj a b ∧ a ∈ S ∧ b ∈ S := by
  simp [inEdges]

theorem inEdges_univ : inEdges G univ = G.edgeFinset := by
  ext e; simp [inEdges]

/-- **The split.**  For disjoint `C, H`, the edges inside `C ∪ H` are the edges inside `C`,
the `C`–`H` links and the edges inside `H`. -/
theorem card_inEdges_union {C H : Finset V} (hCH : Disjoint C H) :
    (inEdges G (C ∪ H)).card =
      (inEdges G C).card + crossCount G C H + (inEdges G H).card := by
  set E := inEdges G (C ∪ H)
  set X := E.filter (fun e => ¬ (∀ v ∈ e, v ∈ C) ∧ ¬ (∀ v ∈ e, v ∈ H)) with hX
  have hsplit1 := Finset.card_filter_add_card_filter_not (s := E) (fun e => ∀ v ∈ e, v ∈ C)
  have hsplit2 := Finset.card_filter_add_card_filter_not
    (s := E.filter (fun e => ¬ ∀ v ∈ e, v ∈ C)) (fun e => ∀ v ∈ e, v ∈ H)
  have h1 : E.filter (fun e => ∀ v ∈ e, v ∈ C) = inEdges G C := by
    ext e
    simp only [E, inEdges, mem_filter, mem_union]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨⟨h1, fun v hv => Or.inl (h3 v hv)⟩, h3⟩
  have h2 : (E.filter (fun e => ¬ ∀ v ∈ e, v ∈ C)).filter (fun e => ∀ v ∈ e, v ∈ H) =
      inEdges G H := by
    ext e
    simp only [E, inEdges, mem_filter, mem_union]
    constructor
    · rintro ⟨⟨⟨h1, _⟩, _⟩, h4⟩; exact ⟨h1, h4⟩
    · rintro ⟨h1, h4⟩
      refine ⟨⟨⟨h1, fun v hv => Or.inr (h4 v hv)⟩, ?_⟩, h4⟩
      intro hC
      induction e using Sym2.ind with
      | _ a b =>
        exact Finset.disjoint_left.1 hCH (hC a (Sym2.mem_mk_left a b)) (h4 a (Sym2.mem_mk_left a b))
  have h3 : ((E.filter (fun e => ¬ ∀ v ∈ e, v ∈ C)).filter
      (fun e => ¬ ∀ v ∈ e, v ∈ H)).card = crossCount G C H := by
    symm
    apply Finset.card_nbij (fun p => s(p.1, p.2))
    · intro p hp
      simp only [coe_filter, Set.mem_setOf_eq, mem_product] at hp
      obtain ⟨⟨hpC, hpH⟩, hadj⟩ := hp
      simp only [E, inEdges, coe_filter, Set.mem_setOf_eq, mem_filter, SimpleGraph.mem_edgeFinset,
        SimpleGraph.mem_edgeSet, Sym2.mem_iff, mem_union, forall_eq_or_imp, forall_eq]
      refine ⟨⟨⟨hadj, Or.inl hpC, Or.inr hpH⟩, ?_⟩, ?_⟩
      · rintro ⟨_, h⟩; exact Finset.disjoint_left.1 hCH h hpH
      · rintro ⟨h, _⟩; exact Finset.disjoint_left.1 hCH hpC h
    · intro p hp q hq hpq
      simp only [coe_filter, Set.mem_setOf_eq, mem_product] at hp hq
      simp only at hpq
      rcases Sym2.eq_iff.1 hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Prod.ext h1 h2
      · exact absurd (h1 ▸ hp.1.1) (Finset.disjoint_left.1 hCH |>.mt (by simpa using hq.1.2))
    · intro e he
      induction e using Sym2.ind with
      | _ a b =>
        simp only [E, inEdges, coe_filter, Set.mem_setOf_eq, mem_filter,
          SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, Sym2.mem_iff, mem_union,
          forall_eq_or_imp, forall_eq, not_and_or] at he
        obtain ⟨⟨⟨hab, ha, hb⟩, hnC⟩, hnH⟩ := he
        simp only [coe_filter, Set.mem_image, Set.mem_setOf_eq, mem_product]
        have haH : a ∈ C → a ∉ H := fun h => Finset.disjoint_left.1 hCH h
        have hbH : b ∈ C → b ∉ H := fun h => Finset.disjoint_left.1 hCH h
        rcases ha with ha | ha <;> rcases hb with hb | hb
        · exact absurd (Or.inl (not_not.2 ha)) (by tauto)
        · exact ⟨(a, b), ⟨⟨ha, hb⟩, hab⟩, rfl⟩
        · exact ⟨(b, a), ⟨⟨hb, ha⟩, hab.symm⟩, Sym2.eq_swap⟩
        · exact absurd (Or.inl (not_not.2 ha)) (by tauto)
  rw [h1] at hsplit1
  rw [h2, h3] at hsplit2
  omega

/-- The clique case: the edges inside a clique are all its pairs. -/
theorem card_inEdges_of_isClique {S : Finset V} (hS : G.IsClique (S : Set V)) :
    (inEdges G S).card = S.card.choose 2 := by
  rw [← card_pairs]
  congr 1
  ext e
  induction e using Sym2.ind with
  | _ a b =>
    rw [mk_mem_inEdges, mk_mem_pairs]
    constructor
    · rintro ⟨hab, ha, hb⟩; exact ⟨ha, hb, hab.ne⟩
    · rintro ⟨ha, hb, hab⟩; exact ⟨hS ha hb hab, ha, hb⟩

/-- No edge inside an independent set. -/
theorem card_inEdges_of_independent {S : Finset V} (hS : ∀ a ∈ S, ∀ b ∈ S, ¬ G.Adj a b) :
    (inEdges G S).card = 0 := by
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro e he
  induction e using Sym2.ind with
  | _ a b =>
    rw [mk_mem_inEdges] at he
    exact hS a he.2.1 b he.2.2 he.1

/-- The split of the whole edge set along `V = C ⊔ H`. -/
theorem card_edgeFinset_split {C H : Finset V} (hCH : Disjoint C H) (hcov : C ∪ H = univ) :
    G.edgeFinset.card = (inEdges G C).card + crossCount G C H + (inEdges G H).card := by
  rw [← inEdges_univ, ← hcov, card_inEdges_union hCH]

/-! ## 3. The valuable-edge lower bound -/

private lemma le_one_add_choose (t : ℕ) : t ≤ 1 + t.choose 2 := by
  cases t with
  | zero => simp
  | succ s =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
    omega

/-- **Lower bound for clique partitions of any order.**  If `V = C ⊔ H` with `H`
independent, then every clique partition satisfies `e(G) ≤ |Q| + 2 e(G[C])`: a piece meets
`H` in at most one vertex, so its gain is at most twice the number of edges of `G[C]` it
covers. -/
theorem edgeFinset_card_le_of_independent {C H : Finset V} (hCH : Disjoint C H)
    (hcov : C ∪ H = univ) (hH : ∀ a ∈ H, ∀ b ∈ H, ¬ G.Adj a b) (Q : CliquePartition G) :
    G.edgeFinset.card ≤ Q.size + 2 * (inEdges G C).card := by
  have hdisj : ∀ S : Finset (Sym2 V), (Q.pieces : Set (Finset V)).PairwiseDisjoint
      (fun K => pairs K ∩ S) := by
    intro S K hK L hL hKL
    exact Disjoint.mono inter_subset_left inter_subset_left (Q.edgeDisjoint K hK L hL hKL)
  have htot : ∑ K ∈ Q.pieces, (pairs K).card = G.edgeFinset.card := by
    rw [← Finset.card_biUnion (fun K hK L hL hKL => Q.edgeDisjoint K hK L hL hKL), Q.covers]
  have hC : ∑ K ∈ Q.pieces, (pairs K ∩ inEdges G C).card = (inEdges G C).card := by
    rw [← Finset.card_biUnion (fun K hK L hL hKL => hdisj _ hK hL hKL)]
    congr 1
    rw [← Finset.biUnion_inter, Q.covers]
    exact Finset.inter_eq_right.2 (filter_subset _ _)
  have hpiece : ∀ K ∈ Q.pieces, (pairs K).card ≤ 1 + 2 * (pairs K ∩ inEdges G C).card := by
    intro K hK
    have hKC : pairs K ∩ inEdges G C = pairs (K ∩ C) := by
      ext e
      induction e using Sym2.ind with
      | _ a b =>
        rw [mem_inter, mk_mem_pairs, mk_mem_inEdges, mk_mem_pairs, mem_inter, mem_inter]
        constructor
        · rintro ⟨⟨ha, hb, hab⟩, _, haC, hbC⟩; exact ⟨⟨ha, haC⟩, ⟨hb, hbC⟩, hab⟩
        · rintro ⟨⟨ha, haC⟩, ⟨hb, hbC⟩, hab⟩
          exact ⟨⟨ha, hb, hab⟩, Q.isClique K hK a ha b hb hab, haC, hbC⟩
    have hKH : (K ∩ H).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      by_contra hab
      exact hH a (mem_inter.1 ha).2 b (mem_inter.1 hb).2
        (Q.isClique K hK a (mem_inter.1 ha).1 b (mem_inter.1 hb).1 hab)
    have hsplitK : (K ∩ C).card + (K ∩ H).card = K.card := by
      rw [← Finset.card_union_of_disjoint
        (Disjoint.mono inter_subset_right inter_subset_right hCH), ← Finset.inter_union_distrib_left,
        hcov, inter_univ]
    rw [hKC, card_pairs, card_pairs, ← hsplitK]
    set t := (K ∩ C).card
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hKH with h0 | h1
    · rw [h0, add_zero]; omega
    · have hch : (t + 1).choose 2 = t.choose 2 + t := by
        rw [show (2:ℕ) = 1 + 1 from rfl, Nat.choose_succ_succ', Nat.choose_one_right]; ring
      rw [h1, hch]
      have := le_one_add_choose t
      omega
  calc G.edgeFinset.card = ∑ K ∈ Q.pieces, (pairs K).card := htot.symm
    _ ≤ ∑ K ∈ Q.pieces, (1 + 2 * (pairs K ∩ inEdges G C).card) := Finset.sum_le_sum hpiece
    _ = Q.size + 2 * (inEdges G C).card := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, hC]
      simp [CliquePartition.size]

/-! ## 4. Hosting the edges of `G[C]` -/

variable (G) in
/-- A **host assignment** on `C`: a symmetric choice `c v w` of a host outside `C`, adjacent to
both ends of each edge `vw` of `G[C]`, with distinct hosts on edges sharing an end (a proper
edge colouring of `G[C]` by hosts). -/
def HostAssignment (C : Finset V) (c : V → V → V) : Prop :=
  (∀ v ∈ C, ∀ w ∈ C, G.Adj v w → c v w = c w v) ∧
  (∀ v ∈ C, ∀ w ∈ C, G.Adj v w → c v w ∉ C ∧ G.Adj v (c v w) ∧ G.Adj w (c v w)) ∧
  (∀ v ∈ C, ∀ w ∈ C, ∀ w' ∈ C, G.Adj v w → G.Adj v w' → w ≠ w' → c v w ≠ c v w')

/-- The triangle through an edge `e` of `G[C]` and its host. -/
noncomputable def hostTri (c : V → V → V) (e : Sym2 V) : Finset V :=
  {(Quot.out e).1, (Quot.out e).2, c (Quot.out e).1 (Quot.out e).2}

variable (G) in
/-- The hosted triangles of all edges of `G[C]`. -/
noncomputable def hostedTriangles (C : Finset V) (c : V → V → V) : Finset (Finset V) :=
  (inEdges G C).image (hostTri c)

omit [Fintype V] [DecidableEq V] in
theorem mk_out_eq (e : Sym2 V) : s((Quot.out e).1, (Quot.out e).2) = e := Quot.out_eq e

/-- Every hosted triangle is `{v, w, c v w}` for an edge `vw` of `G[C]`. -/
theorem exists_of_mem_hostedTriangles {C : Finset V} {c : V → V → V} {K : Finset V}
    (hK : K ∈ hostedTriangles G C c) :
    ∃ v w, v ∈ C ∧ w ∈ C ∧ G.Adj v w ∧ K = {v, w, c v w} := by
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hK
  have he' := he
  rw [← mk_out_eq e, mk_mem_inEdges] at he'
  exact ⟨_, _, he'.2.1, he'.2.2, he'.1, rfl⟩

omit [Fintype V] [DecidableRel G.Adj] in
private lemma pair_normal {C : Finset V} {c : V → V → V} (hc : HostAssignment G C c)
    {v w p : V} (hv : v ∈ C) (hw : w ∈ C) (hvw : G.Adj v w) (hp : p = v ∨ p = w) :
    ∃ o ∈ C, G.Adj p o ∧ ({v, w} : Finset V) = {p, o} ∧ c v w = c p o := by
  rcases hp with rfl | rfl
  · exact ⟨w, hw, hvw, rfl, rfl⟩
  · exact ⟨v, hv, hvw.symm, pair_comm _ _, hc.1 v hv p hw hvw⟩

/-- **Hosted triangles are pairwise edge-disjoint.** -/
theorem hostedTriangles_inter {C : Finset V} {c : V → V → V} (hc : HostAssignment G C c)
    {K L : Finset V} (hK : K ∈ hostedTriangles G C c) (hL : L ∈ hostedTriangles G C c)
    (hKL : K ≠ L) : (K ∩ L).card ≤ 1 := by
  obtain ⟨v, w, hv, hw, hvw, rfl⟩ := exists_of_mem_hostedTriangles hK
  obtain ⟨v', w', hv', hw', hvw', rfl⟩ := exists_of_mem_hostedTriangles hL
  have hh := (hc.2.1 v hv w hw hvw).1
  have hh' := (hc.2.1 v' hv' w' hw' hvw').1
  -- elements of the intersection
  have hmem : ∀ p ∈ ({v, w, c v w} : Finset V) ∩ {v', w', c v' w'},
      (p ∈ C ∧ (p = v ∨ p = w) ∧ (p = v' ∨ p = w')) ∨ (p = c v w ∧ p = c v' w') := by
    intro p hp
    simp only [mem_inter, mem_insert, mem_singleton] at hp
    obtain ⟨h1, h2⟩ := hp
    rcases h1 with rfl | rfl | rfl <;> rcases h2 with h2 | h2 | h2
    all_goals first
      | exact Or.inl ⟨by assumption, by tauto, by tauto⟩
      | exact Or.inr ⟨rfl, h2⟩
      | (exfalso; subst h2; contradiction)
  -- same pair gives the same triangle
  have hsame : ({v, w} : Finset V) = {v', w'} → False := by
    intro hpair
    apply hKL
    have hvm : v ∈ ({v', w'} : Finset V) := hpair ▸ (by simp)
    have hwm : w ∈ ({v', w'} : Finset V) := hpair ▸ (by simp)
    simp only [mem_insert, mem_singleton] at hvm hwm
    rcases hvm with rfl | rfl <;> rcases hwm with rfl | rfl
    · exact absurd rfl hvw.ne
    · rfl
    · rw [hc.1 _ hv _ hw hvw]
      ext y; simp only [mem_insert, mem_singleton]; tauto
    · exact absurd rfl hvw.ne
  rw [Finset.card_le_one]
  intro p hp q hq
  by_contra hpq
  rcases hmem p hp with ⟨hpC, hp1, hp2⟩ | ⟨hp1, hp2⟩ <;>
    rcases hmem q hq with ⟨hqC, hq1, hq2⟩ | ⟨hq1, hq2⟩
  · apply hsame
    have hsub : ∀ {x y : V}, x ≠ y → (x = v ∨ x = w) → (y = v ∨ y = w) →
        ({v, w} : Finset V) = {x, y} := by
      intro x y hxy hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact absurd rfl hxy
      · rfl
      · exact pair_comm _ _
      · exact absurd rfl hxy
    have hsub' : ∀ {x y : V}, x ≠ y → (x = v' ∨ x = w') → (y = v' ∨ y = w') →
        ({v', w'} : Finset V) = {x, y} := by
      intro x y hxy hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact absurd rfl hxy
      · rfl
      · exact pair_comm _ _
      · exact absurd rfl hxy
    rw [hsub hpq hp1 hq1, hsub' hpq hp2 hq2]
  · obtain ⟨o, ho, hpo, h1, h2⟩ := pair_normal hc hv hw hvw hp1
    obtain ⟨o', ho', hpo', h1', h2'⟩ := pair_normal hc hv' hw' hvw' hp2
    by_cases hoo : o = o'
    · apply hsame; rw [h1, h1', hoo]
    · exact hc.2.2 p hpC o ho o' ho' hpo hpo' hoo (by rw [← h2, ← h2', ← hq1, hq2])
  · obtain ⟨o, ho, hqo, h1, h2⟩ := pair_normal hc hv hw hvw hq1
    obtain ⟨o', ho', hqo', h1', h2'⟩ := pair_normal hc hv' hw' hvw' hq2
    by_cases hoo : o = o'
    · apply hsame; rw [h1, h1', hoo]
    · exact hc.2.2 q hqC o ho o' ho' hqo hqo' hoo (by rw [← h2, ← h2', ← hp1, hp2])
  · exact hpq (hp1.trans hq1.symm)

/-- Hosted triangles are triangles of `G`. -/
theorem hostedTriangles_isClique {C : Finset V} {c : V → V → V} (hc : HostAssignment G C c)
    {K : Finset V} (hK : K ∈ hostedTriangles G C c) :
    (∀ a ∈ K, ∀ b ∈ K, a ≠ b → G.Adj a b) ∧ K.card = 3 := by
  obtain ⟨v, w, hv, hw, hvw, rfl⟩ := exists_of_mem_hostedTriangles hK
  obtain ⟨hh, hvh, hwh⟩ := hc.2.1 v hv w hw hvw
  refine ⟨?_, ?_⟩
  · intro a ha b hb hab
    simp only [mem_insert, mem_singleton] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
    all_goals first
      | exact absurd rfl hab
      | assumption
      | exact hvw.symm
      | exact hvh.symm
      | exact hwh.symm
  · have h1 : c v w ≠ v := fun h => hh (by rw [h]; exact hv)
    have h2 : c v w ≠ w := fun h => hh (by rw [h]; exact hw)
    rw [Finset.card_insert_of_notMem (by simp [hvw.ne, Ne.symm h1]),
      Finset.card_pair (Ne.symm h2)]

/-- There is one hosted triangle per edge of `G[C]`. -/
theorem card_hostedTriangles {C : Finset V} {c : V → V → V} (hc : HostAssignment G C c) :
    (hostedTriangles G C c).card = (inEdges G C).card := by
  apply Finset.card_image_of_injOn
  intro e he e' he' heq
  have key : ∀ f ∈ inEdges G C, (hostTri c f).filter (· ∈ C) = f.toFinset := by
    intro f hf
    have hf' := hf
    rw [← mk_out_eq f, mk_mem_inEdges] at hf'
    obtain ⟨hadj, h1, h2⟩ := hf'
    have hh := (hc.2.1 _ h1 _ h2 hadj).1
    conv_rhs => rw [← mk_out_eq f]
    rw [Sym2.toFinset_mk_eq]
    ext y
    simp only [hostTri, mem_filter, mem_insert, mem_singleton]
    constructor
    · rintro ⟨h | h | h, hy⟩
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd (h ▸ hy) hh
    · rintro (h | h)
      · exact ⟨Or.inl h, h ▸ h1⟩
      · exact ⟨Or.inr (Or.inl h), h ▸ h2⟩
  have htf : (e : Sym2 V).toFinset = e'.toFinset := by
    rw [← key e he, ← key e' he']
    exact congrArg (fun K => K.filter (· ∈ C)) heq
  have hnd : ∀ f ∈ inEdges G C, ¬ f.IsDiag := fun f hf =>
    G.not_isDiag_of_mem_edgeFinset (mem_filter.1 hf).1
  have := congrArg pairs htf
  rw [pairs_toFinset (hnd e he), pairs_toFinset (hnd e' he')] at this
  exact Finset.singleton_injective this

end A4S1.TerminalPacking

import Mathlib
open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The (off-diagonal) edges spanned by a vertex set `t`. For a 3-clique this is its three edges. -/
def triEdges (t : Finset V) : Finset (Sym2 V) :=
  t.sym2.filter (fun e => ¬ e.IsDiag)

/-- `G` has a **fractional triangle decomposition**: nonnegative weights on the 3-cliques so that
every edge carries total weight exactly `1`. -/
def FractionalTriangleDecomp (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∃ w : Finset V → ℝ, (∀ t, 0 ≤ w t) ∧
    ∀ e ∈ G.edgeFinset,
      (∑ t ∈ G.cliqueFinset 3, if e ∈ triEdges t then w t else 0) = 1

/-- **BLACK BOX — do NOT prove this; use it as given.** The core flow argument, valid when `G` has
no "heavy" triangle (three mutually adjacent vertices each of degree `≥ minDegree + 2`). -/
axiom dross_fractional_flow_noHDT (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : 9 * Fintype.card V ≤ 10 * G.minDegree)
    (δ : ℝ) (hδdef : δ = ((Fintype.card V : ℝ) - G.minDegree) / Fintype.card V)
    (hδ1 : δ < 1/10)
    (hbig : 4 + 2 * (Fintype.card V : ℝ) - 12 * δ * (Fintype.card V : ℝ)
        ≤ (1 - 11 * δ + 10 * δ^2) * (Fintype.card V : ℝ)^2)
    (hNoHDT : ∀ u v w : V, G.Adj u v → G.Adj u w → G.Adj v w →
      G.minDegree + 2 ≤ G.degree u → G.minDegree + 2 ≤ G.degree v →
      G.minDegree + 2 ≤ G.degree w → False) :
    FractionalTriangleDecomp G

private lemma heavy_triangle_vertices_distinct (G : SimpleGraph V) {u v w : V}
    (huv : G.Adj u v) (huw : G.Adj u w) (hvw : G.Adj v w) :
    u ≠ v ∧ u ≠ w ∧ v ≠ w := by
  exact ⟨huv.ne, huw.ne, hvw.ne⟩

private lemma triEdges_heavy_triangle_subset (G : SimpleGraph V) [DecidableRel G.Adj]
    {u v w : V} (huv : G.Adj u v) (huw : G.Adj u w) (hvw : G.Adj v w) :
    triEdges {u, v, w} ⊆ G.edgeFinset := by
  simp only [subset_iff, Sym2.forall, triEdges, mem_filter, mem_sym2_iff,
    mem_insert, mem_singleton, mem_edgeFinset]
  rintro a b ⟨hab, hdiag⟩
  have ha : a = u ∨ a = v ∨ a = w := hab a (by simp)
  have hb : b = u ∨ b = v ∨ b = w := hab b (by simp)
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
    simp_all [SimpleGraph.mem_edgeSet, G.adj_comm]

private lemma triEdges_heavy_triangle_card (G : SimpleGraph V) {u v w : V}
    (huv : G.Adj u v) (huw : G.Adj u w) (hvw : G.Adj v w) :
    #(triEdges {u, v, w}) = 3 := by
  have hne := heavy_triangle_vertices_distinct G huv huw hvw
  have heq : triEdges {u, v, w} = {s(u, v), s(u, w), s(v, w)} := by
    ext e
    induction e using Sym2.inductionOn with | _ a b =>
      simp only [triEdges, mem_filter, mem_sym2_iff, mem_insert, mem_singleton,
        Sym2.mk_isDiag_iff, Sym2.eq_iff]
      aesop
  rw [heq]
  simp [hne.1, hne.2.1, hne.2.2]

private lemma peeled_heavy_triangle_degree_add_two (G : SimpleGraph V) [DecidableRel G.Adj]
    {u v w x : V} :
    G.degree x ≤ (G.deleteEdges (triEdges {u, v, w})).degree x + 2 := by
  rw [← G.card_neighborFinset_eq_degree, ← (G.deleteEdges _).card_neighborFinset_eq_degree]
  let A := (G.deleteEdges (triEdges {u,v,w})).neighborFinset x
  let B := G.neighborFinset x
  have hAB : A ⊆ B := by
    intro y hy
    simp only [B, G.mem_neighborFinset]
    exact (deleteEdges_adj.mp ((G.deleteEdges _).mem_neighborFinset x y |>.mp
      (by simpa [A] using hy))).1
  have hBA : B \ A ⊆ ({u,v,w} : Finset V) := by
    intro y hy
    have hyadj : G.Adj x y := G.mem_neighborFinset x y |>.mp (mem_sdiff.mp hy).1
    simp only [mem_insert, mem_singleton]
    by_contra hn
    have hnot : s(x,y) ∉ triEdges {u,v,w} := by
      intro he
      have hall := (mem_sym2_iff.mp (mem_filter.mp he).1) y (by simp)
      exact hn (by simpa using hall)
    apply (mem_sdiff.mp hy).2
    show y ∈ A
    simp [A, (G.deleteEdges _).mem_neighborFinset, deleteEdges_adj, hyadj, hnot]
  have hcard : #(B \ A) ≤ 2 := by
    by_cases hempty : B \ A = ∅
    · simp [hempty]
    · obtain ⟨y, hy⟩ := nonempty_iff_ne_empty.mpr hempty
      have hxmem : x ∈ ({u,v,w} : Finset V) := by
        have hyadj : G.Adj x y := G.mem_neighborFinset x y |>.mp (mem_sdiff.mp hy).1
        by_contra hx
        have hnot : s(x,y) ∉ triEdges {u,v,w} := by
          intro he
          have hall := (mem_sym2_iff.mp (mem_filter.mp he).1) x (by simp)
          exact hx (by simpa using hall)
        apply (mem_sdiff.mp hy).2
        show y ∈ A
        simp [A, (G.deleteEdges _).mem_neighborFinset, deleteEdges_adj, hyadj, hnot]
      have hsub : B \ A ⊆ ({u,v,w} : Finset V).erase x := by
        intro z hz
        refine mem_erase.mpr ⟨?_, hBA hz⟩
        exact (G.mem_neighborFinset x z |>.mp (mem_sdiff.mp hz).1).ne.symm
      have hc := card_le_card hsub
      have hthree : #({u,v,w} : Finset V) ≤ 3 := by
        calc
          #({u,v,w} : Finset V) ≤ #({v,w} : Finset V) + 1 := card_insert_le _ _
          _ ≤ (#{w} + 1) + 1 := by gcongr; exact card_insert_le _ _
          _ ≤ 3 := by simp
      have herase : #(({u,v,w} : Finset V).erase x) + 1 = #({u,v,w} : Finset V) :=
        card_erase_add_one hxmem
      omega
  rw [← card_sdiff_add_card_inter B A, inter_eq_right.mpr hAB]
  change #(B \ A) + #A ≤ #A + 2
  omega

private lemma peeled_heavy_triangle_minDegree (G : SimpleGraph V) [DecidableRel G.Adj]
    {u v w : V} (hu : G.minDegree + 2 ≤ G.degree u)
    (hv : G.minDegree + 2 ≤ G.degree v)
    (hw : G.minDegree + 2 ≤ G.degree w) :
    (G.deleteEdges (triEdges {u, v, w})).minDegree = G.minDegree := by
  letI : Nonempty V := ⟨u⟩
  apply Nat.le_antisymm
  · exact minDegree_le_minDegree (deleteEdges_le _)
  · apply le_minDegree_of_forall_le_degree
    intro x
    by_cases hx : x = u ∨ x = v ∨ x = w
    · rcases hx with hx | hx | hx
      · have hb := peeled_heavy_triangle_degree_add_two G (u := u) (v := v) (w := w) (x := u)
        subst x
        omega
      · have hb := peeled_heavy_triangle_degree_add_two G (u := u) (v := v) (w := w) (x := v)
        subst x
        omega
      · have hb := peeled_heavy_triangle_degree_add_two G (u := u) (v := v) (w := w) (x := w)
        subst x
        omega
    · have hxu : x ≠ u := fun h => hx (Or.inl h)
      have hxv : x ≠ v := fun h => hx (Or.inr (Or.inl h))
      have hxw : x ≠ w := fun h => hx (Or.inr (Or.inr h))
      have hdeg : (G.deleteEdges (triEdges {u,v,w})).degree x = G.degree x := by
        rw [← G.card_neighborFinset_eq_degree,
          ← (G.deleteEdges _).card_neighborFinset_eq_degree]
        congr 1
        ext y
        simp only [mem_neighborFinset, deleteEdges_adj]
        constructor
        · exact And.left
        · intro hxy
          refine ⟨hxy, ?_⟩
          intro he
          have he' : s(x,y) ∈ (triEdges {u,v,w}) := he
          rw [triEdges, mem_filter] at he'
          have hxmem := (mem_sym2_iff.mp he'.1) x (by simp)
          simp only [mem_insert, mem_singleton] at hxmem
          exact hxmem.elim hxu (fun h => h.elim hxv hxw)
      rw [hdeg]
      exact G.minDegree_le_degree x

private lemma peeled_heavy_triangle_fewer_edges (G : SimpleGraph V) [DecidableRel G.Adj]
    {u v w : V} (huv : G.Adj u v) (huw : G.Adj u w) (hvw : G.Adj v w) :
    (G.deleteEdges (triEdges {u, v, w})).edgeFinset.card < G.edgeFinset.card := by
  have hsub := triEdges_heavy_triangle_subset G huv huw hvw
  have hcard := triEdges_heavy_triangle_card G huv huw hvw
  rw [edgeFinset_deleteEdges, card_sdiff_of_subset hsub]
  apply Nat.sub_lt
  · have := card_le_card hsub
    omega
  · omega

private lemma cliqueFinset_deleteEdges_subset (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Sym2 V)) (n : ℕ) :
    (G.deleteEdges S).cliqueFinset n ⊆ G.cliqueFinset n := by
  intro t ht
  rw [mem_cliqueFinset_iff] at ht ⊢
  exact ht.mono (deleteEdges_le _)

private lemma sum_truncated_cliques (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Sym2 V)) (n : ℕ) (a : Finset V → ℝ) (e : Sym2 V) :
    (∑ t ∈ G.cliqueFinset n,
      if e ∈ triEdges t then (if t ∈ (G.deleteEdges S).cliqueFinset n then a t else 0) else 0) =
    ∑ t ∈ (G.deleteEdges S).cliqueFinset n, if e ∈ triEdges t then a t else 0 := by
  rw [← sum_subset (cliqueFinset_deleteEdges_subset G S n)]
  · apply sum_congr rfl
    intro t ht
    simp [ht]
  · intro t htG htG'
    simp [htG']

private lemma deleted_edge_not_in_clique (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Sym2 V)) {e : Sym2 V} (heS : e ∈ S) {n : ℕ} {t : Finset V}
    (ht : t ∈ (G.deleteEdges S).cliqueFinset n) : e ∉ triEdges t := by
  intro het
  induction e using Sym2.inductionOn with | _ x y =>
    have hmem := mem_filter.mp het
    have hxt := mem_sym2_iff.mp hmem.1 x (by simp)
    have hyt := mem_sym2_iff.mp hmem.1 y (by simp)
    have hxy : x ≠ y := by simpa using hmem.2
    have hc := (mem_cliqueFinset_iff.mp ht).isClique hxt hyt hxy
    exact (deleteEdges_adj.mp hc).2 heS

private lemma triangle_indicator_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    {u v w : V} (huv : G.Adj u v) (huw : G.Adj u w) (hvw : G.Adj v w)
    (e : Sym2 V) :
    (∑ t ∈ G.cliqueFinset 3, if e ∈ triEdges t then (if t = {u,v,w} then (1 : ℝ) else 0) else 0) =
      if e ∈ triEdges {u,v,w} then 1 else 0 := by
  have hT : {u,v,w} ∈ G.cliqueFinset 3 :=
    mem_cliqueFinset_iff.mpr (is3Clique_iff.mpr ⟨u,v,w,huv,huw,hvw,rfl⟩)
  rw [sum_eq_single {u,v,w}]
  · simp
  · intro t ht hne
    simp [hne]
  · intro hnot
    exact (hnot hT).elim

private lemma lift_fractional_decomp_triangle (G : SimpleGraph V) [DecidableRel G.Adj]
    {u v w : V} (huv : G.Adj u v) (huw : G.Adj u w) (hvw : G.Adj v w)
    (hdec : FractionalTriangleDecomp (G.deleteEdges (triEdges {u, v, w}))) :
    FractionalTriangleDecomp G := by
  classical
  let T : Finset V := {u,v,w}
  let G' := G.deleteEdges (triEdges T)
  rcases hdec with ⟨a, ha, hcov⟩
  refine ⟨fun t => (if t ∈ G'.cliqueFinset 3 then a t else 0) +
      (if t = T then 1 else 0), ?_, ?_⟩
  · intro t
    exact add_nonneg (by split <;> simp_all) (by split <;> norm_num)
  · intro e he
    have hsplit :
        (∑ t ∈ G.cliqueFinset 3,
          if e ∈ triEdges t then
            ((if t ∈ G'.cliqueFinset 3 then a t else 0) + (if t = T then 1 else 0)) else 0) =
        (∑ t ∈ G.cliqueFinset 3,
          if e ∈ triEdges t then (if t ∈ G'.cliqueFinset 3 then a t else 0) else 0) +
        (∑ t ∈ G.cliqueFinset 3,
          if e ∈ triEdges t then (if t = T then 1 else 0) else 0) := by
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro t ht
      by_cases het : e ∈ triEdges t <;> simp [het]
    rw [hsplit, sum_truncated_cliques G (triEdges T) 3 a e,
      triangle_indicator_sum G huv huw hvw e]
    by_cases heT : e ∈ triEdges T
    · have hz : (∑ t ∈ G'.cliqueFinset 3, if e ∈ triEdges t then a t else 0) = 0 := by
        apply sum_eq_zero
        intro t ht
        simp [deleted_edge_not_in_clique G (triEdges T) heT ht]
      change (∑ t ∈ G'.cliqueFinset 3, if e ∈ triEdges t then a t else 0) +
        (if e ∈ triEdges T then 1 else 0) = 1
      rw [hz, if_pos heT, zero_add]
    · have heG' : e ∈ G'.edgeFinset := by
        rw [edgeFinset_deleteEdges]
        exact mem_sdiff.mpr ⟨he, heT⟩
      simpa [G', T, heT] using hcov e heG'

/-- **Dross's WLOG heavy-triangle peeling (Theorem 5, p.5, lines 157–162).**

If `G` has a heavy triangle `{u,v,w}` (a 3-clique with `deg u, deg v, deg w ≥ minDegree + 2`), let
`G' = G.deleteEdges (triEdges {u,v,w})` be `G` with those three edges removed. Then:

* `minDegree G' = minDegree G`. (Each of `u,v,w` loses exactly 2 incident edges, so its `G'`-degree
  is `≥ minDegree`; every other vertex keeps its degree. Hence all `G'`-degrees are `≥ minDegree G`,
  giving `minDegree G' ≥ minDegree G`; and the original minimum-degree vertex — which is NOT one of
  `u,v,w`, since those have degree `> minDegree` — keeps its degree, giving `minDegree G' ≤
  minDegree G`.) Consequently `h`, `hδdef`, `hδ1`, `hbig` all transfer verbatim to `G'` (same `n`,
  same `minDegree`, same `δ`).
* `G'.edgeFinset.card = G.edgeFinset.card - 3` (use `edgeFinset_deleteEdges`; the three edges of a
  3-clique are distinct off-diagonal edges, all in `G.edgeFinset`).

By strong induction on `m = G.edgeFinset.card`: if `G` has a heavy triangle, apply the induction
hypothesis to `G'` (fewer edges) and **lift** the decomposition back to `G`; if `G` has no heavy
triangle, `hNoHDT` holds and `dross_fractional_flow_noHDT` finishes directly.

THE LIFT. Given weights `w'` for `G'` (with `∀ t, 0 ≤ w' t` and coverage on `G'.edgeFinset`),
define `w t = (if t ∈ G'.cliqueFinset 3 then w' t else 0) + (if t = {u,v,w} then 1 else 0)`. Then
`w ≥ 0`, and for `e ∈ G.edgeFinset`:
  * if `e ∉ triEdges {u,v,w}` (so `e ∈ G'.edgeFinset`): the `{u,v,w}` term is `0` (as `e ∉ triEdges
    {u,v,w}`), triangles `t ∉ G'.cliqueFinset 3` contribute `0`, and the rest reproduce `G'`'s
    coverage sum `= 1`;
  * if `e ∈ triEdges {u,v,w}` (a restored edge, `e ∉ G'.edgeFinset`): no `G'`-triangle contains `e`
    (they have all edges in `G'`), so only `t = {u,v,w}` contributes, giving `1`.
Note `{u,v,w} ∈ G.cliqueFinset 3` and `e ∈ triEdges {u,v,w}` for each restored `e`, and the three
`triEdges {u,v,w}` are exactly `G.edgeFinset \ G'.edgeFinset`.

Prove this (replace the final `sorry`). You MAY use `dross_fractional_flow_noHDT` freely (it is an
axiom here). No `native_decide`, no `admit`, no new axioms, no `sorry` in the final proof. Use
`classical` for any missing `DecidableRel` / `Fintype` instances. If the full induction is hard,
localize the remaining gap to the smallest possible `sorry`. -/
theorem dross_fractional_flow (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : 9 * Fintype.card V ≤ 10 * G.minDegree)
    (δ : ℝ) (hδdef : δ = ((Fintype.card V : ℝ) - G.minDegree) / Fintype.card V)
    (hδ1 : δ < 1/10)
    (hbig : 4 + 2 * (Fintype.card V : ℝ) - 12 * δ * (Fintype.card V : ℝ)
        ≤ (1 - 11 * δ + 10 * δ^2) * (Fintype.card V : ℝ)^2) :
    FractionalTriangleDecomp G := by
  classical
  induction m : G.edgeFinset.card using Nat.strong_induction_on generalizing G with
  | h m ih =>
    by_cases hNoHDT : ∀ u v w : V, G.Adj u v → G.Adj u w → G.Adj v w →
        G.minDegree + 2 ≤ G.degree u → G.minDegree + 2 ≤ G.degree v →
        G.minDegree + 2 ≤ G.degree w → False
    · exact dross_fractional_flow_noHDT G h δ hδdef hδ1 hbig hNoHDT
    · push_neg at hNoHDT
      obtain ⟨u, v, w, huv, huw, hvw, hu, hv, hw, _⟩ := hNoHDT
      let G' := G.deleteEdges (triEdges {u,v,w})
      have hmin : G'.minDegree = G.minDegree :=
        peeled_heavy_triangle_minDegree G hu hv hw
      have hlt : G'.edgeFinset.card < G.edgeFinset.card :=
        peeled_heavy_triangle_fewer_edges G huv huw hvw
      have hdec : FractionalTriangleDecomp G' := by
        apply ih G'.edgeFinset.card (by omega) G'
        · simpa [hmin] using h
        · simpa [hmin] using hδdef
        · rfl
      exact lift_fractional_decomp_triangle G huv huw hvw hdec

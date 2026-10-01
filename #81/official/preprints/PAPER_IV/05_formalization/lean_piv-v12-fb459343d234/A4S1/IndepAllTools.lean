import A4S1.MinDegreeAll
import A4S1.IndepConstructor
import PaperIV.DefectOneRootStar

/-!
# E14: neutral counting helpers for the independent terminal

Re-proved here (with our own proofs) so that the E10 accounting can be run without any module
of the `T1`/`TS`/two-phase family:

* `inEdges_mono`: `S ⊆ T → inEdges G S ⊆ inEdges G T`;
* `sum_card_filter_adj_le`: `Σ_{v ∈ S} deg_S(v) ≤ 2 e(G[S])` (handshake inside `S`);
* `card_inEdges_union_le`: `e(G[X ∪ Y]) ≤ e(G[X]) + |Y|·|V|`;
* `classCeiling_mul_le`: `⌈m/k⌉ · k ≤ m + k`;
* `card_inEdges_singleton`, `crossCount_singleton`: one vertex spans no edge and has
  `|N_T(x)|` links to `T`.
-/

namespace A4S1.IndepAll

open Finset A4S1.TerminalPacking

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem inEdges_mono {S T : Finset V} (h : S ⊆ T) : inEdges G S ⊆ inEdges G T := by
  intro e he
  rw [inEdges, mem_filter] at he ⊢
  exact ⟨he.1, fun v hv => h (he.2 v hv)⟩

/-- Handshake inside `S`: every edge of `G[S]` is counted from its two ends. -/
theorem sum_card_filter_adj_le (S : Finset V) :
    ∑ v ∈ S, (S.filter (G.Adj v)).card ≤ 2 * (inEdges G S).card := by
  -- each vertex `v` sees its neighbours in `S` through the edges `s(v, u)` of `G[S]` at `v`
  have hv : ∀ v ∈ S, (S.filter (G.Adj v)).card = ((inEdges G S).filter fun e => v ∈ e).card := by
    intro v hv
    refine card_bij (fun u _ => s(v, u)) ?_ ?_ ?_
    · intro u hu
      rw [mem_filter] at hu
      exact mem_filter.2 ⟨mk_mem_inEdges.2 ⟨hu.2, hv, hu.1⟩, Sym2.mem_mk_left v u⟩
    · intro u hu u' hu' h
      exact (Sym2.congr_right.1 h)
    · intro e he
      rw [mem_filter] at he
      obtain ⟨u, rfl⟩ := Sym2.mem_iff_exists.1 he.2
      rw [mk_mem_inEdges] at he
      exact ⟨u, mem_filter.2 ⟨he.1.2.2, he.1.1⟩, rfl⟩
  rw [sum_congr rfl hv]
  simp only [card_filter]
  rw [sum_comm]
  calc ∑ e ∈ inEdges G S, ∑ v ∈ S, (if v ∈ e then 1 else 0)
      ≤ ∑ _e ∈ inEdges G S, 2 := by
        refine sum_le_sum fun e _ => ?_
        rw [← card_filter]
        calc (S.filter fun v => v ∈ e).card ≤ e.toFinset.card :=
              card_le_card fun v hv => Sym2.mem_toFinset.2 (mem_filter.1 hv).2
          _ ≤ 2 := PaperIV.LiftedPieces.card_toFinset_sym2_le e
    _ = 2 * (inEdges G S).card := by rw [sum_const, smul_eq_mul, mul_comm]

/-- Adding a vertex set `Y` adds at most `|Y|·|V|` inner edges. -/
theorem card_inEdges_union_le (X Y : Finset V) :
    (inEdges G (X ∪ Y)).card ≤ (inEdges G X).card + Y.card * Fintype.card V := by
  have hsub : inEdges G (X ∪ Y) ⊆ inEdges G X ∪ Y.biUnion (fun y => G.incidenceFinset y) := by
    intro e he
    by_cases hX : ∀ v ∈ e, v ∈ X
    · exact mem_union_left _ (mem_filter.2 ⟨(mem_filter.1 he).1, hX⟩)
    · push_neg at hX
      obtain ⟨v, hve, hvX⟩ := hX
      have hvY : v ∈ Y := by
        rcases mem_union.1 ((mem_filter.1 he).2 v hve) with h | h
        · exact absurd h hvX
        · exact h
      refine mem_union_right _ (mem_biUnion.2 ⟨v, hvY, ?_⟩)
      rw [SimpleGraph.mem_incidenceFinset]
      exact ⟨SimpleGraph.mem_edgeFinset.1 (mem_filter.1 he).1, hve⟩
  have h1 := card_le_card hsub
  have h2 := card_union_le (inEdges G X) (Y.biUnion fun y => G.incidenceFinset y)
  have h3 := card_biUnion_le (s := Y) (t := fun y => G.incidenceFinset y)
  have h4 : ∑ y ∈ Y, (G.incidenceFinset y).card ≤ ∑ _y ∈ Y, Fintype.card V := by
    refine sum_le_sum fun y _ => ?_
    rw [SimpleGraph.card_incidenceFinset_eq_degree]
    exact (G.degree_lt_card_verts y).le
  rw [sum_const, smul_eq_mul] at h4
  omega

/-- A single vertex spans no edge. -/
theorem card_inEdges_singleton (x : V) : (inEdges G {x}).card = 0 := by
  rw [card_eq_zero, eq_empty_iff_forall_notMem]
  intro e he
  induction e using Sym2.ind with
  | _ a b =>
    rw [mk_mem_inEdges, mem_singleton, mem_singleton] at he
    obtain ⟨hab, rfl, rfl⟩ := he
    exact hab.ne rfl

omit [Fintype V] [DecidableEq V] in
/-- The links from one vertex. -/
theorem crossCount_singleton (x : V) (T : Finset V) :
    crossCount G {x} T = (T.filter (G.Adj x)).card := by
  unfold crossCount
  refine card_bij (fun p _ => p.2) ?_ ?_ ?_
  · intro p hp
    rw [mem_filter, mem_product, mem_singleton] at hp
    rw [mem_filter]
    exact ⟨hp.1.2, hp.1.1 ▸ hp.2⟩
  · intro p hp p' hp' h
    rw [mem_filter, mem_product, mem_singleton] at hp hp'
    exact Prod.ext (hp.1.1.trans hp'.1.1.symm) h
  · intro y hy
    rw [mem_filter] at hy
    exact ⟨(x, y), mem_filter.2 ⟨mem_product.2 ⟨mem_singleton_self x, hy.1⟩, hy.2⟩, rfl⟩

/-- `⌈m/k⌉ · k ≤ m + k`. -/
theorem classCeiling_mul_le (m k : ℕ) :
    PaperIV.EquitableEdgeColouring.classCeiling m k * k ≤ m + k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  have h := Nat.div_mul_le_self (m + k - 1) k
  have h' : PaperIV.EquitableEdgeColouring.classCeiling m k = (m + k - 1) / k := by
    unfold PaperIV.EquitableEdgeColouring.classCeiling
    rw [Nat.ceilDiv_eq_add_pred_div]
  rw [h']
  omega

end A4S1.IndepAll

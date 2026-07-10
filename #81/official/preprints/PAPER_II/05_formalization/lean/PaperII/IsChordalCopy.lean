import PaperII.IsChordal
import PaperII.CloneCopy

/-!
# Paper II — A2 from `IsChordal`: copying toward a clique neighborhood preserves chordality (Path 2)

The class-copy `classCopy H A B` toward a **simplicial** target (target neighborhood `B` a clique)
preserves chordality. This is the ledger fact A2, here PROVEN from the standard definition
`IsChordal` (no longer assumed as `A2Transfer`). A new cycle of length `≥ 4` through a copied vertex
`v` has two neighbors of `v` in its clique neighborhood, which are adjacent — giving a chord.
-/

open scoped BigOperators

namespace PaperII

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-
Any two distinct vertices of `B` are adjacent in `classCopy H A B`, because `B` is a clique of
`H` and copied vertices point into `B`.
-/
lemma classCopy_clique_adj (H : SimpleGraph V) [DecidableRel H.Adj] (A B : Finset V)
    (hB : H.IsClique (B : Set V)) {x y : V} (hx : x ∈ B) (hy : y ∈ B) (hne : x ≠ y) :
    (classCopy H A B).Adj x y := by
  unfold classCopy;
  unfold classCopyRel;
  by_cases hxA : H.neighborFinset x = A <;> by_cases hyA : H.neighborFinset y = A <;> simp +decide [ *, SimpleGraph.fromRel_adj ];
  exact Or.inl ( hB hx hy hne )

/-
A neighbor `u` (in `classCopy H A B`) of a copied vertex `v` (`N_H(v) = A`) is either in `B`, or
is itself copied and `v ∈ B`.
-/
lemma classCopy_neighbor_mem (H : SimpleGraph V) [DecidableRel H.Adj] (A B : Finset V)
    {v u : V} (hv : H.neighborFinset v = A) (hadj : (classCopy H A B).Adj v u) :
    u ∈ B ∨ (H.neighborFinset u = A ∧ v ∈ B) := by
  contrapose! hadj; simp_all +decide [ classCopy, fromRel ] ;
  unfold classCopyRel; aesop;

/-
On non-copied vertices (`N_H ≠ A`), `classCopy H A B` agrees with `H`.
-/
lemma classCopy_adj_of_neighborFinset_ne (H : SimpleGraph V) [DecidableRel H.Adj] (A B : Finset V)
    {x y : V} (hx : H.neighborFinset x ≠ A) (hy : H.neighborFinset y ≠ A) :
    (classCopy H A B).Adj x y ↔ H.Adj x y := by
  simp +decide [ classCopy, classCopyRel, hx, hy ];
  by_cases h : H.Adj x y <;> simp_all +decide [ SimpleGraph.adj_comm ];
  exact h.ne

/-
In a path, the unique edge incident to the starting vertex `u` goes to the second vertex
`p.getVert 1`.
-/
lemma path_edge_start_eq_getVert_one {G : SimpleGraph V} {u w : V} {p : G.Walk u w}
    (hp : p.IsPath) {t : V} (ht : s(u, t) ∈ p.edges) : t = p.getVert 1 := by
  cases p <;> simp_all +decide [ SimpleGraph.Walk.cons_isPath_iff ];
  rename_i h₁ h₂;
  rcases ht with ( ( rfl | ⟨ rfl, rfl ⟩ ) | ht );
  · rfl;
  · rfl;
  · exact False.elim ( hp.2 ( SimpleGraph.Walk.fst_mem_support_of_mem_edges h₂ ht ) )

/-
A cycle of length `≥ 4` contains no triangle: three mutually incident cycle edges are
impossible.
-/
lemma cycle_no_triangle {G : SimpleGraph V} {v0 : V} (c : G.Walk v0 v0)
    (hc : c.IsCycle) (hlen : 4 ≤ c.length) {x y z : V}
    (hxy : s(x, y) ∈ c.edges) (hyz : s(y, z) ∈ c.edges) (hxz : s(x, z) ∈ c.edges) : False := by
  -- Rotate the cycle so it starts at `x`. Since `s(x,y) ∈ c.edges`, `x ∈ c.support` (`c.fst_mem_support_of_mem_edges`). Let `hx : x ∈ c.support` and set `d := c.rotate hx`.
  obtain ⟨hx, d, hd⟩ : ∃ hx : x ∈ c.support, ∃ d : G.Walk x x, d = c.rotate hx ∧ d.IsCycle ∧ s(x, y) ∈ d.edges ∧ s(y, z) ∈ d.edges ∧ s(x, z) ∈ d.edges ∧ 4 ≤ d.length := by
    obtain ⟨hx, d, hd⟩ : ∃ hx : x ∈ c.support, ∃ d : G.Walk x x, d = c.rotate hx ∧ d.IsCycle ∧ 4 ≤ d.length := by
      obtain ⟨hx, d, hd⟩ : ∃ hx : x ∈ c.support, ∃ d : G.Walk x x, d = c.rotate hx ∧ d.IsCycle := by
        exact ⟨ by simpa using SimpleGraph.Walk.fst_mem_support_of_mem_edges _ hxy, _, rfl, hc.rotate _ ⟩;
      have hrot : d.edges ~r c.edges := by
        grind +suggestions;
      have := hrot.perm.length_eq; simp_all +decide [ SimpleGraph.Walk.length_edges ] ;
      aesop;
    refine' ⟨ hx, d, hd.1, hd.2.1, _, _, _, hd.2.2 ⟩ <;> simp_all +decide [ SimpleGraph.Walk.rotate_edges ];
    · convert List.IsRotated.mem_iff ( c.rotate_edges hx ) |>.2 hxy using 1;
    · convert List.IsRotated.mem_iff ( c.rotate_edges hx ) |>.2 hyz using 1;
    · convert List.IsRotated.mem_iff ( c.rotate_edges hx ) |>.2 hxz using 1;
  -- Let `m` be the first vertex after `x` in `d`. Then `d = Walk.cons h1 q` for some `q : G.Walk m x`.
  obtain ⟨m, h1, q, hq⟩ : ∃ m : V, ∃ h1 : G.Adj x m, ∃ q : G.Walk m x, d = Walk.cons h1 q := by
    rcases d with ( _ | ⟨ h1, q ⟩ ) <;> simp_all +decide;
    exact ⟨ _, h1, _, hd.1.symm ⟩;
  -- Let `N := q.reverse.getVert 1`. `q.reverse : G.Walk x m` is a path (`hq.reverse`).
  set N := q.reverse.getVert 1 with hN_def
  have hq_reverse_path : q.reverse.IsPath := by
    have := hd.2.1; simp_all +decide [ SimpleGraph.Walk.cons_isCycle_iff ] ;
  have hq_reverse_length : 3 ≤ q.length := by
    simp_all +decide [ SimpleGraph.Walk.length_cons ]
  have hq_reverse_getVert1 : N ≠ x := by
    have := hq_reverse_path.getVert_injOn ( show 0 ∈ { i | i ≤ q.reverse.length } from by simp +decide ) ( show 1 ∈ { i | i ≤ q.reverse.length } from by simp +decide ; linarith ) ; simp_all +decide ;
    exact Ne.symm this;
  -- Apply `path_edge_start_eq_getVert_one` to `s(x,y)` and `s(x,z)` to get `y ∈ {m, N}` and `z ∈ {m, N}`.
  have hyN : y ∈ ({m, N} : Set V) := by
    have hyN : s(x, y) ∈ s(x, m) :: q.edges := by
      aesop;
    by_cases hy : s(x, y) = s(x, m) <;> simp_all +decide [ SimpleGraph.Walk.edges_append ];
    · grind;
    · have := path_edge_start_eq_getVert_one ( show q.reverse.IsPath from hq_reverse_path.reverse ) ( show s(x, y) ∈ q.reverse.edges from by
                                                                                                        rw [ SimpleGraph.Walk.edges_reverse ] ; aesop; ) ; aesop;
  have hzN : z ∈ ({m, N} : Set V) := by
    simp_all +decide [ SimpleGraph.Walk.edges_cons ];
    grind +suggestions
  have hyzN : y ≠ z := by
    have := c.adj_of_mem_edges hyz; aesop;
  have hmn : s(m, N) ∈ d.edges := by
    grind +qlia;
  -- Apply `path_edge_start_eq_getVert_one` to `s(m, N)` to get `N = q.getVert 1`.
  have hN_eq_q_getVert1 : N = q.getVert 1 := by
    have hmn_q : s(m, N) ∈ q.edges := by
      simp_all +decide [ SimpleGraph.Walk.edges_cons ];
      grind;
    grind +suggestions;
  have hN_eq_q_getVert1 : q.getVert 1 = q.getVert (q.length - 1) := by
    rw [ ← hN_eq_q_getVert1, hN_def, SimpleGraph.Walk.getVert_reverse ];
  have hq_getVert_injOn : Set.InjOn q.getVert {i | i ≤ q.length} := by
    have hq_getVert_injOn : q.IsPath := by
      grind +suggestions;
    apply SimpleGraph.Walk.IsPath.getVert_injOn hq_getVert_injOn;
  exact absurd ( hq_getVert_injOn ( show 1 ≤ q.length from by linarith ) ( show q.length - 1 ≤ q.length from Nat.sub_le _ _ ) hN_eq_q_getVert1 ) ( by omega )

/-
Every vertex `v` on a cycle of length `≥ 4` has two distinct cycle-neighbors `a, b` (edges
`s(v,a)`, `s(v,b)` are cycle edges) that are themselves not joined by a cycle edge.
-/
lemma cycle_two_neighbors {G : SimpleGraph V} {v0 : V} (c : G.Walk v0 v0)
    (hc : c.IsCycle) (hlen : 4 ≤ c.length) {v : V} (hv : v ∈ c.support) :
    ∃ a b : V, s(v, a) ∈ c.edges ∧ s(v, b) ∈ c.edges ∧ a ≠ b ∧ s(a, b) ∉ c.edges := by
  -- Rotate the cycle to start at `v`. Let `d := c.rotate hv`.
  obtain ⟨d, hd⟩ : ∃ d : G.Walk v v, d.IsCycle ∧ d.length ≥ 4 ∧ d.edges ~r c.edges := by
    obtain ⟨d, hd⟩ : ∃ d : G.Walk v v, d.IsCycle ∧ d.edges ~r c.edges := by
      exact ⟨ c.rotate hv, hc.rotate hv, by simp +decide [ SimpleGraph.Walk.rotate_edges ] ⟩;
    have := List.Perm.length_eq ( hd.2.perm ) ; simp_all +decide [ SimpleGraph.Walk.length_edges ] ;
    exact ⟨ d, hd.1, this.symm ▸ hlen, hd.2 ⟩;
  -- By `SimpleGraph.Walk.not_nil_iff`, there exists `a`, `h_a : G.Adj v a`, `p : G.Walk a v`, with `hcons : d = Walk.cons h_a p`.
  obtain ⟨a, h_a, p, hcons⟩ : ∃ a : V, ∃ h_a : G.Adj v a, ∃ p : G.Walk a v, d = p.cons h_a := by
    rcases d with ( _ | ⟨ h_a, p ⟩ ) <;> simp_all +decide;
  -- By `SimpleGraph.Walk.not_nil_iff`, there exists `b`, `h_b : G.Adj v b`, `r`, with `hprcons : p.reverse = Walk.cons h_b r`.
  obtain ⟨b, h_b, r, hprcons⟩ : ∃ b : V, ∃ h_b : G.Adj v b, ∃ r : G.Walk b a, p.reverse = r.cons h_b := by
    have hprcons : ¬p.reverse.Nil := by
      cases p <;> simp_all +decide;
    exact SimpleGraph.Walk.not_nil_iff.mp hprcons;
  refine' ⟨ a, b, _, _, _, _ ⟩ <;> simp_all +decide [ List.IsRotated.mem_iff ];
  · exact hd.2.2.mem_iff.mp ( List.mem_cons_self );
  · have h_edge_in_p : s(v, b) ∈ p.reverse.edges := by
      simp +decide [ hprcons, SimpleGraph.Walk.edges_cons ];
    grind +suggestions;
  · intro h; simp_all +decide [ SimpleGraph.Walk.cons_isCycle_iff ] ;
    replace hprcons := congr_arg ( fun q => q.edges ) hprcons ; simp_all +decide [ SimpleGraph.Walk.edges_reverse ] ;
  · intro h;
    apply cycle_no_triangle (Walk.cons h_a p) hd.left (by
    simp +arith +decide [ hd.2.1 ]);
    exact List.mem_cons_self;
    any_goals exact b;
    · have := hd.2.2.symm.mem_iff.mp h; simp_all +decide [ List.mem_cons ] ;
    · replace hprcons := congr_arg ( fun q => s(v, b) ∈ q.edges ) hprcons ; simp_all +decide [ SimpleGraph.Walk.edges_reverse ]

/-- **A2.** Copying the clone class toward a simplicial target (`B` a clique) preserves chordality. -/
theorem chordal_classCopy (H : SimpleGraph V) [DecidableRel H.Adj] (A B : Finset V)
    (hH : IsChordal H) (hB : H.IsClique (B : Set V)) : IsChordal (classCopy H A B) := by
  intro v0 c hc hlen
  by_cases hcop : ∃ w ∈ c.support, H.neighborFinset w = A
  · -- A copied vertex lies on the cycle.
    by_cases hout : ∃ z ∈ c.support, H.neighborFinset z = A ∧ z ∉ B
    · -- Pick a copied vertex `v ∉ B`: both its cycle-neighbors are then forced into `B`.
      obtain ⟨v, hvsup, hvA, hvB⟩ := hout
      obtain ⟨a, b, hva, hvb, hab, hnab⟩ := cycle_two_neighbors c hc hlen hvsup
      have hadja := c.adj_of_mem_edges hva
      have hadjb := c.adj_of_mem_edges hvb
      have ha : a ∈ B := by
        rcases classCopy_neighbor_mem H A B hvA hadja with h | ⟨_, h⟩
        · exact h
        · exact absurd h hvB
      have hb : b ∈ B := by
        rcases classCopy_neighbor_mem H A B hvA hadjb with h | ⟨_, h⟩
        · exact h
        · exact absurd h hvB
      exact ⟨a, b, c.snd_mem_support_of_mem_edges hva, c.snd_mem_support_of_mem_edges hvb,
        classCopy_clique_adj H A B hB ha hb hab, hnab⟩
    · -- All copied cycle-vertices are in `B`; use the given copied vertex `w`.
      push_neg at hout
      obtain ⟨w, hw, hwA⟩ := hcop
      obtain ⟨a, b, hva, hvb, hab, hnab⟩ := cycle_two_neighbors c hc hlen hw
      have hadja := c.adj_of_mem_edges hva
      have hadjb := c.adj_of_mem_edges hvb
      have ha : a ∈ B := by
        rcases classCopy_neighbor_mem H A B hwA hadja with h | ⟨haA, _⟩
        · exact h
        · exact hout a (c.snd_mem_support_of_mem_edges hva) haA
      have hb : b ∈ B := by
        rcases classCopy_neighbor_mem H A B hwA hadjb with h | ⟨hbA, _⟩
        · exact h
        · exact hout b (c.snd_mem_support_of_mem_edges hvb) hbA
      exact ⟨a, b, c.snd_mem_support_of_mem_edges hva, c.snd_mem_support_of_mem_edges hvb,
        classCopy_clique_adj H A B hB ha hb hab, hnab⟩
  · -- No copied vertex on the cycle: it is a genuine `H`-cycle, so use chordality of `H`.
    push_neg at hcop
    have hEsub : ∀ e ∈ c.edges, e ∈ H.edgeSet := by
      intro e he
      refine Sym2.ind (fun x y he => ?_) e he
      have hx := c.fst_mem_support_of_mem_edges he
      have hy := c.snd_mem_support_of_mem_edges he
      rw [SimpleGraph.mem_edgeSet]
      have hadj := c.adj_of_mem_edges he
      rwa [classCopy_adj_of_neighborFinset_ne H A B (hcop x hx) (hcop y hy)] at hadj
    have hcH : (c.transfer H hEsub).IsCycle := hc.transfer hEsub
    have hlenH : 4 ≤ (c.transfer H hEsub).length := by
      rw [SimpleGraph.Walk.length_transfer]; exact hlen
    obtain ⟨x, y, hx, hy, hadj, hedge⟩ := hH (c.transfer H hEsub) hcH hlenH
    rw [SimpleGraph.Walk.supp
/-
# Nibble — an unconditional spread fractional triangle decomposition for near-complete graphs

`Nibble/DrossLinkRouting.lean` reduces the spread Dross input to a family of local
*vertex-prescription* problems in the links, and `Nibble/LinkSolve.lean` solves the linear systems
those problems produce whenever the coefficient matrix is a near rank-one perturbation of a multiple
of the identity.

This file carries that programme out unconditionally for graphs of minimum degree at least
`(1 - 1/100)|V|`:

* `Nibble.linkTriangles`, `Nibble.linkMat` — the triangles inside the link of a vertex and their
  pair-count matrix; `Nibble.sum_linkMat_mul` identifies the vertex degrees of the ansatz
  `b_{xyz} = f x + f y + f z` with the matrix acting on `f`.
* `Nibble.isNearRankOne_linkMatExt` — at minimum degree `(1 - 1/100)|V|` the pair-count matrix is
  a near rank-one perturbation of `D·I + |V|·J` with `D = |V|²/2 - |V|`.
* `Nibble.exists_linkDeficiencyRouting_of_nearComplete` — hence the local problems are solvable,
  with weights of the required size.
* `Nibble.nearComplete_hasSpreadFracTriangleDecomp` — **the theorem**: every graph on at least
  `1000` vertices with minimum degree at least `(1 - 1/100)|V|` carries a fractional triangle
  decomposition all of whose weights are at most `3/|V|`.

Sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.DrossLinkRouting
import Nibble.LinkSolve

open Finset SimpleGraph Hypergraph Nibble.YusterE

namespace Nibble

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ### The link triangles and their pair counts -/

/-- The triangles of `G` inside the link of `u`. -/
noncomputable def linkTriangles (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) :
    Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => ∀ x ∈ t, G.Adj u x)

/-- The number of link triangles of `u` through both `v` and `w` (through `v`, if `v = w`). -/
noncomputable def linkMat (G : SimpleGraph V) [DecidableRel G.Adj] (u v w : V) : ℝ :=
  (((linkTriangles G u).filter (fun t => v ∈ t ∧ w ∈ t)).card : ℝ)

/-- **The counting identity.**  The vertex degree at `v` of the triangle weighting
`t ↦ ∑_{x ∈ t} f x` is the `v`-th row of the pair-count matrix applied to `f`. -/
theorem sum_linkMat_mul (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (f : V → ℝ) (v : V) :
    ∑ w, linkMat G u v w * f w
      = ∑ t ∈ (linkTriangles G u).filter (fun t => v ∈ t), ∑ x ∈ t, f x := by
  classical
  have hinner : ∀ t : Finset V, ∑ x ∈ t, f x = ∑ w : V, (if w ∈ t then f w else 0) := by
    intro t
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  calc ∑ w, linkMat G u v w * f w
      = ∑ w : V, ∑ t ∈ (linkTriangles G u).filter (fun t => v ∈ t),
          (if w ∈ t then f w else 0) := by
        refine Finset.sum_congr rfl (fun w _ => ?_)
        rw [linkMat, ← Finset.sum_filter, Finset.filter_filter, Finset.sum_const, nsmul_eq_mul]
    _ = ∑ t ∈ (linkTriangles G u).filter (fun t => v ∈ t), ∑ w : V,
          (if w ∈ t then f w else 0) := Finset.sum_comm
    _ = ∑ t ∈ (linkTriangles G u).filter (fun t => v ∈ t), ∑ x ∈ t, f x :=
        Finset.sum_congr rfl (fun t _ => (hinner t).symm)

/-- **The doubling identity.**  Each link triangle through `v` has two other vertices. -/
theorem sum_erase_linkMat (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) :
    ∑ w ∈ Finset.univ.erase v, linkMat G u v w = 2 * linkMat G u v v := by
  classical
  set S : Finset (Finset V) := (linkTriangles G u).filter (fun t => v ∈ t) with hS
  have hmat : ∀ w : V, linkMat G u v w = ((S.filter (fun t => w ∈ t)).card : ℝ) := by
    intro w
    rw [linkMat, hS, Finset.filter_filter]
  have hdiagset : (linkTriangles G u).filter (fun t => v ∈ t ∧ v ∈ t) = S := by
    rw [hS]
    exact Finset.filter_congr (fun t _ => by simp)
  have hdiag : linkMat G u v v = (S.card : ℝ) := by rw [linkMat, hdiagset]
  have hcast : ∀ w : V, ((S.filter (fun t => w ∈ t)).card : ℝ)
      = ∑ t ∈ S, (if w ∈ t then (1 : ℝ) else 0) := by
    intro w
    rw [Finset.card_filter]
    push_cast
    rfl
  calc ∑ w ∈ Finset.univ.erase v, linkMat G u v w
      = ∑ w ∈ Finset.univ.erase v, ∑ t ∈ S, (if w ∈ t then (1 : ℝ) else 0) :=
        Finset.sum_congr rfl (fun w _ => by rw [hmat w, hcast w])
    _ = ∑ t ∈ S, ∑ w ∈ Finset.univ.erase v, (if w ∈ t then (1 : ℝ) else 0) := Finset.sum_comm
    _ = ∑ _t ∈ S, (2 : ℝ) := by
        refine Finset.sum_congr rfl (fun t ht => ?_)
        rw [Finset.sum_ite_mem]
        have hin : (Finset.univ.erase v) ∩ t = t.erase v := by
          ext a
          simp only [Finset.mem_inter, Finset.mem_erase, Finset.mem_univ]
          tauto
        rw [hin, Finset.sum_const, nsmul_eq_mul, mul_one]
        have hv : v ∈ t := (Finset.mem_filter.mp ht).2
        have h3 : t.card = 3 := by
          have hlt := (Finset.mem_filter.mp ht).1
          rw [linkTriangles, Finset.mem_filter, SimpleGraph.mem_cliqueFinset_iff] at hlt
          exact hlt.1.card_eq
        rw [Finset.card_erase_of_mem hv, h3]
        norm_num
    _ = 2 * linkMat G u v v := by rw [Finset.sum_const, nsmul_eq_mul, hdiag]; ring

/-! ### Neighbourhood estimates in a near-complete graph -/

/-- The number of non-neighbours of a vertex is `|V| - deg`. -/
theorem card_sdiff_neighborFinset (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) :
    (((Finset.univ \ G.neighborFinset u).card : ℕ) : ℝ)
      = (Fintype.card V : ℝ) - (G.degree u : ℝ) := by
  have h : ((Finset.univ \ G.neighborFinset u).card : ℕ) + (G.neighborFinset u).card
      = Fintype.card V := by
    rw [Finset.card_sdiff_add_card_eq_card (Finset.subset_univ _), Finset.card_univ]
  have h' : (((Finset.univ \ G.neighborFinset u).card : ℕ) : ℝ) + ((G.neighborFinset u).card : ℝ)
      = (Fintype.card V : ℝ) := by exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) h
  rw [SimpleGraph.card_neighborFinset_eq_degree] at h'
  linarith

/-- **Few non-neighbours.**  At minimum degree `(1 - c)|V|` every vertex has at most `c|V|`
non-neighbours. -/
theorem card_nonNbrs_le (G : SimpleGraph V) [DecidableRel G.Adj] {c : ℝ}
    (hmin : (1 - c) * (Fintype.card V : ℝ) ≤ (G.minDegree : ℝ)) (u : V) :
    (((Finset.univ \ G.neighborFinset u).card : ℕ) : ℝ) ≤ c * (Fintype.card V : ℝ) := by
  have hdeg : ((G.minDegree : ℕ) : ℝ) ≤ (G.degree u : ℝ) := by
    exact_mod_cast G.minDegree_le_degree u
  rw [card_sdiff_neighborFinset]
  linarith

/-- **Triple codegrees.**  Three vertices have many common neighbours. -/
theorem card_inter3_ge (G : SimpleGraph V) [DecidableRel G.Adj] {c : ℝ}
    (hmin : (1 - c) * (Fintype.card V : ℝ) ≤ (G.minDegree : ℝ)) (u v w : V) :
    (1 - 3 * c) * (Fintype.card V : ℝ)
      ≤ (((G.neighborFinset u ∩ G.neighborFinset v ∩ G.neighborFinset w).card : ℕ) : ℝ) := by
  classical
  set A := G.neighborFinset u ∩ G.neighborFinset v ∩ G.neighborFinset w with hA
  have hsub : (Finset.univ \ A) ⊆ (Finset.univ \ G.neighborFinset u)
      ∪ (Finset.univ \ G.neighborFinset v) ∪ (Finset.univ \ G.neighborFinset w) := by
    intro x hx
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, hA, Finset.mem_inter,
      Finset.mem_union] at hx ⊢
    tauto
  have hcard : ((Finset.univ \ A).card : ℝ) ≤ 3 * c * (Fintype.card V : ℝ) := by
    have h1 : (Finset.univ \ A).card
        ≤ (Finset.univ \ G.neighborFinset u).card + (Finset.univ \ G.neighborFinset v).card
          + (Finset.univ \ G.neighborFinset w).card := by
      refine le_trans (Finset.card_le_card hsub) ?_
      exact le_trans (Finset.card_union_le _ _) (by
        exact Nat.add_le_add_right (Finset.card_union_le _ _) _)
    have h1' : ((Finset.univ \ A).card : ℝ)
        ≤ ((Finset.univ \ G.neighborFinset u).card : ℝ)
          + ((Finset.univ \ G.neighborFinset v).card : ℝ)
          + ((Finset.univ \ G.neighborFinset w).card : ℝ) := by exact_mod_cast h1
    have hu := card_nonNbrs_le G hmin u
    have hv := card_nonNbrs_le G hmin v
    have hw := card_nonNbrs_le G hmin w
    linarith
  have hsum : ((Finset.univ \ A).card : ℝ) + (A.card : ℝ) = (Fintype.card V : ℝ) := by
    have h : (Finset.univ \ A).card + A.card = Fintype.card V := by
      rw [Finset.card_sdiff_add_card_eq_card (Finset.subset_univ _), Finset.card_univ]
    exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) h
  linarith

/-! ### The pair-count matrix of a near-complete graph -/

/-- **Upper bound**: at most `|V|` link triangles through a pair of distinct vertices. -/
theorem linkMat_le (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) {v w : V} (hvw : v ≠ w) :
    linkMat G u v w ≤ (Fintype.card V : ℝ) := by
  classical
  have hsub : (linkTriangles G u).filter (fun t => v ∈ t ∧ w ∈ t)
      ⊆ (G.cliqueFinset 3).filter (fun t => ({v, w} : Finset V) ⊆ t) := by
    intro t ht
    rw [Finset.mem_filter] at ht ⊢
    obtain ⟨htl, hv, hw⟩ := ht
    refine ⟨(Finset.mem_filter.mp htl).1, ?_⟩
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact hv
    · rw [Finset.mem_singleton] at ha
      exact ha ▸ hw
  have hq : ({v, w} : Finset V).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simp [hvw]), Finset.card_singleton]
  calc linkMat G u v w ≤ (((G.cliqueFinset 3).filter (fun t => ({v, w} : Finset V) ⊆ t)).card : ℝ) := by
        rw [linkMat]
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ (Fintype.card V : ℝ) := card_cliqueFinset3_filter_supset_le G hq

/-- **Vanishing**: no link triangle of `u` contains a pair that is not an edge inside the link. -/
theorem linkMat_eq_zero (G : SimpleGraph V) [DecidableRel G.Adj] {u v w : V} (hvw : v ≠ w)
    (h : ¬ (G.Adj u w ∧ G.Adj v w)) : linkMat G u v w = 0 := by
  classical
  rw [linkMat, Nat.cast_eq_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro t ht
  rintro ⟨hv, hw⟩
  rw [linkTriangles, Finset.mem_filter, SimpleGraph.mem_cliqueFinset_iff] at ht
  exact h ⟨ht.2 w hw, ht.1.isClique hv hw hvw⟩

/-- **Lower bound**: a pair of adjacent vertices inside the link lies in almost `|V|` link
triangles. -/
theorem linkMat_ge (G : SimpleGraph V) [DecidableRel G.Adj] {c : ℝ}
    (hmin : (1 - c) * (Fintype.card V : ℝ) ≤ (G.minDegree : ℝ)) {u v w : V} (hvw : v ≠ w)
    (huv : G.Adj u v) (huw : G.Adj u w) (hvw' : G.Adj v w) :
    (1 - 3 * c) * (Fintype.card V : ℝ) - 2 ≤ linkMat G u v w := by
  classical
  set A := G.neighborFinset u ∩ G.neighborFinset v ∩ G.neighborFinset w with hA
  set S := A \ ({v, w} : Finset V) with hSdef
  have hmaps : ∀ x ∈ S, (insert x ({v, w} : Finset V))
      ∈ (linkTriangles G u).filter (fun t => v ∈ t ∧ w ∈ t) := by
    intro x hx
    rw [hSdef, Finset.mem_sdiff, hA, Finset.mem_inter, Finset.mem_inter] at hx
    obtain ⟨⟨⟨hxu, hxv⟩, hxw⟩, hxnot⟩ := hx
    rw [SimpleGraph.mem_neighborFinset] at hxu hxv hxw
    have hxv' : x ≠ v := by
      intro h; exact hxnot (by simp [h])
    have hxw' : x ≠ w := by
      intro h; exact hxnot (by simp [h])
    have hclique : G.IsNClique 3 (insert x ({v, w} : Finset V)) :=
      SimpleGraph.is3Clique_triple_iff.mpr ⟨hxv.symm, hxw.symm, hvw'⟩
    rw [Finset.mem_filter, linkTriangles, Finset.mem_filter, SimpleGraph.mem_cliqueFinset_iff]
    refine ⟨⟨hclique, ?_⟩, by simp, by simp⟩
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact hxu
    · rcases Finset.mem_insert.mp hy with rfl | hy
      · exact huv
      · rw [Finset.mem_singleton] at hy
        exact hy ▸ huw
  have hinj : Set.InjOn (fun x => insert x ({v, w} : Finset V)) (S : Set V) := by
    intro x hx x' hx' heq
    simp only [Finset.mem_coe, hSdef, Finset.mem_sdiff] at hx hx'
    have heq' : insert x ({v, w} : Finset V) = insert x' ({v, w} : Finset V) := heq
    have hxmem : x ∈ insert x' ({v, w} : Finset V) := by
      have hx0 : x ∈ insert x ({v, w} : Finset V) := Finset.mem_insert_self _ _
      rwa [heq'] at hx0
    rcases Finset.mem_insert.mp hxmem with h | h
    · exact h
    · exact absurd h hx.2
  have hcards : (S.card : ℝ) ≤ linkMat G u v w := by
    rw [linkMat]
    exact_mod_cast Finset.card_le_card_of_injOn _ hmaps hinj
  have hAS : (A.card : ℝ) - 2 ≤ (S.card : ℝ) := by
    have h1 : A.card ≤ S.card + ({v, w} : Finset V).card := by
      have := Finset.card_le_card_sdiff_add_card (s := A) (t := ({v, w} : Finset V))
      simpa [hSdef] using this
    have h2 : ({v, w} : Finset V).card ≤ 2 := Finset.card_insert_le _ _ |>.trans (by simp)
    have h1' : (A.card : ℝ) ≤ (S.card : ℝ) + (({v, w} : Finset V).card : ℝ) := by
      exact_mod_cast h1
    have h2' : ((({v, w} : Finset V).card : ℕ) : ℝ) ≤ 2 := by exact_mod_cast h2
    linarith
  have hAge := card_inter3_ge G hmin u v w
  rw [← hA] at hAge
  linarith

/-! ### The near rank-one estimate -/

/-- The pair-count matrix, extended off the link so that every row is close to the rank-one
model. -/
noncomputable def linkMatExt (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (D pi : ℝ)
    (v w : V) : ℝ :=
  if G.Adj u v then linkMat G u v w else (if v = w then D + pi else pi)

/-- **The row estimate.**  At minimum degree `(1 - 1/100)|V|` the extended pair-count matrix of
every link is a near rank-one perturbation of `D·I + |V|·J`, with `D = |V|²/2 - |V|`, of row error
at most `D/4`. -/
theorem isNearRankOne_linkMatExt (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 1000 ≤ Fintype.card V)
    (hmin : (1 - 1 / 100 : ℝ) * (Fintype.card V : ℝ) ≤ (G.minDegree : ℝ)) (u : V) :
    IsNearRankOne
      (linkMatExt G u ((Fintype.card V : ℝ) ^ 2 / 2 - (Fintype.card V : ℝ))
        (Fintype.card V : ℝ))
      ((Fintype.card V : ℝ) ^ 2 / 2 - (Fintype.card V : ℝ)) (Fintype.card V : ℝ) (1 / 4) := by
  classical
  set n : ℝ := (Fintype.card V : ℝ) with hndef
  have hn1000 : (1000 : ℝ) ≤ n := by rw [hndef]; exact_mod_cast hn
  set D : ℝ := n ^ 2 / 2 - n with hD
  have hDpos : 0 < D := by rw [hD]; nlinarith
  intro v
  by_cases huv : G.Adj u v
  · -- the interesting rows
    have hdiag : linkMatExt G u D n v v = linkMat G u v v := by
      rw [linkMatExt, if_pos huv]
    have hoff : ∀ w, linkMatExt G u D n v w = linkMat G u v w := by
      intro w; rw [linkMatExt, if_pos huv]
    simp only [hoff]
    -- the off-diagonal row error
    set R : ℝ := ∑ w ∈ Finset.univ.erase v, |linkMat G u v w - n| with hR
    have hbadcard : (((Finset.univ.erase v).filter
        (fun w => ¬ (G.Adj u w ∧ G.Adj v w))).card : ℝ) ≤ 2 / 100 * n := by
      have hsub : ((Finset.univ.erase v).filter (fun w => ¬ (G.Adj u w ∧ G.Adj v w)))
          ⊆ (Finset.univ \ G.neighborFinset u) ∪ (Finset.univ \ G.neighborFinset v) := by
        intro w hw
        rw [Finset.mem_filter] at hw
        simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and,
          SimpleGraph.mem_neighborFinset]
        tauto
      have h1 : ((Finset.univ.erase v).filter (fun w => ¬ (G.Adj u w ∧ G.Adj v w))).card
          ≤ (Finset.univ \ G.neighborFinset u).card + (Finset.univ \ G.neighborFinset v).card :=
        le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
      have h1' : ((((Finset.univ.erase v).filter
          (fun w => ¬ (G.Adj u w ∧ G.Adj v w))).card : ℕ) : ℝ)
          ≤ ((Finset.univ \ G.neighborFinset u).card : ℝ)
            + ((Finset.univ \ G.neighborFinset v).card : ℝ) := by exact_mod_cast h1
      have hu := card_nonNbrs_le G hmin u
      have hv := card_nonNbrs_le G hmin v
      linarith
    have hRle : R ≤ 5 / 100 * n ^ 2 + 2 * n := by
      rw [hR, ← Finset.sum_filter_add_sum_filter_not (Finset.univ.erase v)
        (fun w => G.Adj u w ∧ G.Adj v w)]
      have hgood : ∑ w ∈ (Finset.univ.erase v).filter (fun w => G.Adj u w ∧ G.Adj v w),
          |linkMat G u v w - n| ≤ 3 / 100 * n ^ 2 + 2 * n := by
        have hterm : ∀ w ∈ (Finset.univ.erase v).filter (fun w => G.Adj u w ∧ G.Adj v w),
            |linkMat G u v w - n| ≤ 3 / 100 * n + 2 := by
          intro w hw
          rw [Finset.mem_filter, Finset.mem_erase] at hw
          obtain ⟨⟨hwv, -⟩, huw, hvw⟩ := hw
          have hle := linkMat_le G u (Ne.symm hwv)
          have hge := linkMat_ge G hmin (Ne.symm hwv) huv huw hvw
          rw [abs_le]
          constructor <;> [linarith; linarith]
        refine le_trans (Finset.sum_le_sum hterm) ?_
        rw [Finset.sum_const, nsmul_eq_mul]
        have hcard : ((((Finset.univ.erase v).filter
            (fun w => G.Adj u w ∧ G.Adj v w)).card : ℕ) : ℝ) ≤ n := by
          have h1 : ((Finset.univ.erase v).filter (fun w => G.Adj u w ∧ G.Adj v w)).card
              ≤ Fintype.card V := by
            calc ((Finset.univ.erase v).filter (fun w => G.Adj u w ∧ G.Adj v w)).card
                ≤ (Finset.univ : Finset V).card :=
                  Finset.card_le_card (fun x _ => Finset.mem_univ x)
              _ = Fintype.card V := Finset.card_univ
          rw [hndef]
          exact_mod_cast h1
        have hpos : (0 : ℝ) ≤ 3 / 100 * n + 2 := by linarith
        nlinarith only [hcard, hpos]
      have hbad : ∑ w ∈ (Finset.univ.erase v).filter (fun w => ¬ (G.Adj u w ∧ G.Adj v w)),
          |linkMat G u v w - n| ≤ 2 / 100 * n ^ 2 := by
        have hterm : ∀ w ∈ (Finset.univ.erase v).filter (fun w => ¬ (G.Adj u w ∧ G.Adj v w)),
            |linkMat G u v w - n| ≤ n := by
          intro w hw
          rw [Finset.mem_filter, Finset.mem_erase] at hw
          obtain ⟨⟨hwv, -⟩, hbadw⟩ := hw
          rw [linkMat_eq_zero G (Ne.symm hwv) hbadw]
          rw [zero_sub, abs_neg, abs_of_nonneg (by linarith : (0:ℝ) ≤ n)]
        refine le_trans (Finset.sum_le_sum hterm) ?_
        rw [Finset.sum_const, nsmul_eq_mul]
        nlinarith only [hbadcard, hn1000]
      linarith
    -- the diagonal error, from the doubling identity
    have hdouble := sum_erase_linkMat G u v
    have hcarderase : ((Finset.univ.erase v).card : ℝ) = n - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ]
      have : 1 ≤ Fintype.card V := by omega
      push_cast [Nat.cast_sub this]
      rw [hndef]
    have hsumapprox : |(∑ w ∈ Finset.univ.erase v, linkMat G u v w) - (n - 1) * n| ≤ R := by
      have hEq : (∑ w ∈ Finset.univ.erase v, linkMat G u v w) - (n - 1) * n
          = ∑ w ∈ Finset.univ.erase v, (linkMat G u v w - n) := by
        rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hcarderase]
      rw [hEq, hR]
      exact Finset.abs_sum_le_sum_abs _ _
    have hdiagerr : |linkMat G u v v - (D + n)| ≤ (R + n) / 2 := by
      rw [hdouble] at hsumapprox
      have hDn : D + n = n ^ 2 / 2 := by rw [hD]; ring
      rw [hDn]
      have habs := abs_le.mp hsumapprox
      rw [abs_le]
      constructor <;> nlinarith [habs.1, habs.2]
    -- combine
    have hfinal : (R + n) / 2 + R ≤ 1 / 4 * D := by
      rw [hD]
      nlinarith only [hRle, hn1000]
    calc |linkMat G u v v - (D + n)| + R ≤ (R + n) / 2 + R := by linarith only [hdiagerr]
      _ ≤ 1 / 4 * D := hfinal
  · -- the rows off the link are exactly of the model shape
    have hdiag : linkMatExt G u D n v v = D + n := by
      rw [linkMatExt, if_neg huv, if_pos rfl]
    have hoff : ∀ w ∈ Finset.univ.erase v, linkMatExt G u D n v w = n := by
      intro w hw
      rw [Finset.mem_erase] at hw
      rw [linkMatExt, if_neg huv, if_neg (Ne.symm hw.1)]
    rw [hdiag]
    simp only [sub_self, abs_zero, zero_add]
    have : ∑ w ∈ Finset.univ.erase v, |linkMatExt G u D n v w - n| = 0 := by
      refine Finset.sum_eq_zero (fun w hw => ?_)
      rw [hoff w hw, sub_self, abs_zero]
    rw [this]
    positivity

/-! ### Solving the local problems -/

/-- **Codegrees.**  Two vertices have many common neighbours. -/
theorem card_inter2_ge (G : SimpleGraph V) [DecidableRel G.Adj] {c : ℝ}
    (hmin : (1 - c) * (Fintype.card V : ℝ) ≤ (G.minDegree : ℝ)) (u v : V) :
    (1 - 2 * c) * (Fintype.card V : ℝ)
      ≤ (((G.neighborFinset u ∩ G.neighborFinset v).card : ℕ) : ℝ) := by
  classical
  set A := G.neighborFinset u ∩ G.neighborFinset v with hA
  have hsub : (Finset.univ \ A) ⊆ (Finset.univ \ G.neighborFinset u)
      ∪ (Finset.univ \ G.neighborFinset v) := by
    intro x hx
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, hA, Finset.mem_inter,
      Finset.mem_union] at hx ⊢
    tauto
  have h1 : (Finset.univ \ A).card
      ≤ (Finset.univ \ G.neighborFinset u).card + (Finset.univ \ G.neighborFinset v).card :=
    le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
  have h1' : ((Finset.univ \ A).card : ℝ)
      ≤ ((Finset.univ \ G.neighborFinset u).card : ℝ)
        + ((Finset.univ \ G.neighborFinset v).card : ℝ) := by exact_mod_cast h1
  have hu := card_nonNbrs_le G hmin u
  have hv := card_nonNbrs_le G hmin v
  have hsum : ((Finset.univ \ A).card : ℝ) + (A.card : ℝ) = (Fintype.card V : ℝ) := by
    have h : (Finset.univ \ A).card + A.card = Fintype.card V := by
      rw [Finset.card_sdiff_add_card_eq_card (Finset.subset_univ _), Finset.card_univ]
    exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) h
  linarith

/-- The common neighbourhood of two adjacent vertices misses both of them. -/
theorem card_inter2_le (G : SimpleGraph V) [DecidableRel G.Adj] {u v : V} (huv : G.Adj u v) :
    (((G.neighborFinset u ∩ G.neighborFinset v).card : ℕ) : ℝ) + 2 ≤ (Fintype.card V : ℝ) := by
  classical
  have hsub : G.neighborFinset u ∩ G.neighborFinset v ⊆ Finset.univ \ ({u, v} : Finset V) := by
    intro x hx
    rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset, SimpleGraph.mem_neighborFinset] at hx
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    rintro (rfl | rfl)
    · exact hx.1.ne rfl
    · exact hx.2.ne rfl
  have hcard : ((Finset.univ : Finset V) \ ({u, v} : Finset V)).card + 2 = Fintype.card V := by
    have h2 : ({u, v} : Finset V).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp [huv.ne]), Finset.card_singleton]
    have h3 := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ ({u, v} : Finset V))
    rw [h2, Finset.card_univ] at h3
    exact h3
  have h1 : (G.neighborFinset u ∩ G.neighborFinset v).card
      ≤ ((Finset.univ : Finset V) \ ({u, v} : Finset V)).card := Finset.card_le_card hsub
  have h1' : (((G.neighborFinset u ∩ G.neighborFinset v).card : ℕ) : ℝ)
      ≤ ((((Finset.univ : Finset V) \ ({u, v} : Finset V)).card : ℕ) : ℝ) := by exact_mod_cast h1
  have hcard' : ((((Finset.univ : Finset V) \ ({u, v} : Finset V)).card : ℕ) : ℝ) + 2
      = (Fintype.card V : ℝ) := by exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) hcard
  linarith

/-- **The prescription**: each endpoint of an edge takes a quarter of the deficiency of the
uniform weighting `1/(|V|-2)` at that edge. -/
noncomputable def linkDemand (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) : ℝ :=
  if G.Adj u v then
    (1 - ((G.neighborFinset u ∩ G.neighborFinset v).card : ℝ) / ((Fintype.card V : ℝ) - 2)) / 4
  else 0

/-- **The prescription is small.** -/
theorem abs_linkDemand_le (G : SimpleGraph V) [DecidableRel G.Adj] (hn : 1000 ≤ Fintype.card V)
    (hmin : (1 - 1 / 100 : ℝ) * (Fintype.card V : ℝ) ≤ (G.minDegree : ℝ)) (u v : V) :
    |linkDemand G u v| ≤ 1 / 150 := by
  have hn1000 : (1000 : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast hn
  rw [linkDemand]
  split_ifs with huv
  · have hge := card_inter2_ge G hmin u v
    have hle := card_inter2_le G huv
    have hpos : (0 : ℝ) < (Fintype.card V : ℝ) - 2 := by linarith
    have hkey : (1 : ℝ) - ((G.neighborFinset u ∩ G.neighborFinset v).card : ℝ)
        / ((Fintype.card V : ℝ) - 2)
        = (((Fintype.card V : ℝ) - 2) - ((G.neighborFinset u ∩ G.neighborFinset v).card : ℝ))
          / ((Fintype.card V : ℝ) - 2) := by
      field_simp
    rw [hkey, abs_le]
    constructor
    · have hnn : (0 : ℝ) ≤ (((Fintype.card V : ℝ) - 2)
          - ((G.neighborFinset u ∩ G.neighborFinset v).card : ℝ))
          / ((Fintype.card V : ℝ) - 2) / 4 := by
        apply div_nonneg _ (by norm_num : (0:ℝ) ≤ 4)
        exact div_nonneg (by linarith) hpos.le
      linarith
    · rw [div_le_iff₀ (by norm_num : (0:ℝ) < 4), div_le_iff₀ hpos]
      nlinarith only [hge, hn1000]
  · simp

/-- **The local problems are solvable**: at minimum degree `(1 - 1/100)|V|` the deficiency of the
uniform weighting can be routed through the links, with weights of size `(1/4)/|V|²`. -/
theorem exists_linkDeficiencyRouting_of_nearComplete (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 1000 ≤ Fintype.card V)
    (hmin : (1 - 1 / 100 : ℝ) * (Fintype.card V : ℝ) ≤ (G.minDegree : ℝ)) :
    ∃ b : V → Finset V → ℝ, IsLinkDeficiencyRouting G 1 (1 / 4) b := by
  classical
  set n : ℝ := (Fintype.card V : ℝ) with hndef
  have hn1000 : (1000 : ℝ) ≤ n := by rw [hndef]; exact_mod_cast hn
  set D : ℝ := n ^ 2 / 2 - n with hD
  have hDpos : 0 < D := by rw [hD]; nlinarith
  -- solve the local systems
  have Hsolve : ∀ u : V, ∃ f : V → ℝ,
      (∀ v, ∑ w, linkMatExt G u D n v w * f w = linkDemand G u v) ∧ ‖f‖ ≤ 4 * (1 / 150) / D := by
    intro u
    obtain ⟨f, hf, hfb⟩ := exists_matMap_eq (linkMatExt G u D n) hDpos (by linarith)
      (by norm_num) (le_refl (1/4 : ℝ)) (isNearRankOne_linkMatExt G hn hmin u)
      (fun v => linkDemand G u v)
    refine ⟨f, hf, le_trans hfb ?_⟩
    have hcn : ‖fun v => linkDemand G u v‖ ≤ 1 / 150 := by
      refine (pi_norm_le_iff_of_nonneg (by norm_num)).mpr (fun v => ?_)
      simpa [Real.norm_eq_abs] using abs_linkDemand_le G hn hmin u v
    have h4 : 4 * ‖fun v => linkDemand G u v‖ ≤ 4 * (1 / 150) := by linarith
    gcongr
  choose f hfeq hfb using Hsolve
  set b : V → Finset V → ℝ :=
    fun u t => if t ∈ linkTriangles G u then ∑ x ∈ t, f u x else 0 with hbdef
  have hbval : ∀ u t, b u t = if t ∈ linkTriangles G u then ∑ x ∈ t, f u x else 0 :=
    fun u t => rfl
  refine ⟨b, ?_, ?_, ?_⟩
  · -- support
    intro u t ht
    by_cases hlt : t ∈ linkTriangles G u
    · rw [linkTriangles, Finset.mem_filter] at hlt
      exact ⟨hlt.1, hlt.2⟩
    · rw [hbval u t, if_neg hlt] at ht
      exact absurd rfl ht
  · -- size
    intro u t
    rw [hbval u t]
    by_cases hlt : t ∈ linkTriangles G u
    · rw [if_pos hlt]
      have ht3 : t.card = 3 := by
        rw [linkTriangles, Finset.mem_filter, SimpleGraph.mem_cliqueFinset_iff] at hlt
        exact hlt.1.card_eq
      have hb : |∑ x ∈ t, f u x| ≤ 3 * ‖f u‖ := by
        calc |∑ x ∈ t, f u x| ≤ ∑ x ∈ t, |f u x| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _x ∈ t, ‖f u‖ :=
              Finset.sum_le_sum (fun x _ => by
                simpa [Real.norm_eq_abs] using norm_le_pi_norm (f u) x)
          _ = 3 * ‖f u‖ := by rw [Finset.sum_const, ht3, nsmul_eq_mul]; norm_num
      have hfu := hfb u
      have hDge : (499 / 1000) * n ^ 2 ≤ D := by rw [hD]; nlinarith only [hn1000]
      have hnpos : (0 : ℝ) < n := by linarith
      calc |∑ x ∈ t, f u x| ≤ 3 * ‖f u‖ := hb
        _ ≤ 3 * (4 * (1 / 150) / D) := by
            have := norm_nonneg (f u)
            nlinarith only [hfu]
        _ ≤ 1 / 4 / n ^ 2 := by
            have h1 : 3 * (4 * (1 / 150) / D) = (2 / 25) / D := by
              field_simp
              norm_num
            rw [h1, div_le_div_iff₀ hDpos (by positivity)]
            nlinarith only [hDge, hnpos]
      -- (the goal is stated with `(Fintype.card V : ℝ) ^ 2`, definitionally `n ^ 2`)
    · rw [if_neg hlt, abs_zero]
      positivity
  · -- the prescription
    intro e u v huv hval
    have huvadj : G.Adj u v := by
      have hc := (SimpleGraph.mem_cliqueFinset_iff.mp e.property).isClique
      exact hc (by rw [hval]; simp) (by rw [hval]; simp) huv
    have hvsum : ∀ p q : V, G.Adj p q → linkVertexSum G b p q = linkDemand G p q := by
      intro p q hpq
      have hstep : linkVertexSum G b p q
          = ∑ t ∈ (linkTriangles G p).filter (fun t => q ∈ t), ∑ x ∈ t, f p x := by
        rw [linkVertexSum]
        rw [← Finset.sum_subset (s₁ := (linkTriangles G p).filter (fun t => q ∈ t))
            (s₂ := (G.cliqueFinset 3).filter (fun t => q ∈ t))]
        · exact Finset.sum_congr rfl (fun t ht => by
            rw [hbval p t, if_pos (Finset.mem_filter.mp ht).1])
        · intro t ht
          rw [Finset.mem_filter] at ht ⊢
          exact ⟨(Finset.mem_filter.mp ht.1).1, ht.2⟩
        · intro t _ hnot
          have : t ∉ linkTriangles G p := by
            intro hlt
            exact hnot (Finset.mem_filter.mpr ⟨hlt, by
              have := ‹t ∈ (G.cliqueFinset 3).filter (fun t => q ∈ t)›
              exact (Finset.mem_filter.mp this).2⟩)
          rw [hbval p t, if_neg this]
      rw [hstep, ← sum_linkMat_mul G p (f p) q]
      have hrow : ∀ w, linkMatExt G p D n q w = linkMat G p q w := by
        intro w; rw [linkMatExt, if_pos hpq]
      have := hfeq p q
      rw [Finset.sum_congr rfl (fun w _ => by rw [hrow w])] at this
      exact this
    rw [hvsum u v huvadj, hvsum v u huvadj.symm]
    have hcn : commonNbrs G e = G.neighborFinset u ∩ G.neighborFinset v := commonNbrs_eq G hval
    rw [linkDemand, linkDemand, if_pos huvadj, if_pos huvadj.symm, hcn,
      Finset.inter_comm (G.neighborFinset v) (G.neighborFinset u)]
    ring

/-- **The theorem.**  Every graph on at least `1000` vertices with minimum degree at least
`(1 - 1/100)|V|` carries a fractional triangle decomposition all of whose weights are at most
`3/|V|`. -/
theorem nearComplete_hasSpreadFracTriangleDecomp (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 1000 ≤ Fintype.card V)
    (hmin : (1 - 1 / 100 : ℝ) * (Fintype.card V : ℝ) ≤ (G.minDegree : ℝ)) :
    HasSpreadFracTriangleDecomp G 3 := by
  classical
  have hn3 : 3 ≤ Fintype.card V := by omega
  have hnR : (1000 : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast hn
  obtain ⟨b, hb⟩ := exists_linkDeficiencyRouting_of_nearComplete G hn hmin
  have hcorr : IsScaledDeficiencyCorrection G 1 (linkCorrection G b) :=
    isScaledDeficiencyCorrection_of_linkRouting G (by norm_num) (by norm_num) hn3 hb
  obtain ⟨w, hw, hwb⟩ :=
    (exists_scaledCorrection_iff_bounded_decomp G hn3 1).mp ⟨linkCorrection G b, hcorr⟩
  refine ⟨w, hw, fun T hT => ?_⟩
  refine le_trans (hwb T hT) ?_
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  linarith

end Nibble

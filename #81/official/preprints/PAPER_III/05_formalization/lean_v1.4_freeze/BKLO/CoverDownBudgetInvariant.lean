/-
# The greedy budget invariant of BKLO Lemma 10.3 (r = 2): the accumulated used degree is bounded

The greedy chooser `BKLO.exists_matching_of_budget` needs the already-used set `D` to have edge
degree `≤ d = γ|V|` at every neighbour.  Along the sweep, `D` is the union of the star-triangle edge
sets of the earlier apices, and the bound is automatic: a matching contributes at most `2` to the
degree of any non-apex vertex, and a vertex is matched by at most `d_H(v,U) ≤ γ|V|/2` apices
(condition (iii)), so `edeg D v ≤ 2 · d_H(v,U) ≤ γ|V|`.

This file proves, `sorry`-free, the two combinatorial facts behind that bound:
* `BKLO.edeg_biUnion_le` — edge degree is subadditive over a `biUnion` (from the project's
  `BKLO.edeg_union_le`);
* `BKLO.edeg_famEdges_starTriangles_le_two` — the star triangles at one apex `x` contribute at most
  `2` to the degree of any vertex `v ≠ x` (`v` lies in at most one matching edge, hence in at most
  the two triangle edges through it).

Everything here is `sorry`-free.
-/
import BKLO.StarMatchingTriangles
import BKLO.Reservoir

open Finset

namespace BKLO

variable {V : Type} [DecidableEq V]

/-- **Edge degree is subadditive over a `biUnion`.** -/
theorem edeg_biUnion_le {ι : Type*} [DecidableEq ι] (S : Finset ι) (f : ι → Finset (Sym2 V))
    (v : V) : edeg (S.biUnion f) v ≤ ∑ y ∈ S, edeg (f y) v := by
  classical
  induction S using Finset.induction with
  | empty => simp [edeg]
  | @insert a s ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    exact le_trans (edeg_union_le _ _ v) (Nat.add_le_add_left ih _)

/-- **One apex contributes at most `2` to a non-apex degree.**  For `v ≠ x` and a matching `M`
avoiding `x`, the star triangles `{x} ∪ e` contribute at most `2` to `edeg` at `v`: `v` lies in at
most one matching edge `e`, hence in at most the two edges `{x,v}`, `{v, e\{v}}` of its triangle. -/
theorem edeg_famEdges_starTriangles_le_two {x : V} {M : Finset (Finset V)}
    (h : IsMatchingAvoiding M x) {v : V} (hv : v ≠ x) :
    edeg (famEdges (starTriangles x M)) v ≤ 2 := by
  classical
  -- bound by the sum over triangles of the per-triangle degree, each `≤ 2`, with `≤ 1` triangle at v
  refine le_trans (edeg_biUnion_le (starTriangles x M) cliqueEdges v) ?_
  -- every triangle has three vertices, so its clique edge set has degree `≤ 2` at `v`
  have hcard : ∀ t ∈ starTriangles x M, t.card = 3 := fun t ht => card_starTriangle h ht
  -- the triangles containing `v` number at most one (`v` lies in ≤ 1 matching edge)
  have hle_one : ((starTriangles x M).filter (fun t => v ∈ t)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro t ht t' ht'
    rw [Finset.mem_filter, starTriangles, Finset.mem_image] at ht ht'
    obtain ⟨⟨e, he, rfl⟩, hvt⟩ := ht
    obtain ⟨⟨e', he', rfl⟩, hvt'⟩ := ht'
    have hve : v ∈ e := (Finset.mem_insert.1 hvt).resolve_left hv
    have hve' : v ∈ e' := (Finset.mem_insert.1 hvt').resolve_left hv
    by_contra hne
    have hee' : e ≠ e' := fun hh => hne (by rw [hh])
    exact (Finset.disjoint_left.1 (h.pairwise_disjoint he he' hee') hve) hve'
  -- now sum the per-triangle degrees
  calc ∑ t ∈ starTriangles x M, edeg (cliqueEdges t) v
      = ∑ t ∈ (starTriangles x M).filter (fun t => v ∈ t), edeg (cliqueEdges t) v := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun t ht => ?_
        by_cases hvt : v ∈ t
        · rw [if_pos hvt]
        · rw [if_neg hvt]
          have : edeg (cliqueEdges t) v = 0 := by
            unfold edeg
            rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
            intro e he hve
            exact hvt ((mem_cliqueEdgesV.1 he).1 v hve)
          exact this
    _ ≤ ∑ _t ∈ (starTriangles x M).filter (fun t => v ∈ t), 2 := by
        refine Finset.sum_le_sum fun t ht => ?_
        rw [Finset.mem_filter] at ht
        rw [edeg_cliqueEdges (hcard t ht.1) v, if_pos ht.2]
    _ = 2 * ((starTriangles x M).filter (fun t => v ∈ t)).card := by
        rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
    _ ≤ 2 * 1 := Nat.mul_le_mul_left 2 hle_one
    _ = 2 := by norm_num

end BKLO

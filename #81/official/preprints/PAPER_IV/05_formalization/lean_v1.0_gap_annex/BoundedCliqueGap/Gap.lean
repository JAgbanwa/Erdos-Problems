import BoundedCliqueGap.PEOBridge
import BoundedCliqueGap.THMaster

/-!
# The linear integrality gap of triangle packings on chordal graphs of bounded clique number

This is the headline of the library.  For a finite simple graph `G`,
`BoundedCliqueGap.nu3 G` is the maximum size of an edge-disjoint family of triangles
(`ν₃(G)`, the *integral* triangle packing number) and `BoundedCliqueGap.FracPacking G` is a
feasible solution of its LP relaxation, whose objective is `F.value` (so the optimum of the
LP is `ν₃*(G)`).

## Main results

* `BoundedCliqueGap.chordal_gap_linear_cliqueFree` — **every chordal graph with no clique on
  `d + 2` vertices satisfies `ν₃*(G) ≤ ν₃(G) + (10 + d/2)·|V|`**, unconditionally and with no
  presentation data beyond chordality.
* `BoundedCliqueGap.chordal_gap_linear_of_cliqueTree_width` — the same bound stated through a
  clique tree of width `≤ d`, i.e. in the treewidth form.
* `BoundedCliqueGap.exists_cliqueTree_width_le_iff_cliqueFree` — on a chordal graph the two
  hypotheses agree: a clique tree of width `≤ d` exists iff there is no clique on `d + 2`
  vertices.  This is the identity `treewidth = ω − 1` for chordal graphs, in the form in
  which it is available here.

## Scope: this is the TRIANGULAR gap, not the MIXED gap

The quantity bounded here is the triangular integrality gap `ν₃*(G) − ν₃(G)`: fractional
versus integral **triangle** packings.

It is **not** the mixed gap `W*(G) − W(G)` of the manuscript, where the packing may use
both edges and triangles with their own weights and where the open question concerns the
gains `2` on `K₃` and `K₄`.  Those are different statements about different objective
functions; nothing here is claimed about `W*(G) − W(G)`, and the two must not be conflated
when citing this result.

## On treewidth

Mathlib (v4.28.0) has no `treewidth`, so the "treewidth `≤ d`" hypothesis is expressed
through the tree decomposition this tree does have, `SimpleGraph.CliqueTree`
(`PaperIV/CliqueTree/`): a clique tree with all bags of size `≤ d + 1`.  For a chordal graph
this is exactly a tree decomposition of width `≤ d` of the standard kind — its bags are
cliques — and, by the Helly property of clique trees, its existence is equivalent to
`CliqueFree (d + 2)`, which is the familiar `treewidth = ω − 1` for chordal graphs.
-/

namespace BoundedCliqueGap

open Finset

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- **The theorem.**  Every chordal graph without a clique on `d + 2` vertices has a linear
triangular integrality gap:

`ν₃*(G) ≤ ν₃(G) + (10 + d/2)·|V|`,

unconditionally, with no presentation data beyond chordality (`SimpleGraph.IsChordal`: no
chordless cycle of length `≥ 4`).

Note the scope: this is the **triangular** gap `ν₃* − ν₃`, not the **mixed** gap `W* − W`
of the manuscript (see the module docstring). -/
theorem chordal_gap_linear_cliqueFree {H : SimpleGraph V} {d : ℕ}
    (hc : H.IsChordal) (hk : H.CliqueFree (d + 2)) (F : FracPacking H) :
    F.value ≤ (nu3 H : ℚ) + (10 + (d : ℚ) / 2) * (Fintype.card V : ℚ) := by
  obtain ⟨ord, hpes⟩ := exists_revPES_of_simpleGraph_isChordal hc
  exact gap_linear_of_revPES hpes hk F

/-! ## The treewidth form -/

/-- A clique tree of width `≤ d` forbids cliques on `d + 2` vertices: by the Helly property
its bags contain every clique, and they have at most `d + 1` elements. -/
theorem cliqueFree_of_cliqueTree_width {H : SimpleGraph V} {ι : Type*} {d : ℕ}
    (T : H.CliqueTree ι) (hw : ∀ i, (T.bag i).card ≤ d + 1) : H.CliqueFree (d + 2) := by
  classical
  intro s hs
  obtain ⟨i, hi⟩ := T.exists_subset_bag (K := s)
    (Finset.card_pos.1 (by rw [hs.2]; omega)) hs.1
  have : d + 2 ≤ d + 1 := by
    calc d + 2 = s.card := hs.2.symm
      _ ≤ (T.bag i).card := Finset.card_le_card hi
      _ ≤ d + 1 := hw i
  omega

/-- **The treewidth form of the theorem.**  A chordal graph carrying a clique tree of width
`≤ d` (all bags of size `≤ d + 1`) — equivalently, of treewidth `≤ d`, see
`exists_cliqueTree_width_le_iff_cliqueFree` — has triangular integrality gap at most
`(10 + d/2)·|V|`. -/
theorem chordal_gap_linear_of_cliqueTree_width {H : SimpleGraph V} {ι : Type*} {d : ℕ}
    (hc : H.IsChordal) (T : H.CliqueTree ι) (hw : ∀ i, (T.bag i).card ≤ d + 1)
    (F : FracPacking H) :
    F.value ≤ (nu3 H : ℚ) + (10 + (d : ℚ) / 2) * (Fintype.card V : ℚ) :=
  chordal_gap_linear_cliqueFree hc (cliqueFree_of_cliqueTree_width T hw) F

/-- Conversely, a chordal graph with no clique on `d + 2` vertices carries a clique tree of
width `≤ d`: the bags `{v} ∪ N⁺(v)` of a perfect elimination order are cliques, hence have at
most `d + 1` vertices. -/
theorem exists_cliqueTree_width_le_of_cliqueFree {H : SimpleGraph V} [DecidableRel H.Adj]
    {d : ℕ} (hc : H.IsChordal) (hk : H.CliqueFree (d + 2)) :
    ∃ (ι : Type u) (T : H.CliqueTree ι), ∀ i, (T.bag i).card ≤ d + 1 := by
  classical
  obtain ⟨ord, hord⟩ := hc.exists_isPEO
  refine ⟨V, hord.cliqueTree, fun v => ?_⟩
  by_contra hcard
  push_neg at hcard
  rw [SimpleGraph.IsPEO.cliqueTree_bag] at hcard
  obtain ⟨s, hs, hcards⟩ :=
    Finset.exists_subset_card_eq (show d + 2 ≤ (SimpleGraph.peoBag H ord v).card by omega)
  exact hk s ⟨(hord.peoBag_isClique v).subset (by exact_mod_cast hs), hcards⟩

/-- **`treewidth = ω − 1` on chordal graphs**, in the form available here: a chordal graph
carries a clique tree of width `≤ d` if and only if it has no clique on `d + 2` vertices. -/
theorem exists_cliqueTree_width_le_iff_cliqueFree {H : SimpleGraph V} [DecidableRel H.Adj]
    {d : ℕ} (hc : H.IsChordal) :
    (∃ (ι : Type u) (T : H.CliqueTree ι), ∀ i, (T.bag i).card ≤ d + 1) ↔
      H.CliqueFree (d + 2) :=
  ⟨fun ⟨_, T, hw⟩ => cliqueFree_of_cliqueTree_width T hw,
    fun hk => exists_cliqueTree_width_le_of_cliqueFree hc hk⟩

end BoundedCliqueGap

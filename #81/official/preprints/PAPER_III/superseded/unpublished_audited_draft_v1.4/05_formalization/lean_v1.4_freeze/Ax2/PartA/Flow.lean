/-
  Part A — LP-duality / Farkas bridge (Dross route, step A5).

  Dross's flow / min-cut argument shows the *fractional* triangle decomposition LP is
  feasible. We encode its LP-duality content in the a-posteriori-certificate style of
  Paper IV's `PaperIV.apost_certificate`: instead of solving the LP inside Lean, we expose
  the dual object whose non-existence certifies primal feasibility.

  The fractional decomposition asks for `w ≥ 0` on 3-cliques with the edge-incidence system
  `A w = 𝟙` (every edge covered with total weight exactly `1`). By LP duality / Farkas'
  lemma, this system is feasible iff there is **no** edge-potential `y : Sym2 V → ℝ` that is
  non-negative on every triangle (`∑_{e ∈ t} y e ≥ 0` for all 3-cliques `t`) yet has
  negative total edge potential (`∑_{e ∈ E(G)} y e < 0`). Such a `y` is a Farkas certificate
  of *in*feasibility; ruling it out is exactly what the K₄-counting bound A6 (and the
  extremization A7) achieve for dense graphs.

  STATUS: scaffolding. `fractional_of_no_farkas_potential` (A5) is the LP-duality direction we
  need, stated as a TARGET (sorry): the hard analytic content (strong LP duality for the
  fractional triangle-cover polytope) to be discharged separately. The counting hypothesis it
  consumes is supplied by A6/A7.
-/
import Ax2.Basic

namespace Ax2

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The potential of a 3-clique `t` under an edge-potential `y`: the sum of `y` over the
three edges of `t`. -/
def triPotSum (y : Sym2 V → ℝ) (t : Finset V) : ℝ :=
  ∑ e ∈ triEdges t, y e

/-- The total edge potential of `G` under an edge-potential `y`. -/
def edgePotSum (G : SimpleGraph V) [DecidableRel G.Adj] (y : Sym2 V → ℝ) : ℝ :=
  ∑ e ∈ G.edgeFinset, y e

/-- A **Farkas certificate of infeasibility** for the fractional triangle-decomposition LP:
an edge-potential that is non-negative on every 3-clique yet has strictly negative total
edge potential. -/
def FarkasPotential (G : SimpleGraph V) [DecidableRel G.Adj] (y : Sym2 V → ℝ) : Prop :=
  (∀ t ∈ G.cliqueFinset 3, 0 ≤ triPotSum y t) ∧ edgePotSum G y < 0

-- NOTE: the feasibility direction `(∀ y, ¬ FarkasPotential G y) → FractionalTriangleDecomp G`
-- is proved (sorry-free) as `Ax2.decomp_of_no_farkas` in `Ax2.PartA.FarkasSplit`, which
-- imports this file. It is therefore not restated here.

/-- For a 3-clique `t`, its three edges are genuine edges of `G`. -/
theorem triEdges_subset_edgeFinset (G : SimpleGraph V) [DecidableRel G.Adj]
    {t : Finset V} (ht : t ∈ G.cliqueFinset 3) : triEdges t ⊆ G.edgeFinset := by
  rw [mem_cliqueFinset_iff] at ht
  intro e he
  unfold triEdges at he
  rw [Finset.mem_filter] at he
  obtain ⟨hmem, hdiag⟩ := he
  induction e using Sym2.ind with
  | _ a b =>
    rw [Finset.mk_mem_sym2_iff] at hmem
    rw [Sym2.mk_isDiag_iff] at hdiag
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact ht.1 hmem.1 hmem.2 hdiag

/-- The contrapositive convenience form: a Farkas potential obstructs the fractional
decomposition. This direction is the *easy* (weak-duality) one — a feasible `w` pairs with
any triangle-nonnegative `y` to force `0 ≤ ∑_e y e`, contradicting `edgePotSum < 0`. -/
theorem not_farkas_of_fractional (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfrac : FractionalTriangleDecomp G) :
    ∀ y : Sym2 V → ℝ, ¬ FarkasPotential G y := by
  obtain ⟨w, hw, hcov⟩ := hfrac
  intro y hy
  obtain ⟨htri, hneg⟩ := hy
  -- Fubini: total edge potential = ∑ over triangles of w·(triangle potential).
  have key : edgePotSum G y = ∑ t ∈ G.cliqueFinset 3, w t * triPotSum y t := by
    unfold edgePotSum
    have h1 : ∑ e ∈ G.edgeFinset, y e
        = ∑ e ∈ G.edgeFinset, ∑ t ∈ G.cliqueFinset 3,
            (if e ∈ triEdges t then w t else 0) * y e := by
      apply Finset.sum_congr rfl
      intro e he
      conv_lhs => rw [← one_mul (y e), ← hcov e he, Finset.sum_mul]
    rw [h1, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t ht
    have hite : ∀ e, (if e ∈ triEdges t then w t else 0) * y e
        = if e ∈ triEdges t then w t * y e else 0 := by
      intro e; split_ifs <;> ring
    simp_rw [hite]
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr (triEdges_subset_edgeFinset G ht),
      triPotSum, Finset.mul_sum]
  have hpos : 0 ≤ ∑ t ∈ G.cliqueFinset 3, w t * triPotSum y t :=
    Finset.sum_nonneg (fun t ht => mul_nonneg (hw t) (htri t ht))
  rw [key] at hneg
  linarith

end Ax2

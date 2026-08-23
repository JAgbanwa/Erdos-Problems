/-
# The accumulated budget of BKLO Lemma 10.3 (r = 2): degree at `v` is `≤ 2 ·` (apices touching `v`)

The greedy sweep of Lemma 10.3 accumulates, over the apices `x ∈ U`, the star-triangle edge sets
`famEdges (starTriangles x (Mx x))`.  Their union `D` is the used set.  This file proves, `sorry`-free,
the accumulation bound that turns the per-apex fact
`BKLO.edeg_famEdges_starTriangles_le_two` (each apex contributes `≤ 2` to a non-apex degree) into the
global budget: for a vertex `v` distinct from every apex,

  `edeg D v ≤ 2 · #{ x ∈ U : v is matched by Mx x }`.

Since a vertex is matched by an apex `x` only if it lies in `N_H(x,W)` (so `x` is a neighbour of `v`
inside `U`), the right-hand count is bounded by `d_H(v,U)`, and Lemma 10.3(iii)
(`d_H(v,U) ≤ γ|W|/2`) then yields `edeg D v ≤ γ|W|` — condition Dirac needs at every later step, and
the `Δ(H_V) ≤ γ|W|` conclusion of the lemma.

Everything here is `sorry`-free.
-/
import BKLO.CoverDownBudgetInvariant
import BKLO.Section10Defs

open Finset

namespace BKLO

variable {V : Type} [DecidableEq V]

/-- A star at `x` over `M` contributes nothing to a vertex `v` that is neither `x` nor matched by
`M` — `v` lies in no triangle `{x} ∪ e`, so in no clique edge of the star. -/
theorem edeg_famEdges_starTriangles_eq_zero {x : V} {M : Finset (Finset V)}
    {v : V} (hvx : v ≠ x) (hvM : ∀ e ∈ M, v ∉ e) :
    edeg (famEdges (starTriangles x M)) v = 0 := by
  classical
  refine Nat.le_zero.1 ?_
  refine le_trans (edeg_biUnion_le (starTriangles x M) cliqueEdges v) ?_
  refine le_trans (Finset.sum_le_sum (g := fun _ => 0) ?_) (by simp)
  intro t ht
  rw [starTriangles, Finset.mem_image] at ht
  obtain ⟨e, he, rfl⟩ := ht
  have hvt : v ∉ insert x e := by
    rw [Finset.mem_insert]; push_neg; exact ⟨hvx, hvM e he⟩
  refine Nat.le_zero.2 ?_
  unfold edeg
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro g hg hvg
  exact hvt ((mem_cliqueEdgesV.1 hg).1 v hvg)

/-- **The accumulated budget bound.**  For a vertex `v` distinct from every apex of `U`, the used set
`D = ⋃_{x ∈ U} famEdges (starTriangles x (Mx x))` has edge degree at `v` bounded by `2` times the
number of apices whose matching touches `v`. -/
theorem edeg_biUnion_starTriangles_le_count {U : Finset V} {Mx : V → Finset (Finset V)}
    (hM : ∀ x ∈ U, IsMatchingAvoiding (Mx x) x) {v : V} (hv : ∀ x ∈ U, v ≠ x) :
    edeg (U.biUnion (fun x => famEdges (starTriangles x (Mx x)))) v
      ≤ 2 * (U.filter (fun x => ∃ e ∈ Mx x, v ∈ e)).card := by
  classical
  refine le_trans (edeg_biUnion_le U (fun x => famEdges (starTriangles x (Mx x))) v) ?_
  calc ∑ x ∈ U, edeg (famEdges (starTriangles x (Mx x))) v
      = ∑ x ∈ U.filter (fun x => ∃ e ∈ Mx x, v ∈ e),
          edeg (famEdges (starTriangles x (Mx x))) v := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun x hx => ?_
        by_cases hxe : ∃ e ∈ Mx x, v ∈ e
        · rw [if_pos hxe]
        · rw [if_neg hxe]
          push_neg at hxe
          exact edeg_famEdges_starTriangles_eq_zero (hv x hx) hxe
    _ ≤ ∑ _x ∈ U.filter (fun x => ∃ e ∈ Mx x, v ∈ e), 2 := by
        refine Finset.sum_le_sum fun x hx => ?_
        rw [Finset.mem_filter] at hx
        exact edeg_famEdges_starTriangles_le_two (hM x hx.1) (hv x hx.1)
    _ = 2 * (U.filter (fun x => ∃ e ∈ Mx x, v ∈ e)).card := by
        rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]

/-- **Apices touching `v` are neighbours of `v` in `U`.**  If every matching edge of every apex lies
inside that apex's neighbourhood `N_H(x,W)`, then an apex `x` whose matching touches `v` satisfies
`s(x,v) ∈ H`, i.e. `x ∈ N_H(v,U)`.  Hence the touching apices number at most `d_H(v,U)`. -/
theorem card_apices_touching_le_degTo {H : Finset (Sym2 V)} {U W : Finset V}
    {Mx : V → Finset (Finset V)} {v : V}
    (hsub : ∀ x ∈ U, ∀ e ∈ Mx x, e ⊆ nbhdIn H x W) :
    (U.filter (fun x => ∃ e ∈ Mx x, v ∈ e)).card ≤ degTo H v U := by
  classical
  refine Finset.card_le_card ?_
  intro x hx
  rw [Finset.mem_filter] at hx
  obtain ⟨hxU, e, he, hve⟩ := hx
  have hvnb : v ∈ nbhdIn H x W := hsub x hxU e he hve
  rw [mem_nbhdIn] at hvnb
  rw [mem_nbhdIn]
  refine ⟨hxU, ?_⟩
  rw [Sym2.eq_swap]
  exact hvnb.2

/-- **The accumulated budget, in `d_H(v,U)` form.**  Combining the two facts above: for `v` distinct
from every apex, with every matching edge inside its apex's neighbourhood, `edeg D v ≤ 2 · d_H(v,U)`.
This is the bound that Lemma 10.3(iii) (`d_H(v,U) ≤ γ|W|/2`) turns into `edeg D v ≤ γ|W|`. -/
theorem edeg_biUnion_starTriangles_le_two_degTo {H : Finset (Sym2 V)} {U W : Finset V}
    {Mx : V → Finset (Finset V)}
    (hM : ∀ x ∈ U, IsMatchingAvoiding (Mx x) x) {v : V} (hv : ∀ x ∈ U, v ≠ x)
    (hsub : ∀ x ∈ U, ∀ e ∈ Mx x, e ⊆ nbhdIn H x W) :
    edeg (U.biUnion (fun x => famEdges (starTriangles x (Mx x)))) v ≤ 2 * degTo H v U :=
  le_trans (edeg_biUnion_starTriangles_le_count hM hv)
    (Nat.mul_le_mul_left 2 (card_apices_touching_le_degTo hsub))

end BKLO

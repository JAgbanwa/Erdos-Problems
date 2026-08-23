/-
# Nibble — the `K₄` exchange gadget for fractional triangle decompositions

`Nibble/DrossSpread.lean` reduces the spread Dross input `Nibble.DrossFractionalQuantSpread` to a
*signed* correction of the uniform triangle weighting `1/(|V|-2)`
(`Nibble.IsUniformDeficiencyCorrection`).  This file provides the natural device for building such
corrections, and turns the residual into a **nonnegative** (sign-free) routing problem.

For a `K₄` on `{x, y, z, u}` in `G`, the signed triangle weighting

  `+1` on `xyu`, `xzu`, `yzu`  and  `-1` on `xyz`

changes the total weight carried by an edge by `+2` on each of the three *star* edges `xu`, `yu`,
`zu`, and by `0` on every other edge of `G` — the three "core" edges `xy`, `xz`, `yz` cancel.

* `Nibble.sum_trianglesThrough_eq` — the dictionary between summing over the hyperedge model of
  triangles and summing over `3`-cliques.
* `Nibble.k4Gadget` — the gadget weighting.
* `Nibble.k4Gadget_coverage` — **its coverage**: `2` on the star of the apex `u` inside the `K₄`,
  and `0` on every other edge.
* `Nibble.IsGadgetRouting`, `Nibble.isUniformDeficiencyCorrection_of_gadgetRouting` — a sign-free
  sufficient condition for the residual: nonnegative gadget coefficients whose star deliveries meet
  the uniform deficiency exactly, and whose total usage of any single triangle stays inside the
  uniform budget `1/(|V|-2)`.

Sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.DrossSpread

open Finset SimpleGraph Hypergraph Nibble.YusterE

namespace Nibble

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ### Summing over triangles through an edge -/

/-- **The dictionary.**  Summing a function of the vertex set of a triangle over the triangles
through an edge `e` is summing it over the `3`-cliques containing `e`. -/
theorem sum_trianglesThrough_eq (G : SimpleGraph V) [DecidableRel G.Adj] (e : EdgeV G)
    (F : Finset V → ℝ) :
    ∑ T ∈ trianglesThrough G e, F (triOf G T)
      = ∑ t ∈ (G.cliqueFinset 3).filter (fun t => e.val ⊆ t), F t := by
  classical
  have hecard : (e.val).card = 2 := (SimpleGraph.mem_cliqueFinset_iff.mp e.property).card_eq
  refine Finset.sum_bij' (fun T _ => triOf G T)
    (fun t _ => (t.powersetCard 2).subtype (· ∈ G.cliqueFinset 2)) ?_ ?_ ?_ ?_ ?_
  · intro T hT
    show triOf G T ∈ _
    rw [trianglesThrough, Finset.mem_filter] at hT
    obtain ⟨t, ht, rfl⟩ := (mem_triangleHypergraphSub_iff G).mp hT.1
    rw [triOf_subtype G ht, Finset.mem_filter, SimpleGraph.mem_cliqueFinset_iff]
    refine ⟨ht, ?_⟩
    have := hT.2
    rw [Finset.mem_subtype, Finset.mem_powersetCard] at this
    exact this.1
  · intro t ht
    show (t.powersetCard 2).subtype (· ∈ G.cliqueFinset 2) ∈ _
    rw [Finset.mem_filter, SimpleGraph.mem_cliqueFinset_iff] at ht
    rw [trianglesThrough, Finset.mem_filter]
    refine ⟨(mem_triangleHypergraphSub_iff G).mpr ⟨t, ht.1, rfl⟩, ?_⟩
    rw [Finset.mem_subtype, Finset.mem_powersetCard]
    exact ⟨ht.2, hecard⟩
  · intro T hT
    show ((triOf G T).powersetCard 2).subtype (· ∈ G.cliqueFinset 2) = T
    rw [trianglesThrough, Finset.mem_filter] at hT
    obtain ⟨t, ht, rfl⟩ := (mem_triangleHypergraphSub_iff G).mp hT.1
    rw [triOf_subtype G ht]
  · intro t ht
    show triOf G ((t.powersetCard 2).subtype (· ∈ G.cliqueFinset 2)) = t
    rw [Finset.mem_filter, SimpleGraph.mem_cliqueFinset_iff] at ht
    exact triOf_subtype G ht.1
  · intro T _
    rfl

/-! ### The gadget -/

/-- **The `K₄` exchange gadget** with apex `u` and core `{x, y, z}`: weight `+1` on each of the
three triangles through `u`, weight `-1` on the core triangle. -/
noncomputable def k4Gadget (G : SimpleGraph V) [DecidableRel G.Adj] (x y z u : V)
    (T : Finset (EdgeV G)) : ℝ :=
  (if triOf G T = {x, y, u} then (1 : ℝ) else 0) + (if triOf G T = {x, z, u} then (1 : ℝ) else 0)
    + (if triOf G T = {y, z, u} then (1 : ℝ) else 0)
    - (if triOf G T = {x, y, z} then (1 : ℝ) else 0)

/-- **The usage** of a triangle by a gadget: the number of the gadget's four triangles it is. -/
noncomputable def k4Usage (G : SimpleGraph V) [DecidableRel G.Adj] (x y z u : V)
    (T : Finset (EdgeV G)) : ℝ :=
  (if triOf G T = {x, y, u} then (1 : ℝ) else 0) + (if triOf G T = {x, z, u} then (1 : ℝ) else 0)
    + (if triOf G T = {y, z, u} then (1 : ℝ) else 0)
    + (if triOf G T = {x, y, z} then (1 : ℝ) else 0)

/-- The gadget is bounded in absolute value by the usage. -/
theorem abs_k4Gadget_le_usage (G : SimpleGraph V) [DecidableRel G.Adj] (x y z u : V)
    (T : Finset (EdgeV G)) : |k4Gadget G x y z u T| ≤ k4Usage G x y z u T := by
  classical
  have hA : (0 : ℝ) ≤ (if triOf G T = ({x, y, u} : Finset V) then (1 : ℝ) else 0) := by
    split <;> norm_num
  have hB : (0 : ℝ) ≤ (if triOf G T = ({x, z, u} : Finset V) then (1 : ℝ) else 0) := by
    split <;> norm_num
  have hC : (0 : ℝ) ≤ (if triOf G T = ({y, z, u} : Finset V) then (1 : ℝ) else 0) := by
    split <;> norm_num
  have hD : (0 : ℝ) ≤ (if triOf G T = ({x, y, z} : Finset V) then (1 : ℝ) else 0) := by
    split <;> norm_num
  rw [k4Gadget, k4Usage, abs_le]
  constructor <;> linarith

omit [Fintype V] in
/-- The four indicator evaluation behind `Nibble.k4Gadget_coverage`. -/
theorem gadget_indicator_eval (x y z u p q : V) (hpq : p ≠ q)
    (hxy : x ≠ y) (hxz : x ≠ z) (hxu : x ≠ u) (hyz : y ≠ z) (hyu : y ≠ u) (hzu : z ≠ u) :
    (if ({p, q} : Finset V) ⊆ ({x, y, u} : Finset V) then (1 : ℝ) else 0)
      + (if ({p, q} : Finset V) ⊆ ({x, z, u} : Finset V) then (1 : ℝ) else 0)
      + (if ({p, q} : Finset V) ⊆ ({y, z, u} : Finset V) then (1 : ℝ) else 0)
      - (if ({p, q} : Finset V) ⊆ ({x, y, z} : Finset V) then (1 : ℝ) else 0)
      = if (u ∈ ({p, q} : Finset V) ∧ ({p, q} : Finset V) ⊆ ({x, y, z, u} : Finset V))
          then (2 : ℝ) else 0 := by
  classical
  have hqp : q ≠ p := hpq.symm
  have hyx : y ≠ x := hxy.symm
  have hzx : z ≠ x := hxz.symm
  have hux : u ≠ x := hxu.symm
  have hzy : z ≠ y := hyz.symm
  have huy : u ≠ y := hyu.symm
  have huz : u ≠ z := hzu.symm
  by_cases hp : p ∈ ({x, y, z, u} : Finset V)
  · by_cases hq : q ∈ ({x, y, z, u} : Finset V)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
      rcases hp with rfl | rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl | rfl <;>
        simp_all [Finset.subset_iff] <;> norm_num
    · have h1 : ¬ (({p, q} : Finset V) ⊆ ({x, y, z, u} : Finset V)) := by
        intro hsub; exact hq (hsub (by simp))
      have h2 : ∀ A : Finset V, A ⊆ ({x, y, z, u} : Finset V) → ¬ (({p, q} : Finset V) ⊆ A) :=
        fun A hA hsub => h1 (hsub.trans hA)
      rw [if_neg (h2 _ (by intro a ha; simp at ha ⊢; tauto)),
        if_neg (h2 _ (by intro a ha; simp at ha ⊢; tauto)),
        if_neg (h2 _ (by intro a ha; simp at ha ⊢; tauto)),
        if_neg (h2 _ (by intro a ha; simp at ha ⊢; tauto)), if_neg (by tauto)]
      norm_num
  · have h1 : ¬ (({p, q} : Finset V) ⊆ ({x, y, z, u} : Finset V)) := by
      intro hsub; exact hp (hsub (by simp))
    have h2 : ∀ A : Finset V, A ⊆ ({x, y, z, u} : Finset V) → ¬ (({p, q} : Finset V) ⊆ A) :=
      fun A hA hsub => h1 (hsub.trans hA)
    rw [if_neg (h2 _ (by intro a ha; simp at ha ⊢; tauto)),
      if_neg (h2 _ (by intro a ha; simp at ha ⊢; tauto)),
      if_neg (h2 _ (by intro a ha; simp at ha ⊢; tauto)),
      if_neg (h2 _ (by intro a ha; simp at ha ⊢; tauto)), if_neg (by tauto)]
    norm_num

/-- **The coverage of the gadget.**  On a `K₄` `{x, y, z, u}` of `G` the gadget with apex `u` adds
exactly `2` to the coverage of each of the three edges of the star of `u`, and `0` to the coverage
of every other edge of `G`. -/
theorem k4Gadget_coverage (G : SimpleGraph V) [DecidableRel G.Adj] {x y z u : V}
    (hxy : G.Adj x y) (hxz : G.Adj x z) (hyz : G.Adj y z)
    (hxu : G.Adj x u) (hyu : G.Adj y u) (hzu : G.Adj z u) (e : EdgeV G) :
    ∑ T ∈ trianglesThrough G e, k4Gadget G x y z u T
      = if (u ∈ e.val ∧ e.val ⊆ ({x, y, z, u} : Finset V)) then (2 : ℝ) else 0 := by
  classical
  have hxyu : G.IsNClique 3 ({x, y, u} : Finset V) :=
    SimpleGraph.is3Clique_triple_iff.mpr ⟨hxy, hxu, hyu⟩
  have hxzu : G.IsNClique 3 ({x, z, u} : Finset V) :=
    SimpleGraph.is3Clique_triple_iff.mpr ⟨hxz, hxu, hzu⟩
  have hyzu : G.IsNClique 3 ({y, z, u} : Finset V) :=
    SimpleGraph.is3Clique_triple_iff.mpr ⟨hyz, hyu, hzu⟩
  have hxyz : G.IsNClique 3 ({x, y, z} : Finset V) :=
    SimpleGraph.is3Clique_triple_iff.mpr ⟨hxy, hxz, hyz⟩
  have hF := sum_trianglesThrough_eq G e (fun s : Finset V =>
      (if s = ({x, y, u} : Finset V) then (1 : ℝ) else 0)
        + (if s = ({x, z, u} : Finset V) then (1 : ℝ) else 0)
        + (if s = ({y, z, u} : Finset V) then (1 : ℝ) else 0)
        - (if s = ({x, y, z} : Finset V) then (1 : ℝ) else 0))
  rw [show (∑ T ∈ trianglesThrough G e, k4Gadget G x y z u T) = _ from hF]
  have hstep : ∑ t ∈ (G.cliqueFinset 3).filter (fun t => e.val ⊆ t),
      ((if t = ({x, y, u} : Finset V) then (1 : ℝ) else 0)
        + (if t = ({x, z, u} : Finset V) then (1 : ℝ) else 0)
        + (if t = ({y, z, u} : Finset V) then (1 : ℝ) else 0)
        - (if t = ({x, y, z} : Finset V) then (1 : ℝ) else 0))
      = (if e.val ⊆ ({x, y, u} : Finset V) then (1 : ℝ) else 0)
        + (if e.val ⊆ ({x, z, u} : Finset V) then (1 : ℝ) else 0)
        + (if e.val ⊆ ({y, z, u} : Finset V) then (1 : ℝ) else 0)
        - (if e.val ⊆ ({x, y, z} : Finset V) then (1 : ℝ) else 0) := by
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq',
      Finset.mem_filter, SimpleGraph.mem_cliqueFinset_iff]
    simp [hxyu, hxzu, hyzu, hxyz]
  rw [hstep]
  obtain ⟨p, q, hpq, -, hval⟩ := exists_pair_of_edgeV G e
  rw [hval]
  exact gadget_indicator_eval x y z u p q hpq hxy.ne hxz.ne hxu.ne hyz.ne hyu.ne hzu.ne

/-! ### The sign-free residual: routing the uniform deficiency through gadgets -/

/-- The `K₄` predicate on an ordered quadruple: the core `{x,y,z}` is a triangle and the apex `u`
is joined to all of it. -/
def IsK4 (G : SimpleGraph V) (w : V × V × V × V) : Prop :=
  G.Adj w.1 w.2.1 ∧ G.Adj w.1 w.2.2.1 ∧ G.Adj w.2.1 w.2.2.1 ∧
    G.Adj w.1 w.2.2.2 ∧ G.Adj w.2.1 w.2.2.2 ∧ G.Adj w.2.2.1 w.2.2.2

/-- The correction assembled from gadget coefficients `a`. -/
noncomputable def gadgetCorrection (G : SimpleGraph V) [DecidableRel G.Adj]
    (a : V × V × V × V → ℝ) (T : Finset (EdgeV G)) : ℝ :=
  ∑ w : V × V × V × V, a w * k4Gadget G w.1 w.2.1 w.2.2.1 w.2.2.2 T

/-- **A gadget routing of the uniform deficiency.**  Nonnegative coefficients on `K₄`s such that

* the stars deliver exactly the uniform deficiency at every edge, and
* no triangle is used, in total, beyond the uniform budget `1/(|V|-2)`.

This is a *sign-free* sufficient form of `Nibble.IsUniformDeficiencyCorrection`. -/
def IsGadgetRouting (G : SimpleGraph V) [DecidableRel G.Adj] (a : V × V × V × V → ℝ) : Prop :=
  (∀ w, 0 ≤ a w) ∧
  (∀ w, a w ≠ 0 → IsK4 G w) ∧
  (∀ e : EdgeV G,
    ∑ w ∈ (Finset.univ : Finset (V × V × V × V)).filter
        (fun w => w.2.2.2 ∈ e.val ∧ e.val ⊆ ({w.1, w.2.1, w.2.2.1, w.2.2.2} : Finset V)),
      2 * a w = 1 - ((commonNbrs G e).card : ℝ) / ((Fintype.card V : ℝ) - 2)) ∧
  (∀ T ∈ triangleHypergraphSub G,
    ∑ w : V × V × V × V, a w * k4Usage G w.1 w.2.1 w.2.2.1 w.2.2.2 T
      ≤ 1 / ((Fintype.card V : ℝ) - 2))

/-- **A gadget routing is a bounded uniform-deficiency correction.**  Hence, by
`Nibble.exists_correction_iff_bounded_decomp` and
`Nibble.drossFractionalQuantSpread_of_correction`, routing the deficiency through `K₄` gadgets at
the Dross density suffices for the whole chain. -/
theorem isUniformDeficiencyCorrection_of_gadgetRouting (G : SimpleGraph V) [DecidableRel G.Adj]
    {a : V × V × V × V → ℝ} (ha : IsGadgetRouting G a) :
    IsUniformDeficiencyCorrection G (gadgetCorrection G a) := by
  classical
  obtain ⟨hnn, hsupp, hdem, hcap⟩ := ha
  constructor
  · -- the bound
    intro T hT
    calc |gadgetCorrection G a T|
        ≤ ∑ w : V × V × V × V, |a w * k4Gadget G w.1 w.2.1 w.2.2.1 w.2.2.2 T| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ w : V × V × V × V, a w * k4Usage G w.1 w.2.1 w.2.2.1 w.2.2.2 T := by
          refine Finset.sum_le_sum (fun w _ => ?_)
          rw [abs_mul, abs_of_nonneg (hnn w)]
          exact mul_le_mul_of_nonneg_left (abs_k4Gadget_le_usage G _ _ _ _ T) (hnn w)
      _ ≤ 1 / ((Fintype.card V : ℝ) - 2) := hcap T hT
  · -- the coverage
    intro e
    have hswap : ∑ T ∈ trianglesThrough G e, gadgetCorrection G a T
        = ∑ w : V × V × V × V,
            a w * (∑ T ∈ trianglesThrough G e, k4Gadget G w.1 w.2.1 w.2.2.1 w.2.2.2 T) := by
      simp only [gadgetCorrection, Finset.mul_sum]
      exact Finset.sum_comm
    rw [hswap]
    have hterm : ∀ w : V × V × V × V,
        a w * (∑ T ∈ trianglesThrough G e, k4Gadget G w.1 w.2.1 w.2.2.1 w.2.2.2 T)
          = a w * (if (w.2.2.2 ∈ e.val ∧ e.val ⊆ ({w.1, w.2.1, w.2.2.1, w.2.2.2} : Finset V))
              then (2 : ℝ) else 0) := by
      intro w
      by_cases hw : a w = 0
      · rw [hw, zero_mul, zero_mul]
      · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hsupp w hw
        rw [k4Gadget_coverage G h1 h2 h3 h4 h5 h6 e]
    rw [Finset.sum_congr rfl (fun w _ => hterm w)]
    rw [← hdem e, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    by_cases hcond : (w.2.2.2 ∈ e.val ∧ e.val ⊆ ({w.1, w.2.1, w.2.2.1, w.2.2.2} : Finset V))
    · rw [if_pos hcond, if_pos hcond, mul_comm]
    · rw [if_neg hcond, if_neg hcond, mul_zero]

/-- **The sign-free route to the target.**  If at the Dross density the uniform deficiency can be
routed through `K₄` gadgets, then `Nibble.DrossFractionalQuantSpread` holds (with `C = 3`), and with
it the whole chain down to `Nibble.DenseTriangleNibbleDeg`. -/
theorem drossFractionalQuantSpread_of_gadgetRouting
    (h : ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      9 * Fintype.card V ≤ 10 * G.minDegree → ∃ a : V × V × V × V → ℝ, IsGadgetRouting G a) :
    DrossFractionalQuantSpread := by
  refine drossFractionalQuantSpread_of_correction ?_
  intro V _ _ G _ hdense
  obtain ⟨a, ha⟩ := h G hdense
  exact ⟨gadgetCorrection G a, isUniformDeficiencyCorrection_of_gadgetRouting G ha⟩

/-- **Non-vacuity.**  On the complete graph the uniform weighting is already exact, so the empty
routing works. -/
theorem isGadgetRouting_zero_top (hV : 3 ≤ Fintype.card V) :
    IsGadgetRouting (⊤ : SimpleGraph V) (fun _ => (0 : ℝ)) := by
  classical
  have h3 : (3 : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast hV
  have h2 : (0 : ℝ) < (Fintype.card V : ℝ) - 2 := by linarith only [h3]
  refine ⟨fun _ => le_rfl, fun w hw => absurd rfl hw, fun e => ?_, fun T _ => ?_⟩
  · have hcod : ((commonNbrs (⊤ : SimpleGraph V) e).card : ℝ) = (Fintype.card V : ℝ) - 2 := by
      have h := card_triangles_through_edge_top e
      rw [card_trianglesThrough_eq_commonNbrs] at h
      have : ((commonNbrs (⊤ : SimpleGraph V) e).card : ℝ) = ((Fintype.card V - 2 : ℕ) : ℝ) := by
        exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) h
      rw [this, Nat.cast_sub (by omega)]
      norm_num
    rw [hcod, div_self (ne_of_gt h2)]
    simp
  · simp only [zero_mul, Finset.sum_const_zero]
    positivity

end Nibble

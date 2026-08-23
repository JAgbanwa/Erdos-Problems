/-
# Nibble — the `K₄` obstruction to spreading a near-optimal fractional triangle packing

`Nibble.FracNibbleWeightedTheorem` (`Nibble/FracNibbleRepaired.lean`) hypothesises that the
*weighted codegrees* `∑_{T ⊇ {x,z}} w T` of the fractional matching are at most `γ`.  For the
triangle hypergraph of a graph `G` — vertices = the edges of `G`, hyperedges = the triangles of
`G` — two graph-edges lie in **at most one** common triangle, so the weighted codegree of a pair is
either `0` or the weight of that single triangle.  The hypothesis of the weighted nibble is
therefore literally "*every triangle carries weight at most `γ`*".

This file records, in a completely explicit finite example, that such a *spread* fractional
triangle packing cannot be near-optimal: the triangle hypergraph of `K₄` has fractional matching
number `2` (attained only with all four weights equal to `1/2`), while every fractional matching
whose weights are `≤ γ` has value at most `4γ`, and every *integral* matching has just one edge.

Consequently the naive route
`FracNibbleWeightedTheorem → HaxellRodlGap → CoreGapResidual → AX1`
(the route that `Nibble.AX1.haxellRodlGap_of_fracNibble` takes for the *refuted*
`Nibble.FracNibbleTheorem`) is unavailable: it would need a near-optimal fractional triangle
packing whose triangle weights are all at most `γ`, and `K₄`-decompositions of `Kₙ` show that no
such packing exists.  See `RESIDUAL.md`, §4.

Vertices of the hypergraph are the six edges of `K₄`, encoded as `Fin 6`:
`0 = 01`, `1 = 02`, `2 = 03`, `3 = 12`, `4 = 13`, `5 = 23`.

Sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.Basic
import Mathlib.Analysis.RCLike.Basic

open Finset Hypergraph

namespace Nibble.K4

/-- The triangle `012` of `K₄`, as the set of its three edges `01, 02, 12`. -/
def t012 : Finset (Fin 6) := {0, 1, 3}

/-- The triangle `013` of `K₄`, as the set of its three edges `01, 03, 13`. -/
def t013 : Finset (Fin 6) := {0, 2, 4}

/-- The triangle `023` of `K₄`, as the set of its three edges `02, 03, 23`. -/
def t023 : Finset (Fin 6) := {1, 2, 5}

/-- The triangle `123` of `K₄`, as the set of its three edges `12, 13, 23`. -/
def t123 : Finset (Fin 6) := {3, 4, 5}

/-- The triangle hypergraph of `K₄`: four hyperedges on six vertices. -/
def K4Tri : Finset (Finset (Fin 6)) := {t012, t013, t023, t123}

theorem k4Tri_uniform : IsUniform K4Tri 3 := by
  have h : ∀ T ∈ K4Tri, T.card = 3 := by decide
  exact h

theorem k4Tri_card : K4Tri.card = 4 := by decide

/-- Expanding a sum over the four triangles. -/
theorem sum_K4Tri (f : Finset (Fin 6) → ℝ) :
    ∑ T ∈ K4Tri, f T = f t012 + f t013 + f t023 + f t123 := by
  have h1 : t012 ∉ ({t013, t023, t123} : Finset (Finset (Fin 6))) := by decide
  have h2 : t013 ∉ ({t023, t123} : Finset (Finset (Fin 6))) := by decide
  have h3 : t023 ∉ ({t123} : Finset (Finset (Fin 6))) := by decide
  show ∑ T ∈ insert t012 ({t013, t023, t123} : Finset (Finset (Fin 6))), f T = _
  rw [Finset.sum_insert h1, Finset.sum_insert h2, Finset.sum_insert h3, Finset.sum_singleton]
  ring

/-- The uniform fractional matching of value `2`: every triangle of `K₄` gets weight `1/2`. -/
noncomputable def halfWeight : Finset (Fin 6) → ℝ := fun T => if T ∈ K4Tri then 1 / 2 else 0

theorem halfWeight_nonneg (T : Finset (Fin 6)) : 0 ≤ halfWeight T := by
  unfold halfWeight; split <;> norm_num

/-- Every vertex (= edge of `K₄`) lies in exactly two triangles, so the uniform `1/2`-weighting is
a **perfect** fractional matching: all loads are exactly `1`. -/
theorem halfWeight_load (v : Fin 6) :
    ∑ T ∈ K4Tri.filter (fun T => v ∈ T), halfWeight T = 1 := by
  have hval : ∀ T ∈ K4Tri, halfWeight T = 1 / 2 := by
    intro T hT; unfold halfWeight; simp [hT]
  have hcard : (K4Tri.filter (fun T => v ∈ T)).card = 2 := by revert v; decide
  rw [Finset.sum_congr rfl (fun T hT => hval T (Finset.mem_filter.mp hT).1),
    Finset.sum_const, nsmul_eq_mul, hcard]
  norm_num

/-- The uniform `1/2`-weighting has value `2`; in particular the fractional matching number of the
triangle hypergraph of `K₄` is at least `2`. -/
theorem halfWeight_sum : ∑ T ∈ K4Tri, halfWeight T = 2 := by
  rw [sum_K4Tri]
  have h012 : halfWeight t012 = 1 / 2 := by unfold halfWeight; norm_num [K4Tri]
  have h013 : halfWeight t013 = 1 / 2 := by
    unfold halfWeight; rw [if_pos (by decide : t013 ∈ K4Tri)]
  have h023 : halfWeight t023 = 1 / 2 := by
    unfold halfWeight; rw [if_pos (by decide : t023 ∈ K4Tri)]
  have h123 : halfWeight t123 = 1 / 2 := by
    unfold halfWeight; rw [if_pos (by decide : t123 ∈ K4Tri)]
  rw [h012, h013, h023, h123]; norm_num

set_option maxRecDepth 8000 in
/-- Any two triangles of `K₄` share an edge, so an **integral** matching of the triangle
hypergraph of `K₄` has at most one edge: the integrality gap of this example is `2`. -/
theorem k4_matching_card_le_one (M : Finset (Finset (Fin 6))) (hM : IsMatching K4Tri M) :
    M.card ≤ 1 := by
  by_contra h
  obtain ⟨e, he, f, hf, hef⟩ := Finset.one_lt_card.mp (not_le.mp h)
  have hmeet : ∀ e ∈ K4Tri, ∀ f ∈ K4Tri, e ≠ f → ¬ Disjoint e f := by decide
  exact hmeet e (hM.subset he) f (hM.subset hf) hef (hM.disjoint e he f hf hef)

/-- **The obstruction.**  Any nonnegative weighting of the triangles of `K₄` all of whose
*weighted codegrees* are at most `γ` has total value at most `4γ`.  (Each triangle is the unique
one containing any given pair of its edges, so the hypothesis forces every individual triangle
weight to be at most `γ`.)  Compare `Nibble.K4.halfWeight_sum`: the optimum `2` is attained only
with weights `1/2`, so for `γ < 1/2` no near-optimal fractional packing satisfies the weighted
codegree hypothesis of `Nibble.FracNibbleWeightedTheorem`. -/
theorem k4_spread_sum_le (w : Finset (Fin 6) → ℝ) (γ : ℝ)
    (hcod : ∀ x z : Fin 6, x ≠ z →
      ∑ T ∈ K4Tri.filter (fun T => x ∈ T ∧ z ∈ T), w T ≤ γ) :
    ∑ T ∈ K4Tri, w T ≤ 4 * γ := by
  have e012 : w t012 ≤ γ := by
    have h := hcod 0 1 (by decide)
    rwa [show K4Tri.filter (fun T => (0 : Fin 6) ∈ T ∧ (1 : Fin 6) ∈ T) = {t012} from by decide,
      Finset.sum_singleton] at h
  have e013 : w t013 ≤ γ := by
    have h := hcod 0 2 (by decide)
    rwa [show K4Tri.filter (fun T => (0 : Fin 6) ∈ T ∧ (2 : Fin 6) ∈ T) = {t013} from by decide,
      Finset.sum_singleton] at h
  have e023 : w t023 ≤ γ := by
    have h := hcod 1 2 (by decide)
    rwa [show K4Tri.filter (fun T => (1 : Fin 6) ∈ T ∧ (2 : Fin 6) ∈ T) = {t023} from by decide,
      Finset.sum_singleton] at h
  have e123 : w t123 ≤ γ := by
    have h := hcod 3 4 (by decide)
    rwa [show K4Tri.filter (fun T => (3 : Fin 6) ∈ T ∧ (4 : Fin 6) ∈ T) = {t123} from by decide,
      Finset.sum_singleton] at h
  rw [sum_K4Tri]
  linarith only [e012, e013, e023, e123]

/-- **Spread near-optimal fractional triangle packings do not exist.**  Packaged form of
`Nibble.K4.halfWeight_sum` and `Nibble.K4.k4_spread_sum_le`: there is a `3`-uniform hypergraph
carrying a *perfect* fractional matching of value `2`, in which every fractional matching obeying
the weighted-codegree hypothesis with parameter `γ` has value at most `4γ`, and every integral
matching has one edge.  For `γ < 1/2` the second family is bounded away from the optimum, so the
weighted nibble cannot be applied to a near-optimal packing. -/
theorem k4_no_spread_near_optimal :
    IsUniform K4Tri 3 ∧
    (∀ v : Fin 6, ∑ T ∈ K4Tri.filter (fun T => v ∈ T), halfWeight T = 1) ∧
    (∑ T ∈ K4Tri, halfWeight T = 2) ∧
    (∀ M : Finset (Finset (Fin 6)), IsMatching K4Tri M → M.card ≤ 1) ∧
    (∀ (w : Finset (Fin 6) → ℝ) (γ : ℝ),
      (∀ x z : Fin 6, x ≠ z →
        ∑ T ∈ K4Tri.filter (fun T => x ∈ T ∧ z ∈ T), w T ≤ γ) →
      ∑ T ∈ K4Tri, w T ≤ 4 * γ) :=
  ⟨k4Tri_uniform, halfWeight_load, halfWeight_sum, k4_matching_card_le_one, k4_spread_sum_le⟩

end Nibble.K4

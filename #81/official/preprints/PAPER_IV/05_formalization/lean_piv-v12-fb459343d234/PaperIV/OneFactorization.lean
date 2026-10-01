/-
Copyright (c) 2026 J. Traverso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: J. Traverso
-/
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.LinearCombination

/-!
# 1-factorization of complete graphs

A *1-factorization* of a graph `G` is a partition of its edges into perfect matchings. This file
proves the two classical "rotation" (round-robin) results:

* the complete graph on an **even** number of vertices `K_{2n}` admits a 1-factorization into
  `2n - 1` perfect matchings;
* the complete graph on an **odd** number of vertices `K_{2n+1}` admits a *near*-1-factorization
  into `2n + 1` matchings, each missing exactly one vertex.

Together these give the edge chromatic number of complete graphs.

## Main definitions

* `SimpleGraph.IsOneFactorization G M`: the family `M : ι → G.Subgraph` is a 1-factorization
  of `G` — every `M i` is a perfect matching, and every edge of `G` lies in exactly one `M i`.
* `SimpleGraph.IsNearOneFactorization G M`: every `M i` is a matching missing exactly one vertex,
  and every edge lies in exactly one `M i`.

## Main results

* `SimpleGraph.completeGraph_isOneFactorization_even`: `K_{2n}` decomposes into `2n - 1`
  perfect matchings.
* `SimpleGraph.completeGraph_isNearOneFactorization_odd`: `K_{2n+1}` decomposes into `2n + 1`
  matchings, each missing exactly one vertex.

## Implementation notes

*Even case.* The `2n` vertices are identified with `Option (ZMod (2n-1))`: `none` is a distinguished
vertex `∞`, and `some u` ranges over `ZMod (2n-1)`. Colour class `i` matches `∞` with `i` and matches
`u ≠ v` iff `u + v = 2 * i`.

*Odd case.* The `2n+1` vertices are identified with `ZMod (2n+1)` directly (no `∞`). Colour class `i`
matches `u ≠ v` iff `u + v = 2 * i`, leaving vertex `i` itself unmatched.

In both cases the modulus is odd, so `2` is a unit and the colour of a finite edge `{u, v}` is
recovered as the midpoint `(u + v) / 2`, giving the partition property.

## References

The construction is the standard round-robin / circle 1-factorization of complete graphs;
see e.g. Wikipedia, "Edge coloring".
-/

open SimpleGraph

namespace SimpleGraph

variable {V : Type*}

/-- A family `M : ι → G.Subgraph` is a **1-factorization** of `G` when every `M i` is a
perfect matching and every edge of `G` lies in exactly one `M i`. -/
def IsOneFactorization {ι : Type*} (G : SimpleGraph V)
    (M : ι → G.Subgraph) : Prop :=
  (∀ i, (M i).IsPerfectMatching) ∧
  (∀ e ∈ G.edgeSet, ∃! i, e ∈ (M i).edgeSet)

/-- `2` is a unit in `ZMod m` when `m` is odd. -/
lemma two_isUnit (m : ℕ) [NeZero m] (hm : Odd m) : IsUnit (2 : ZMod m) := by
  have : IsUnit ((2 : ℕ) : ZMod m) :=
    (ZMod.isUnit_iff_coprime 2 m).mpr (Nat.coprime_two_left.mpr hm)
  simpa using this

/-- Multiplication by `2` is injective in `ZMod m` when `m` is odd. -/
lemma two_mul_inj (m : ℕ) [NeZero m] (hm : Odd m) {x y : ZMod m}
    (h : 2 * x = 2 * y) : x = y := (two_isUnit m hm).mul_left_cancel h

/-- The colour relation of colour `i` on `Option (ZMod m)`.  `none` plays the role of the
distinguished vertex `∞`; `some u` is the vertex `u` of the `ZMod m` part.  Colour `i`
matches `∞` with `i`, and matches `u` with `v` (both `≠ ∞`) exactly when `u ≠ v` and
`u + v = 2 * i` (i.e. `{i+t, i-t}`). -/
def coleRel (m : ℕ) (i : ZMod m) : Option (ZMod m) → Option (ZMod m) → Prop
  | none, some v => v = i
  | some u, none => u = i
  | some u, some v => u ≠ v ∧ u + v = 2 * i
  | none, none => False

lemma coleRel_symm (m : ℕ) (i : ZMod m) {a b : Option (ZMod m)} :
    coleRel m i a b → coleRel m i b a := by
  cases a <;> cases b <;> simp only [coleRel]
  · exact id
  · exact id
  · exact id
  · exact fun h => ⟨h.1.symm, by rw [add_comm]; exact h.2⟩

lemma coleRel_ne (m : ℕ) (i : ZMod m) {a b : Option (ZMod m)} :
    coleRel m i a b → a ≠ b := by
  cases a <;> cases b <;> simp only [coleRel] <;> intro h <;> simp_all

/-- **Perfect-matching content.**  For every colour `i` and every vertex `a`, there is a
unique partner `b` matched to `a` in colour `i`. -/
lemma coleRel_existsUnique_partner (m : ℕ) [NeZero m] (hm : Odd m) (i : ZMod m)
    (a : Option (ZMod m)) : ∃! b, coleRel m i a b := by
  cases a with
  | none =>
    refine ⟨some i, rfl, ?_⟩
    rintro (_ | v) h
    · simp only [coleRel] at h
    · simp only [coleRel] at h; rw [h]
  | some u =>
    by_cases hui : u = i
    · subst hui
      refine ⟨none, rfl, ?_⟩
      rintro (_ | v) h
      · rfl
      · exfalso
        obtain ⟨hne, hsum⟩ := h
        apply hne
        have : v = u := by rw [two_mul] at hsum; exact add_left_cancel hsum
        exact this.symm
    · refine ⟨some (2 * i - u), ?_, ?_⟩
      · refine ⟨?_, by ring⟩
        intro h
        apply hui
        have h2 : 2 * u = 2 * i := by
          rw [eq_sub_iff_add_eq, ← two_mul] at h; exact h
        exact two_mul_inj m hm h2
      · rintro (_ | v) h
        · exact absurd h hui
        · obtain ⟨hne, hsum⟩ := h
          congr 1
          exact eq_sub_of_add_eq (by rw [add_comm]; exact hsum)

/-- **Partition content.**  Every (non-loop) edge `{a, b}` lies in a unique colour. -/
lemma coleRel_existsUnique_color (m : ℕ) [NeZero m] (hm : Odd m)
    {a b : Option (ZMod m)} (hab : a ≠ b) : ∃! i : ZMod m, coleRel m i a b := by
  cases a with
  | none =>
    cases b with
    | none => exact absurd rfl hab
    | some v => exact ⟨v, rfl, fun j h => by simp only [coleRel] at h; rw [h]⟩
  | some u =>
    cases b with
    | none => exact ⟨u, rfl, fun j h => by simp only [coleRel] at h; rw [h]⟩
    | some v =>
      have huv : u ≠ v := fun h => hab (by rw [h])
      obtain ⟨w, hw⟩ := two_isUnit m hm
      refine ⟨(u + v) * (↑w⁻¹), ⟨huv, ?_⟩, ?_⟩
      · rw [← hw, mul_comm (u + v), ← mul_assoc, Units.mul_inv, one_mul]
      · intro j h
        obtain ⟨_, hsum⟩ := h
        rw [hsum, ← hw, mul_comm (↑w) j, mul_assoc, Units.mul_inv, mul_one]

/-- The perfect matching of colour `i`, as a subgraph of `completeGraph V`, where the
vertex type `V` is identified with `Option (ZMod m)` via `φ`. -/
def colorGraph (m : ℕ) {V : Type*} (φ : V ≃ Option (ZMod m)) (i : ZMod m) :
    (completeGraph V).Subgraph where
  verts := Set.univ
  Adj x y := coleRel m i (φ x) (φ y)
  adj_sub := by
    intro x y h
    rw [completeGraph, top_adj]
    exact fun hxy => coleRel_ne m i h (by rw [hxy])
  edge_vert := by intro x y _; trivial
  symm := by intro x y h; exact coleRel_symm m i h

/-- A 1-factorization of `completeGraph V` whenever `V ≃ Option (ZMod m)` with `m` odd:
the family of colour subgraphs indexed by `ZMod m`. -/
lemma factorization_of_equiv {V : Type*} (m : ℕ) [NeZero m]
    (hm : Odd m) (φ : V ≃ Option (ZMod m)) :
    ∃ N : ZMod m → (completeGraph V).Subgraph,
      (∀ i, (N i).IsPerfectMatching) ∧
      (∀ e ∈ (completeGraph V).edgeSet, ∃! i, e ∈ (N i).edgeSet) := by
  refine ⟨fun i => colorGraph m φ i, ?_, ?_⟩
  · intro i
    rw [Subgraph.isPerfectMatching_iff]
    intro x
    show ∃! y, coleRel m i (φ x) (φ y)
    exact (Equiv.existsUnique_congr_left φ.symm).mp (coleRel_existsUnique_partner m hm i (φ x))
  · intro e he
    induction e using Sym2.ind with
    | _ x y =>
      rw [mem_edgeSet, completeGraph, top_adj] at he
      have hab : φ x ≠ φ y := fun h => he (φ.injective h)
      simp only [Subgraph.mem_edgeSet]
      show ∃! i, coleRel m i (φ x) (φ y)
      exact coleRel_existsUnique_color m hm hab

/-- **1-factorization of `K_{2n}`.** The complete graph on `2n` vertices decomposes into
`2n - 1` perfect matchings. -/
theorem completeGraph_isOneFactorization_even (n : ℕ) (hn : 1 ≤ n) :
    ∃ M : Fin (2 * n - 1) → (completeGraph (Fin (2 * n))).Subgraph,
      IsOneFactorization (completeGraph (Fin (2 * n))) M := by
  haveI : NeZero (2 * n - 1) := ⟨by omega⟩
  have hodd : Odd (2 * n - 1) := ⟨n - 1, by omega⟩
  have hcardZ : Fintype.card (ZMod (2 * n - 1)) = 2 * n - 1 := ZMod.card _
  have hcardO : Fintype.card (Option (ZMod (2 * n - 1))) = 2 * n := by
    rw [Fintype.card_option, hcardZ]; omega
  let φ : Fin (2 * n) ≃ Option (ZMod (2 * n - 1)) :=
    (Fintype.equivFinOfCardEq hcardO).symm
  let ψ : Fin (2 * n - 1) ≃ ZMod (2 * n - 1) :=
    (Fintype.equivFinOfCardEq hcardZ).symm
  obtain ⟨N, hpm, hpart⟩ := factorization_of_equiv (2 * n - 1) hodd φ
  refine ⟨fun j => N (ψ j), fun j => hpm (ψ j), ?_⟩
  intro e he
  exact (Equiv.existsUnique_congr_left ψ.symm).mp (hpart e he)

/-! ### Odd case: near-1-factorization of `K_{2n+1}` -/

/-- A **near-1-factorization** of `G`: a family `M : ι → G.Subgraph` where every `M i` is a
matching that misses exactly one vertex, and every edge of `G` lies in exactly one `M i`. -/
def IsNearOneFactorization {ι : Type*} (G : SimpleGraph V) (M : ι → G.Subgraph) : Prop :=
  (∀ i, (M i).IsMatching) ∧
  (∀ i, ∃ v, (M i).verts = {v}ᶜ) ∧
  (∀ e ∈ G.edgeSet, ∃! i, e ∈ (M i).edgeSet)

/-- The vertex identification `Fin (2n+1) ≃ ZMod (2n+1)`. -/
noncomputable def vertEquiv (n : ℕ) : Fin (2 * n + 1) ≃ ZMod (2 * n + 1) :=
  haveI : NeZero (2 * n + 1) := ⟨by omega⟩
  (Fintype.equivFinOfCardEq (ZMod.card (2 * n + 1))).symm

/-- Colour class `i` of the rotation near-1-factorization of `K_{2n+1}`: the matching pairing
`u` with `v` iff `u ≠ v` and `φ u + φ v = 2 * φ i`, missing exactly the vertex `i`. -/
noncomputable def factor (n : ℕ) (i : Fin (2 * n + 1)) :
    (completeGraph (Fin (2 * n + 1))).Subgraph where
  verts := {i}ᶜ
  Adj u v := u ≠ v ∧ vertEquiv n u + vertEquiv n v = 2 * vertEquiv n i
  adj_sub h := h.1
  edge_vert := by
    intro u v h
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    rintro rfl
    apply h.1
    have hcc : vertEquiv n u + vertEquiv n v = vertEquiv n u + vertEquiv n u := by
      rw [h.2]; ring
    exact ((vertEquiv n).injective (add_left_cancel hcc)).symm
  symm := by
    intro u v h
    exact ⟨h.1.symm, by rw [add_comm (vertEquiv n v) (vertEquiv n u)]; exact h.2⟩

/-- **Near-1-factorization of `K_{2n+1}`.** The complete graph on `2n+1` vertices decomposes into
`2n+1` matchings, each missing exactly one vertex. (Holds for all `n`, including `n = 0`.) -/
theorem completeGraph_isNearOneFactorization_odd (n : ℕ) :
    ∃ M : Fin (2 * n + 1) → (completeGraph (Fin (2 * n + 1))).Subgraph,
      IsNearOneFactorization (completeGraph (Fin (2 * n + 1))) M := by
  classical
  set S := 2 * n + 1 with hS
  haveI : NeZero S := ⟨by omega⟩
  set φ := vertEquiv n with hφ
  have hodd : Odd S := ⟨n, by omega⟩
  have h2 : IsUnit (2 : ZMod S) := by
    have := (ZMod.isUnit_iff_coprime 2 S).mpr (Nat.coprime_two_left.mpr hodd)
    simpa using this
  have hcancel : ∀ x y : ZMod S, 2 * x = 2 * y → x = y := fun _ _ h => h2.mul_right_injective h
  have hsurj : ∀ y : ZMod S, ∃ x : ZMod S, 2 * x = y := by
    obtain ⟨u, hu⟩ := h2
    intro y
    refine ⟨(↑u⁻¹ : ZMod S) * y, ?_⟩
    have hinv : (2 : ZMod S) * (↑u⁻¹ : ZMod S) = 1 := by rw [← hu]; exact u.mul_inv
    rw [← mul_assoc, hinv, one_mul]
  refine ⟨fun i => factor n i, ?_, ?_, ?_⟩
  · intro i v hv
    simp only [factor, Set.mem_compl_iff, Set.mem_singleton_iff] at hv
    obtain ⟨w0, hw0⟩ : ∃ w0 : Fin S, φ w0 = 2 * φ i - φ v := ⟨φ.symm _, φ.apply_symm_apply _⟩
    refine ⟨w0, ⟨?_, ?_⟩, ?_⟩
    · intro hvw
      apply hv
      apply φ.injective
      have hvv : φ v = 2 * φ i - φ v := by rw [← hw0, hvw]
      have : 2 * φ v = 2 * φ i := by linear_combination hvv
      exact hcancel _ _ this
    · show φ v + φ w0 = 2 * φ i
      rw [hw0]; ring
    · intro w hw
      apply φ.injective
      rw [hw0]
      have : φ v + φ w = 2 * φ i := hw.2
      linear_combination this
  · intro i
    exact ⟨i, rfl⟩
  · intro e he
    induction e using Sym2.ind with
    | _ u v =>
      rw [SimpleGraph.mem_edgeSet, SimpleGraph.completeGraph_eq_top,
        SimpleGraph.top_adj] at he
      obtain ⟨c, hc⟩ := hsurj (φ u + φ v)
      refine ⟨φ.symm c, ?_, ?_⟩
      · show s(u, v) ∈ (factor n (φ.symm c)).edgeSet
        rw [Subgraph.mem_edgeSet]
        refine ⟨he, ?_⟩
        show φ u + φ v = 2 * φ (φ.symm c)
        rw [φ.apply_symm_apply, hc]
      · intro i hi
        rw [Subgraph.mem_edgeSet] at hi
        apply φ.injective
        rw [φ.apply_symm_apply]
        have h1 : φ u + φ v = 2 * φ i := hi.2
        have : 2 * φ i = 2 * c := by rw [← h1, ← hc]
        exact (hcancel _ _ this)

end SimpleGraph




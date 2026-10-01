/-
Copyright (c) 2026 J. Traverso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: J. Traverso
-/
-- TODO(PR): replace `import Mathlib` with a minimal targeted set before submission
-- (a first attempt with SimpleGraph.{LineGraph,Coloring,Finite,DegreeSum} was incomplete:
--  the fan/Kempe argument also needs connectivity lemmas, e.g.
--  `SimpleGraph.Connected.card_vert_le_card_edgeSet_add_one`). Kept broad here to compile.
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting
import Mathlib.Combinatorics.SimpleGraph.Ends.Defs
import Mathlib.Combinatorics.SimpleGraph.LineGraph
import Mathlib.ModelTheory.Graph
import Mathlib.Order.BourbakiWitt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Vizing's theorem (edge chromatic number upper bound)

**Vizing's theorem**: every finite simple graph `G` is `(Δ(G) + 1)`-edge-colourable, where
`Δ(G)` is the maximum degree. Phrased through the line graph `L(G)` (whose vertices are the
edges of `G`, adjacent when they share an endpoint), a proper edge colouring of `G` is a proper
(vertex) colouring of `L(G)`, so the statement is `(G.lineGraph).Colorable (Δ(G) + 1)`.

As of Mathlib v4.28.0 the library has vertex `Coloring`, the line graph, `maxDegree` and
`chromaticNumber`, but **not** Vizing's bound (nor any chromatic-index API). This file provides
it. *Re-check `master` before opening a PR.*

## Main definitions

* `Vizing.PEC G C`: a *partial edge colouring* of `G` with colours in `C` — a symmetric partial
  function on adjacent pairs, proper where defined. The proof is an induction that extends a
  partial colouring one edge at a time.

## Main results

* `Vizing.lineGraph_colorable`: `(G.lineGraph).Colorable (G.maxDegree + 1)` — Vizing's theorem.
* `SimpleGraph.lineGraph_chromaticNumber_le_maxDegree_succ`:
  `(G.lineGraph).chromaticNumber ≤ (G.maxDegree : ℕ∞) + 1`.

## Implementation notes

The proof is the classical **Vizing fan** argument with **Kempe-chain** (alternating two-colour
path) recolouring, carried out over `Vizing.PEC`. An uncoloured edge at a vertex `v` is coloured
by building a maximal fan of neighbours, and, when no colour is directly free, rotating the fan
and flipping a Kempe chain to free one. The induction is on the number of uncoloured edges.

## PR checklist (pre-submission)

* [ ] rebase onto Mathlib `master`; confirm the upstream gap still exists;
* [ ] minimise imports (this file lists a targeted set; trim further if possible);
* [ ] align naming with Mathlib edge-colouring conventions if/when they land;
* [ ] resolve linter suggestions (unused section variables, redundant `simp` args).
-/

section -- Vizing.Basic
/-!
# Partial edge colourings

Basic framework for Vizing's theorem: a *partial proper edge colouring* of a simple graph `G`
is a symmetric partial function on pairs of vertices, defined only on edges, such that two
distinct edges sharing a vertex never receive the same colour.
-/

open SimpleGraph Finset

namespace Vizing

variable {V : Type*} [DecidableEq V] {C : Type*}

/-- A partial proper edge colouring of `G` with colours in `C`. -/
structure PEC (G : SimpleGraph V) (C : Type*) where
  /-- The colour of the edge `u v`, if it is coloured. -/
  col : V → V → Option C
  col_symm : ∀ u v, col u v = col v u
  col_adj : ∀ {u v γ}, col u v = some γ → G.Adj u v
  col_proper : ∀ {u v w γ}, col u v = some γ → col u w = some γ → v = w

namespace PEC

variable {G : SimpleGraph V}

/-- A colour is free at a vertex if no edge at that vertex carries it. -/
def IsFree (c : PEC G C) (v : V) (γ : C) : Prop := ∀ u, c.col v u ≠ some γ

/-- `c'` colours at least the edges that `c` colours. -/
def Extends (c c' : PEC G C) : Prop := ∀ u v, c.col u v ≠ none → c'.col u v ≠ none

omit [DecidableEq V] in
lemma Extends.rfl' (c : PEC G C) : Extends c c := fun _ _ h => h

omit [DecidableEq V] in
lemma Extends.trans {c₁ c₂ c₃ : PEC G C} (h₁ : Extends c₁ c₂) (h₂ : Extends c₂ c₃) :
    Extends c₁ c₃ := fun u v h => h₂ u v (h₁ u v h)

omit [DecidableEq V] in
lemma col_self (c : PEC G C) (u : V) : c.col u u = none := by
  cases h : c.col u u with
  | none => rfl
  | some γ => exact absurd (c.col_adj h) (G.irrefl)

omit [DecidableEq V] in
/-- At every vertex there is a free colour, provided there are more colours than the maximum
degree. -/
lemma exists_free [Fintype V] [Fintype C] [DecidableRel G.Adj] (c : PEC G C) (hcard : G.maxDegree < Fintype.card C)
    (v : V) : ∃ γ, c.IsFree v γ := by
  by_contra hcon
  push_neg at hcon
  simp only [IsFree, not_forall, not_not] at hcon
  choose g hg using hcon
  have hginj : Set.InjOn g (univ : Finset C) := by
    intro γ₁ _ γ₂ _ h
    have : (some γ₁ : Option C) = some γ₂ := by rw [← hg γ₁, ← hg γ₂, h]
    exact Option.some_injective _ this
  have hmem : ∀ γ ∈ (univ : Finset C), g γ ∈ G.neighborFinset v := by
    intro γ _
    exact (mem_neighborFinset _ _ _).2 (c.col_adj (hg γ))
  have hcards := Finset.card_le_card_of_injOn g hmem hginj
  simp only [card_univ, card_neighborFinset_eq_degree] at hcards
  exact absurd (hcards.trans (G.degree_le_maxDegree v)) (by omega)

/-! ### Updating a single edge -/

/-- Change the colour of the edge `x y` (in both directions) to `o`. -/
def updFun (f : V → V → Option C) (x y : V) (o : Option C) : V → V → Option C :=
  fun u v => if (u = x ∧ v = y) ∨ (u = y ∧ v = x) then o else f u v

lemma updFun_of_ne {f : V → V → Option C} {x y u v : V} (o : Option C)
    (h : ¬((u = x ∧ v = y) ∨ (u = y ∧ v = x))) : updFun f x y o u v = f u v := if_neg h

@[simp] lemma updFun_left {f : V → V → Option C} {x y : V} (o : Option C) :
    updFun f x y o x y = o := if_pos (Or.inl ⟨rfl, rfl⟩)

@[simp] lemma updFun_right {f : V → V → Option C} {x y : V} (o : Option C) :
    updFun f x y o y x = o := if_pos (Or.inr ⟨rfl, rfl⟩)

/-- Colour the (possibly already coloured) edge `x y` with a colour free at both endpoints. -/
def setEdge (c : PEC G C) {x y : V} (γ : C) (hadj : G.Adj x y)
    (hx : c.IsFree x γ) (hy : c.IsFree y γ) : PEC G C where
  col := updFun c.col x y (some γ)
  col_symm := by
    intro u v
    unfold updFun
    by_cases h : (u = x ∧ v = y) ∨ (u = y ∧ v = x)
    · rw [if_pos h, if_pos (by tauto)]
    · rw [if_neg h, if_neg (by tauto)]
      exact c.col_symm u v
  col_adj := by
    intro u v δ h
    unfold updFun at h
    by_cases hc : (u = x ∧ v = y) ∨ (u = y ∧ v = x)
    · rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hadj
      · exact hadj.symm
    · rw [if_neg hc] at h
      exact c.col_adj h
  col_proper := by
    have key : ∀ u v δ, updFun c.col x y (some γ) u v = some δ →
        ((u = x ∧ v = y) ∨ (u = y ∧ v = x)) ∨ c.col u v = some δ := by
      intro u v δ h
      unfold updFun at h
      by_cases hc : (u = x ∧ v = y) ∨ (u = y ∧ v = x)
      · exact Or.inl hc
      · rw [if_neg hc] at h
        exact Or.inr h
    have hcol : ∀ u v δ, updFun c.col x y (some γ) u v = some δ →
        (((u = x ∧ v = y) ∨ (u = y ∧ v = x)) → δ = γ) := by
      intro u v δ h hc
      unfold updFun at h
      rw [if_pos hc] at h
      exact (Option.some_injective _ h).symm
    intro u v w δ h1 h2
    rcases key u v δ h1 with hc1 | hc1 <;> rcases key u w δ h2 with hc2 | hc2
    · rcases hc1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hc2 with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
        subst_vars <;> rfl
    · have hd1 := hcol u v δ h1 hc1
      subst hd1
      rcases hc1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact absurd hc2 (hx w)
      · exact absurd hc2 (hy w)
    · have hd2 := hcol u w δ h2 hc2
      subst hd2
      rcases hc2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact absurd hc1 (hx v)
      · exact absurd hc1 (hy v)
    · exact c.col_proper hc1 hc2

@[simp] lemma setEdge_col (c : PEC G C) {x y : V} (γ : C) (hadj : G.Adj x y)
    (hx : c.IsFree x γ) (hy : c.IsFree y γ) :
    (c.setEdge γ hadj hx hy).col = updFun c.col x y (some γ) := rfl

lemma setEdge_col_of_ne_left (c : PEC G C) {x y : V} (γ : C) (hadj : G.Adj x y)
    (hx : c.IsFree x γ) (hy : c.IsFree y γ) {w : V} (hwx : w ≠ x) (hwy : w ≠ y) (u : V) :
    (c.setEdge γ hadj hx hy).col w u = c.col w u :=
  updFun_of_ne _ (by tauto)

lemma isFree_setEdge_of_ne (c : PEC G C) {x y : V} (γ : C) (hadj : G.Adj x y)
    (hx : c.IsFree x γ) (hy : c.IsFree y γ) {w : V} (hwx : w ≠ x) (hwy : w ≠ y) (δ : C) :
    (c.setEdge γ hadj hx hy).IsFree w δ ↔ c.IsFree w δ := by
  constructor <;> intro h u hu
  · exact h u (by rw [c.setEdge_col_of_ne_left γ hadj hx hy hwx hwy u]; exact hu)
  · rw [c.setEdge_col_of_ne_left γ hadj hx hy hwx hwy u] at hu
    exact h u hu

lemma extends_setEdge (c : PEC G C) {x y : V} (γ : C) (hadj : G.Adj x y)
    (hx : c.IsFree x γ) (hy : c.IsFree y γ) : Extends c (c.setEdge γ hadj hx hy) := by
  intro u v h
  simp only [setEdge_col, updFun]
  split
  · exact Option.some_ne_none _
  · exact h

end PEC

end Vizing
end

section -- Vizing.Endpoints
/-!
# Components of graphs of maximum degree two

A connected component of a graph with maximum degree at most `2` (a path or a cycle) contains
at most two vertices of degree at most `1`.  This is the combinatorial input to the Kempe chain
step of Vizing's theorem.
-/

open SimpleGraph Finset

namespace Vizing

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- Degrees can only drop when passing to the induced graph on a connected component. -/
lemma degree_toSimpleGraph_le {H : SimpleGraph V} [DecidableRel H.Adj]
    (Cp : H.ConnectedComponent) [DecidableRel Cp.toSimpleGraph.Adj]
    [∀ z : ↥Cp, Fintype (Cp.toSimpleGraph.neighborSet z)] (z : ↥Cp) :
    Cp.toSimpleGraph.degree z ≤ H.degree z.1 := by
  classical
  rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
  refine Finset.card_le_card_of_injOn (fun t => t.1) ?_ ?_
  · intro t ht
    simp only [Finset.mem_coe, mem_neighborFinset] at ht ⊢
    exact ht
  · intro t _ s _ h
    exact Subtype.ext h

/-- In a graph of maximum degree at most `2`, no connected component contains three distinct
vertices of degree at most `1`. -/
theorem no_three_endpoints {H : SimpleGraph V} [DecidableRel H.Adj]
    (hdeg : ∀ z, H.degree z ≤ 2) {u v w : V} (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (hu : H.degree u ≤ 1) (hv : H.degree v ≤ 1) (hw : H.degree w ≤ 1)
    (h1 : H.Reachable u v) (h2 : H.Reachable u w) : False := by
  classical
  set Cp := H.connectedComponentMk u with hCp
  have humem : u ∈ Cp := rfl
  have hvmem : v ∈ Cp := (ConnectedComponent.sound h1.symm : _)
  have hwmem : w ∈ Cp := (ConnectedComponent.sound h2.symm : _)
  set K := Cp.toSimpleGraph with hK
  have hKconn : K.Connected := Cp.connected_toSimpleGraph
  set u' : ↥Cp := ⟨u, humem⟩ with hu'
  set v' : ↥Cp := ⟨v, hvmem⟩ with hv'
  set w' : ↥Cp := ⟨w, hwmem⟩ with hw'
  have hdegK : ∀ z : ↥Cp, K.degree z ≤ H.degree z.1 := fun z => degree_toSimpleGraph_le Cp z
  set N := Fintype.card ↥Cp with hN
  set T : Finset ↥Cp := {u', v', w'} with hT
  have hTcard : T.card = 3 := by
    rw [hT, Finset.card_insert_of_notMem (by simp [hu', hv', hw', Subtype.ext_iff, huv, huw]),
      Finset.card_insert_of_notMem (by simp [hv', hw', Subtype.ext_iff, hvw]),
      Finset.card_singleton]
  have hN3 : 3 ≤ N := by
    rw [hN, ← Finset.card_univ, ← hTcard]
    exact Finset.card_le_card (Finset.subset_univ T)
  have hsum : ∑ z : ↥Cp, K.degree z ≤ 2 * N - 3 := by
    have hsplit : ∑ z ∈ T, K.degree z + ∑ z ∈ (Finset.univ \ T), K.degree z
        = ∑ z : ↥Cp, K.degree z := by
      rw [add_comm]
      exact Finset.sum_sdiff (Finset.subset_univ T)
    have hT' : ∑ z ∈ T, K.degree z ≤ 3 := by
      calc ∑ z ∈ T, K.degree z ≤ ∑ _z ∈ T, 1 := by
            refine Finset.sum_le_sum ?_
            intro z hz
            rw [hT] at hz
            simp only [Finset.mem_insert, Finset.mem_singleton] at hz
            rcases hz with rfl | rfl | rfl
            · exact le_trans (hdegK _) hu
            · exact le_trans (hdegK _) hv
            · exact le_trans (hdegK _) hw
        _ = 3 := by simp [hTcard]
    have hR : ∑ z ∈ (Finset.univ \ T), K.degree z ≤ 2 * (N - 3) := by
      calc ∑ z ∈ (Finset.univ \ T), K.degree z ≤ ∑ _z ∈ (Finset.univ \ T), 2 :=
            Finset.sum_le_sum fun z _ => le_trans (hdegK z) (hdeg z.1)
        _ = 2 * (N - 3) := by
            rw [Finset.sum_const, Finset.card_univ_diff, smul_eq_mul, hTcard, mul_comm, ← hN]
    omega
  have hhand : ∑ z : ↥Cp, K.degree z = 2 * #K.edgeFinset :=
    K.sum_degrees_eq_twice_card_edges
  have hedges : N ≤ #K.edgeFinset + 1 := by
    have hc := hKconn.card_vert_le_card_edgeSet_add_one
    rwa [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← hN,
      ← Set.toFinset_card, ← edgeFinset] at hc
  omega

end Vizing
end

section -- Vizing.Kempe
/-!
# Kempe chains for partial edge colourings

Given a partial proper edge colouring `c` and two colours `a b`, the *Kempe graph* consists of
the edges coloured `a` or `b`.  Swapping the two colours on the connected component of a vertex
`x` produces another partial proper edge colouring, colouring exactly the same edges.
-/

open SimpleGraph Finset

namespace Vizing

namespace PEC

variable {V : Type*} [Fintype V] [DecidableEq V] {C : Type*} [DecidableEq C]
  {G : SimpleGraph V}

/-- The subgraph consisting of the edges coloured `a` or `b`. -/
def kempeGraph (c : PEC G C) (a b : C) : SimpleGraph V where
  Adj u v := u ≠ v ∧ (c.col u v = some a ∨ c.col u v = some b)
  symm := by
    rintro u v ⟨h1, h2⟩
    refine ⟨h1.symm, ?_⟩
    rwa [c.col_symm v u]
  loopless := ⟨fun v h => h.1 rfl⟩

omit [Fintype V] [DecidableEq V] [DecidableEq C] in
lemma kempeGraph_adj {c : PEC G C} {a b : C} {u v : V} :
    (c.kempeGraph a b).Adj u v ↔ u ≠ v ∧ (c.col u v = some a ∨ c.col u v = some b) := Iff.rfl

omit [Fintype V] [DecidableEq V] [DecidableEq C] in
lemma kempeGraph_adj_of_col {c : PEC G C} {a b : C} {u v : V}
    (h : c.col u v = some a ∨ c.col u v = some b) : (c.kempeGraph a b).Adj u v := by
  refine ⟨?_, h⟩
  rcases h with h | h <;> exact (c.col_adj h).ne

omit [Fintype V] [DecidableEq V] [DecidableEq C] in
/-- Reachability in the Kempe graph propagates along edges coloured `a` or `b`. -/
lemma reachable_of_col {c : PEC G C} {a b : C} {x u v : V}
    (hu : (c.kempeGraph a b).Reachable x u)
    (h : c.col u v = some a ∨ c.col u v = some b) : (c.kempeGraph a b).Reachable x v :=
  hu.trans (kempeGraph_adj_of_col h).reachable

open Classical in
/-- The colour function after swapping `a` and `b` on the Kempe component of `x`. -/
noncomputable def kempeSwapFun (c : PEC G C) (a b : C) (x : V) : V → V → Option C :=
  fun u v => if (c.kempeGraph a b).Reachable x u ∧ (c.kempeGraph a b).Reachable x v
    then (c.col u v).map (Equiv.swap a b) else c.col u v

lemma kempeSwapFun_of_reachable (c : PEC G C) (a b : C) {x u : V}
    (hu : (c.kempeGraph a b).Reachable x u) (v : V) :
    c.kempeSwapFun a b x u v = (c.col u v).map (Equiv.swap a b) := by
  classical
  unfold kempeSwapFun
  by_cases hv : (c.kempeGraph a b).Reachable x v
  · rw [if_pos ⟨hu, hv⟩]
  · rw [if_neg (by tauto)]
    cases h : c.col u v with
    | none => simp
    | some γ =>
      have hγa : γ ≠ a := by
        rintro rfl
        exact hv (reachable_of_col hu (Or.inl h))
      have hγb : γ ≠ b := by
        rintro rfl
        exact hv (reachable_of_col hu (Or.inr h))
      simp [Equiv.swap_apply_of_ne_of_ne hγa hγb]

lemma kempeSwapFun_of_not_reachable (c : PEC G C) (a b : C) {x u : V}
    (hu : ¬ (c.kempeGraph a b).Reachable x u) (v : V) :
    c.kempeSwapFun a b x u v = c.col u v := by
  classical
  unfold kempeSwapFun
  rw [if_neg (by tauto)]

lemma kempeSwapFun_isSome (c : PEC G C) (a b : C) (x u v : V) :
    (c.kempeSwapFun a b x u v = none) ↔ (c.col u v = none) := by
  classical
  by_cases hu : (c.kempeGraph a b).Reachable x u
  · rw [kempeSwapFun_of_reachable c a b hu v]
    cases c.col u v <;> simp
  · rw [kempeSwapFun_of_not_reachable c a b hu v]

/-- Swapping the colours `a` and `b` on the Kempe component of `x`. -/
noncomputable def kempeSwap (c : PEC G C) (a b : C) (x : V) : PEC G C where
  col := c.kempeSwapFun a b x
  col_symm := by
    classical
    intro u v
    unfold kempeSwapFun
    by_cases h : (c.kempeGraph a b).Reachable x u ∧ (c.kempeGraph a b).Reachable x v
    · rw [if_pos h, if_pos ⟨h.2, h.1⟩, c.col_symm u v]
    · rw [if_neg h, if_neg (fun hh => h ⟨hh.2, hh.1⟩), c.col_symm u v]
  col_adj := by
    intro u v γ h
    by_cases hu : (c.kempeGraph a b).Reachable x u
    · rw [kempeSwapFun_of_reachable c a b hu v] at h
      cases hc : c.col u v with
      | none => rw [hc] at h; simp at h
      | some δ => exact c.col_adj hc
    · rw [kempeSwapFun_of_not_reachable c a b hu v] at h
      exact c.col_adj h
  col_proper := by
    intro u v w γ h1 h2
    by_cases hu : (c.kempeGraph a b).Reachable x u
    · rw [kempeSwapFun_of_reachable c a b hu v] at h1
      rw [kempeSwapFun_of_reachable c a b hu w] at h2
      cases hcv : c.col u v with
      | none => rw [hcv] at h1; simp at h1
      | some δ =>
        cases hcw : c.col u w with
        | none => rw [hcw] at h2; simp at h2
        | some ε =>
          rw [hcv] at h1
          rw [hcw] at h2
          simp only [Option.map_some] at h1 h2
          have : δ = ε := (Equiv.swap a b).injective (by
            rw [Option.some_injective _ h1, Option.some_injective _ h2])
          exact c.col_proper hcv (this ▸ hcw)
    · rw [kempeSwapFun_of_not_reachable c a b hu v] at h1
      rw [kempeSwapFun_of_not_reachable c a b hu w] at h2
      exact c.col_proper h1 h2

@[simp] lemma kempeSwap_col (c : PEC G C) (a b : C) (x : V) :
    (c.kempeSwap a b x).col = c.kempeSwapFun a b x := rfl

lemma extends_kempeSwap (c : PEC G C) (a b : C) (x : V) : Extends c (c.kempeSwap a b x) := by
  intro u v h
  rw [kempeSwap_col, ne_eq, kempeSwapFun_isSome]
  exact h

/-- On the Kempe component the free colours get swapped. -/
lemma isFree_kempeSwap_of_reachable (c : PEC G C) (a b : C) {x v : V}
    (hv : (c.kempeGraph a b).Reachable x v) (γ : C) :
    (c.kempeSwap a b x).IsFree v γ ↔ c.IsFree v (Equiv.swap a b γ) := by
  constructor
  · intro h u hu
    refine h u ?_
    rw [kempeSwap_col, kempeSwapFun_of_reachable c a b hv u, hu]
    simp
  · intro h u hu
    rw [kempeSwap_col, kempeSwapFun_of_reachable c a b hv u] at hu
    cases hc : c.col v u with
    | none => rw [hc] at hu; simp at hu
    | some δ =>
      rw [hc] at hu
      simp only [Option.map_some, Option.some.injEq] at hu
      refine h u ?_
      rw [hc, ← hu]
      simp

/-- Off the Kempe component the free colours are unchanged. -/
lemma isFree_kempeSwap_of_not_reachable (c : PEC G C) (a b : C) {x v : V}
    (hv : ¬ (c.kempeGraph a b).Reachable x v) (γ : C) :
    (c.kempeSwap a b x).IsFree v γ ↔ c.IsFree v γ := by
  constructor
  · intro h u hu
    exact h u (by rw [kempeSwap_col, kempeSwapFun_of_not_reachable c a b hv u]; exact hu)
  · intro h u hu
    rw [kempeSwap_col, kempeSwapFun_of_not_reachable c a b hv u] at hu
    exact h u hu

/-! ### Degrees in the Kempe graph -/

lemma kempe_degree_le_two (c : PEC G C) (a b : C) [DecidableRel (c.kempeGraph a b).Adj] (v : V) :
    (c.kempeGraph a b).degree v ≤ 2 := by
  classical
  rw [← card_neighborFinset_eq_degree]
  have hsub : (c.kempeGraph a b).neighborFinset v ⊆
      ((c.kempeGraph a b).neighborFinset v).filter (fun u => c.col v u = some a) ∪
      ((c.kempeGraph a b).neighborFinset v).filter (fun u => c.col v u = some b) := by
    intro u hu
    have hu' := hu
    rw [mem_neighborFinset, kempeGraph_adj] at hu'
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    rcases hu'.2 with h | h
    · exact Or.inl ⟨hu, h⟩
    · exact Or.inr ⟨hu, h⟩
  have hcarda : (((c.kempeGraph a b).neighborFinset v).filter
      (fun u => c.col v u = some a)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro p hp q hq
    rw [Finset.mem_filter] at hp hq
    exact c.col_proper hp.2 hq.2
  have hcardb : (((c.kempeGraph a b).neighborFinset v).filter
      (fun u => c.col v u = some b)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro p hp q hq
    rw [Finset.mem_filter] at hp hq
    exact c.col_proper hp.2 hq.2
  calc ((c.kempeGraph a b).neighborFinset v).card
      ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := Finset.card_union_le _ _
    _ ≤ 2 := by omega

omit [DecidableEq V] [DecidableEq C] in
lemma kempe_degree_le_one_of_isFree (c : PEC G C) {a b : C} [DecidableRel (c.kempeGraph a b).Adj]
    {v : V} {γ : C} (hγ : γ = a ∨ γ = b) (hfree : c.IsFree v γ) :
    (c.kempeGraph a b).degree v ≤ 1 := by
  classical
  rw [← card_neighborFinset_eq_degree, Finset.card_le_one]
  intro p hp q hq
  rw [mem_neighborFinset, kempeGraph_adj] at hp hq
  rcases hγ with rfl | rfl
  · rcases hp.2 with h | h
    · exact absurd h (hfree p)
    · rcases hq.2 with h' | h'
      · exact absurd h' (hfree q)
      · exact c.col_proper h h'
  · rcases hp.2 with h | h
    · rcases hq.2 with h' | h'
      · exact c.col_proper h h'
      · exact absurd h' (hfree q)
    · exact absurd h (hfree p)

end PEC

end Vizing
end

section -- Vizing.Fan
/-!
# Vizing fans

A *fan* at a vertex `x` starting at an uncoloured edge `x y` is a sequence of distinct
neighbours `f 0 = y, f 1, …, f n` of `x` such that the colour of `x (f (i+1))` is free at
`f i`.  Rotating a fan whose last vertex misses a colour that is also missing at `x` colours
the edge `x y`.
-/

open SimpleGraph Finset

namespace Vizing

namespace PEC

variable {V : Type*} [Fintype V] [DecidableEq V] {C : Type*} [DecidableEq C]
  {G : SimpleGraph V}

/-- `f 0, …, f n` is a fan at `x` for the uncoloured edge `x y`. -/
structure IsFan (c : PEC G C) (x y : V) (n : ℕ) (f : ℕ → V) : Prop where
  start : f 0 = y
  uncoloured : c.col x y = none
  adj : ∀ i ≤ n, G.Adj x (f i)
  inj : ∀ i ≤ n, ∀ j ≤ n, f i = f j → i = j
  step : ∀ i < n, ∃ γ, c.col x (f (i + 1)) = some γ ∧ c.IsFree (f i) γ

omit [DecidableEq V] [DecidableEq C] in
/-- A fan has at most `Fintype.card V` vertices. -/
lemma IsFan.length_le {c : PEC G C} {x y : V} {n : ℕ} {f : ℕ → V} (h : c.IsFan x y n f) :
    n ≤ Fintype.card V := by
  classical
  have hcard : (Finset.range (n + 1)).card ≤ (Finset.univ : Finset V).card := by
    refine Finset.card_le_card_of_injOn f (fun i _ => Finset.mem_univ _) ?_
    intro i hi j hj hij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    exact h.inj i (by omega) j (by omega) hij
  simp only [Finset.card_range, Finset.card_univ] at hcard
  omega

omit [Fintype V] [DecidableEq C] in
/-- Rotating a fan: if some colour `b` is free both at `x` and at the last vertex of the fan,
then the uncoloured edge `x y` can be coloured (after recolouring the fan edges). -/
lemma fan_rotate (x y : V) (f : ℕ → V) : ∀ (n : ℕ) (c : PEC G C) (b : C), c.IsFan x y n f →
    c.IsFree x b → c.IsFree (f n) b → ∃ c' : PEC G C, Extends c c' ∧ c'.col x y ≠ none := by
  intro n
  induction n with
  | zero =>
    intro c b hf hbx hbn
    have hy : y = f 0 := hf.start.symm
    subst hy
    refine ⟨c.setEdge b (hf.adj 0 le_rfl) hbx hbn, c.extends_setEdge b (hf.adj 0 le_rfl) hbx hbn,
      ?_⟩
    rw [setEdge_col, updFun_left]
    exact Option.some_ne_none _
  | succ n ih =>
    intro c b hf hbx hbn
    obtain ⟨γ, hγ, hγfree⟩ := hf.step n (Nat.lt_succ_self n)
    have hadj : G.Adj x (f (n + 1)) := hf.adj (n + 1) le_rfl
    have hnex : ∀ i, i ≤ n + 1 → f i ≠ x := fun i hi => (hf.adj i hi).ne'
    have hnelast : ∀ i, i ≤ n → f i ≠ f (n + 1) := by
      intro i hi hcon
      have := hf.inj i (by omega) (n + 1) le_rfl hcon
      omega
    set c1 := c.setEdge b hadj hbx hbn with hc1
    have hcolne : ∀ w u, w ≠ x → w ≠ f (n + 1) → c1.col w u = c.col w u := fun w u hw hw' =>
      c.setEdge_col_of_ne_left b hadj hbx hbn hw hw' u
    have hcolx : ∀ u, u ≠ f (n + 1) → c1.col x u = c.col x u := by
      intro u hu
      rw [hc1, setEdge_col]
      exact updFun_of_ne _ (by
        rintro (⟨-, h⟩ | ⟨h, -⟩)
        · exact hu h
        · exact hadj.ne h)
    have hbγ : b ≠ γ := by
      rintro rfl
      exact hbx _ hγ
    -- the fan of length `n` survives the recolouring of the last fan edge
    have hfan1 : c1.IsFan x y n f := by
      refine ⟨hf.start, ?_, fun i hi => hf.adj i (by omega),
        fun i hi j hj hij => hf.inj i (by omega) j (by omega) hij, ?_⟩
      · rw [← hf.start, hcolx (f 0) (hnelast 0 (by omega))]
        rw [hf.start]
        exact hf.uncoloured
      · intro i hi
        obtain ⟨δ, hδ, hδfree⟩ := hf.step i (by omega)
        refine ⟨δ, ?_, ?_⟩
        · rw [hcolx (f (i + 1)) (hnelast (i + 1) (by omega))]
          exact hδ
        · rw [hc1, c.isFree_setEdge_of_ne b hadj hbx hbn (hnex i (by omega))
            (hnelast i (by omega)) δ]
          exact hδfree
    have hγx : c1.IsFree x γ := by
      intro u hu
      by_cases hcase : u = f (n + 1)
      · subst hcase
        rw [hc1, setEdge_col, updFun_left] at hu
        exact hbγ (Option.some_injective _ hu)
      · rw [hcolx u hcase] at hu
        exact hcase (c.col_proper hu hγ)
    have hγn : c1.IsFree (f n) γ := by
      rw [hc1, c.isFree_setEdge_of_ne b hadj hbx hbn (hnex n (by omega))
        (hnelast n le_rfl) γ]
      exact hγfree
    obtain ⟨c', hext, hcol'⟩ := ih c1 γ hfan1 hγx hγn
    exact ⟨c', (c.extends_setEdge b hadj hbx hbn).trans hext, hcol'⟩

omit [DecidableEq V] [DecidableEq C] in
/-- Existence of a maximal fan. -/
lemma exists_maximal_fan (c : PEC G C) {x y : V} (hadj : G.Adj x y) (hnone : c.col x y = none) :
    ∃ (n : ℕ) (f : ℕ → V), c.IsFan x y n f ∧
      ∀ (m : ℕ) (g : ℕ → V), c.IsFan x y m g → m ≤ n := by
  classical
  set P : ℕ → Prop := fun n => ∃ g : ℕ → V, c.IsFan x y n g with hP
  have hP0 : P 0 := by
    refine ⟨fun _ => y, rfl, hnone, fun i _ => hadj, ?_, ?_⟩
    · intro i hi j hj _
      omega
    · intro i hi
      omega
  set N := Fintype.card V with hN
  have hspec : P (Nat.findGreatest P N) := Nat.findGreatest_spec (Nat.zero_le _) hP0
  refine ⟨Nat.findGreatest P N, hspec.choose, hspec.choose_spec, ?_⟩
  intro m g hg
  by_contra hcon
  push_neg at hcon
  exact Nat.findGreatest_is_greatest hcon hg.length_le ⟨g, hg⟩

end PEC

end Vizing
end

section -- Vizing.Step
/-!
# The Vizing extension step

Given a partial proper edge colouring with `Δ + 1` colours and an uncoloured edge `x y`, one can
recolour so that `x y` becomes coloured and no edge loses its colour.  This is the heart of
Vizing's theorem: a maximal fan at `x` is rotated, after a Kempe chain interchange if needed.
-/

open SimpleGraph Finset

namespace Vizing

namespace PEC

variable {V : Type*} [Fintype V] [DecidableEq V] {C : Type*} [Fintype C] [DecidableEq C]
  {G : SimpleGraph V}

omit [Fintype C] in
/-- A fan survives a Kempe interchange of `a` and `b` (where `a` is free at `x`) up to the first
index at which the fan edge is coloured `b` and the interchange separates `f i` from `x`. -/
lemma isFan_kempeSwap (c : PEC G C) {x y : V} {n : ℕ} {f : ℕ → V} (hfan : c.IsFan x y n f)
    {a b : C} (ha : c.IsFree x a) (w : V) {m : ℕ} (hm : m ≤ n)
    (hbreak : ∀ i < m, c.col x (f (i + 1)) = some b →
      ((c.kempeGraph a b).Reachable w (f i) ↔ (c.kempeGraph a b).Reachable w x)) :
    (c.kempeSwap a b w).IsFan x y m f := by
  classical
  refine ⟨hfan.start, ?_, fun i hi => hfan.adj i (hi.trans hm),
    fun i hi j hj hij => hfan.inj i (hi.trans hm) j (hj.trans hm) hij, ?_⟩
  · by_cases hxw : (c.kempeGraph a b).Reachable w x
    · rw [kempeSwap_col, kempeSwapFun_of_reachable c a b hxw y, hfan.uncoloured]
      rfl
    · rw [kempeSwap_col, kempeSwapFun_of_not_reachable c a b hxw y]
      exact hfan.uncoloured
  · intro i hi
    obtain ⟨γ, hγ, hγfree⟩ := hfan.step i (hi.trans_le hm)
    have hγa : γ ≠ a := by
      rintro rfl
      exact ha _ hγ
    by_cases hxw : (c.kempeGraph a b).Reachable w x
    · refine ⟨Equiv.swap a b γ, ?_, ?_⟩
      · rw [kempeSwap_col, kempeSwapFun_of_reachable c a b hxw (f (i + 1)), hγ]
        rfl
      · by_cases hiw : (c.kempeGraph a b).Reachable w (f i)
        · rw [isFree_kempeSwap_of_reachable c a b hiw]
          simpa using hγfree
        · have hγb : γ ≠ b := by
            rintro rfl
            exact hiw ((hbreak i hi hγ).2 hxw)
          rw [isFree_kempeSwap_of_not_reachable c a b hiw,
            Equiv.swap_apply_of_ne_of_ne hγa hγb]
          exact hγfree
    · refine ⟨γ, ?_, ?_⟩
      · rw [kempeSwap_col, kempeSwapFun_of_not_reachable c a b hxw (f (i + 1))]
        exact hγ
      · by_cases hiw : (c.kempeGraph a b).Reachable w (f i)
        · have hγb : γ ≠ b := by
            rintro rfl
            exact hxw ((hbreak i hi hγ).1 hiw)
          rw [isFree_kempeSwap_of_reachable c a b hiw,
            Equiv.swap_apply_of_ne_of_ne hγa hγb]
          exact hγfree
        · rw [isFree_kempeSwap_of_not_reachable c a b hiw]
          exact hγfree

/-- **Vizing's extension step.** -/
theorem vizing_step [DecidableRel G.Adj] (c : PEC G C) (hcard : G.maxDegree < Fintype.card C)
    {x y : V} (hadj : G.Adj x y) (hnone : c.col x y = none) :
    ∃ c' : PEC G C, Extends c c' ∧ c'.col x y ≠ none := by
  classical
  obtain ⟨n, f, hfan, hmax⟩ := c.exists_maximal_fan hadj hnone
  obtain ⟨a, ha⟩ := c.exists_free hcard x
  obtain ⟨b, hb⟩ := c.exists_free hcard (f n)
  by_cases han : c.IsFree (f n) a
  · exact fan_rotate x y f n c a hfan ha han
  by_cases hbx : c.IsFree x b
  · exact fan_rotate x y f n c b hfan hbx hb
  -- `b` is used at `x`, on an edge of the fan
  obtain ⟨z, hz⟩ : ∃ z, c.col x z = some b := by
    by_contra hcon
    push_neg at hcon
    exact hbx hcon
  have hzadj : G.Adj x z := c.col_adj hz
  have hzfan : ∃ i ≤ n, f i = z := by
    by_contra hcon
    push_neg at hcon
    set g : ℕ → V := fun i => if i = n + 1 then z else f i with hg
    have hgi : ∀ i, i ≤ n → g i = f i := fun i hi => if_neg (by omega)
    have hgn1 : g (n + 1) = z := if_pos rfl
    have hgfan : c.IsFan x y (n + 1) g := by
      refine ⟨by rw [hgi 0 (by omega)]; exact hfan.start, hfan.uncoloured, ?_, ?_, ?_⟩
      · intro i hi
        rcases Nat.lt_or_ge i (n + 1) with h | h
        · rw [hgi i (by omega)]
          exact hfan.adj i (by omega)
        · have hin : i = n + 1 := by omega
          subst hin
          rw [hgn1]
          exact hzadj
      · intro i hi j hj hij
        rcases Nat.lt_or_ge i (n + 1) with h | h <;> rcases Nat.lt_or_ge j (n + 1) with h' | h'
        · rw [hgi i (by omega), hgi j (by omega)] at hij
          exact hfan.inj i (by omega) j (by omega) hij
        · exfalso
          have hjn : j = n + 1 := by omega
          subst hjn
          rw [hgi i (by omega), hgn1] at hij
          exact hcon i (by omega) hij
        · exfalso
          have hin : i = n + 1 := by omega
          subst hin
          rw [hgi j (by omega), hgn1] at hij
          exact hcon j (by omega) hij.symm
        · omega
      · intro i hi
        rcases Nat.lt_or_ge i n with h | h
        · obtain ⟨γ, hγ, hγfree⟩ := hfan.step i h
          exact ⟨γ, by rw [hgi (i + 1) (by omega)]; exact hγ,
            by rw [hgi i (by omega)]; exact hγfree⟩
        · have hin : i = n := by omega
          subst hin
          exact ⟨b, by rw [hgn1]; exact hz, by rw [hgi _ le_rfl]; exact hb⟩
    have := hmax (n + 1) g hgfan
    omega
  obtain ⟨i, hin, hiz⟩ := hzfan
  have hi0 : i ≠ 0 := by
    rintro rfl
    rw [hfan.start] at hiz
    rw [hiz] at hnone
    rw [hnone] at hz
    simp at hz
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  have hbxcol : c.col x (f (j + 1)) = some b := by rw [hiz]; exact hz
  have hbj : c.IsFree (f j) b := by
    obtain ⟨γ, hγ, hγfree⟩ := hfan.step j (by omega)
    have hγb : γ = b := Option.some_injective _ (by rw [← hγ, hbxcol])
    rw [← hγb]
    exact hγfree
  have hxfn : x ≠ f n := (hfan.adj n le_rfl).ne
  have hxfj : x ≠ f j := (hfan.adj j (by omega)).ne
  have hfnfj : f n ≠ f j := by
    intro h
    have := hfan.inj n le_rfl j (by omega) h
    omega
  have hdeg2 : ∀ v, (c.kempeGraph a b).degree v ≤ 2 := c.kempe_degree_le_two a b
  have hdegx : (c.kempeGraph a b).degree x ≤ 1 :=
    c.kempe_degree_le_one_of_isFree (Or.inl rfl) ha
  have hdegn : (c.kempeGraph a b).degree (f n) ≤ 1 :=
    c.kempe_degree_le_one_of_isFree (Or.inr rfl) hb
  have hdegj : (c.kempeGraph a b).degree (f j) ≤ 1 :=
    c.kempe_degree_le_one_of_isFree (Or.inr rfl) hbj
  by_cases hRn : (c.kempeGraph a b).Reachable x (f n)
  · -- the Kempe chain from `x` ends at `f n`; interchange on the component of `f j` instead
    have hRj : ¬ (c.kempeGraph a b).Reachable x (f j) := fun hRj =>
      no_three_endpoints hdeg2 hxfn hxfj hfnfj hdegx hdegn hdegj hRn hRj
    have hxnotR : ¬ (c.kempeGraph a b).Reachable (f j) x := fun h => hRj h.symm
    have hfan2 : (c.kempeSwap a b (f j)).IsFan x y j f := by
      refine c.isFan_kempeSwap hfan ha (f j) (by omega) ?_
      intro i' hi' hcol
      exfalso
      have h1 : f (i' + 1) = f (j + 1) := c.col_proper hcol hbxcol
      have h2 := hfan.inj (i' + 1) (by omega) (j + 1) (by omega) h1
      omega
    have hax : (c.kempeSwap a b (f j)).IsFree x a :=
      (isFree_kempeSwap_of_not_reachable c a b hxnotR a).2 ha
    have hajfree : (c.kempeSwap a b (f j)).IsFree (f j) a :=
      (isFree_kempeSwap_of_reachable c a b (Reachable.refl _) a).2 (by simpa using hbj)
    obtain ⟨c', hext, hcol'⟩ := fan_rotate x y f j _ a hfan2 hax hajfree
    exact ⟨c', (c.extends_kempeSwap a b (f j)).trans hext, hcol'⟩
  · -- interchange on the component of `x`
    have hxR : (c.kempeGraph a b).Reachable x x := Reachable.refl x
    have hbx1 : (c.kempeSwap a b x).IsFree x b :=
      (isFree_kempeSwap_of_reachable c a b hxR b).2 (by simpa using ha)
    by_cases hRj : (c.kempeGraph a b).Reachable x (f j)
    · have hfan2 : (c.kempeSwap a b x).IsFan x y n f := by
        refine c.isFan_kempeSwap hfan ha x le_rfl ?_
        intro i' hi' hcol
        have h1 : f (i' + 1) = f (j + 1) := c.col_proper hcol hbxcol
        have h2 := hfan.inj (i' + 1) (by omega) (j + 1) (by omega) h1
        have h3 : i' = j := by omega
        subst h3
        exact ⟨fun _ => hxR, fun _ => hRj⟩
      have hbn1 : (c.kempeSwap a b x).IsFree (f n) b :=
        (isFree_kempeSwap_of_not_reachable c a b hRn b).2 hb
      obtain ⟨c', hext, hcol'⟩ := fan_rotate x y f n _ b hfan2 hbx1 hbn1
      exact ⟨c', (c.extends_kempeSwap a b x).trans hext, hcol'⟩
    · have hfan2 : (c.kempeSwap a b x).IsFan x y j f := by
        refine c.isFan_kempeSwap hfan ha x (by omega) ?_
        intro i' hi' hcol
        exfalso
        have h1 : f (i' + 1) = f (j + 1) := c.col_proper hcol hbxcol
        have h2 := hfan.inj (i' + 1) (by omega) (j + 1) (by omega) h1
        omega
      have hbj1 : (c.kempeSwap a b x).IsFree (f j) b :=
        (isFree_kempeSwap_of_not_reachable c a b hRj b).2 hbj
      obtain ⟨c', hext, hcol'⟩ := fan_rotate x y f j _ b hfan2 hbx1 hbj1
      exact ⟨c', (c.extends_kempeSwap a b x).trans hext, hcol'⟩

end PEC

end Vizing
end

section -- Vizing.Main
/-!
# Vizing's theorem, upper bound

Iterating the extension step colours all edges, giving a proper edge colouring with
`Δ + 1` colours; equivalently, the line graph is `(Δ + 1)`-colourable.
-/

open SimpleGraph Finset

namespace Vizing

namespace PEC

variable {V : Type*} [Fintype V] [DecidableEq V] {C : Type*} [Fintype C] [DecidableEq C]
  {G : SimpleGraph V}

/-- The colouring that colours nothing. -/
def empty (G : SimpleGraph V) (C : Type*) : PEC G C where
  col := fun _ _ => none
  col_symm := fun _ _ => rfl
  col_adj := by intro u v γ h; exact absurd h (by simp)
  col_proper := by intro u v w γ h; exact absurd h (by simp)

/-- The set of (ordered) uncoloured edges. -/
noncomputable def uncoloured [DecidableRel G.Adj] (c : PEC G C) : Finset (V × V) :=
  {p ∈ (Finset.univ : Finset (V × V)) | G.Adj p.1 p.2 ∧ c.col p.1 p.2 = none}

omit [DecidableEq V] [Fintype C] [DecidableEq C] in
lemma mem_uncoloured [DecidableRel G.Adj] (c : PEC G C) (p : V × V) :
    p ∈ c.uncoloured ↔ G.Adj p.1 p.2 ∧ c.col p.1 p.2 = none := by
  classical
  simp [uncoloured]

/-- Every graph has a proper edge colouring with more than `Δ` colours. -/
theorem exists_total [DecidableRel G.Adj] (hcard : G.maxDegree < Fintype.card C) :
    ∃ c : PEC G C, ∀ u v, G.Adj u v → c.col u v ≠ none := by
  classical
  suffices H : ∀ (k : ℕ) (c : PEC G C), c.uncoloured.card ≤ k →
      ∃ c' : PEC G C, ∀ u v, G.Adj u v → c'.col u v ≠ none by
    exact H (empty G C).uncoloured.card (empty G C) le_rfl
  intro k
  induction k with
  | zero =>
    intro c hk
    refine ⟨c, fun u v huv hcol => ?_⟩
    have hmem : (u, v) ∈ c.uncoloured := (c.mem_uncoloured (u, v)).2 ⟨huv, hcol⟩
    have := Finset.card_pos.2 ⟨_, hmem⟩
    omega
  | succ k ih =>
    intro c hk
    by_cases hall : ∀ u v, G.Adj u v → c.col u v ≠ none
    · exact ⟨c, hall⟩
    · push_neg at hall
      obtain ⟨x, y, hadj, hnone⟩ := hall
      obtain ⟨c1, hext, hc1⟩ := vizing_step c hcard hadj (by simpa using hnone)
      refine ih c1 ?_
      have hsub : c1.uncoloured ⊆ c.uncoloured := by
        intro p hp
        rw [mem_uncoloured] at hp ⊢
        refine ⟨hp.1, ?_⟩
        by_contra hcon
        exact (hext p.1 p.2 hcon) hp.2
      have hxy : (x, y) ∈ c.uncoloured := (c.mem_uncoloured (x, y)).2 ⟨hadj, by simpa using hnone⟩
      have hxy' : (x, y) ∉ c1.uncoloured := by
        rw [mem_uncoloured]
        rintro ⟨-, h⟩
        exact hc1 h
      have hlt : c1.uncoloured.card < c.uncoloured.card :=
        Finset.card_lt_card ⟨hsub, fun hcon => hxy' (hcon hxy)⟩
      omega

/-! ### From total colourings to colourings of the line graph -/

/-- The colour of an edge, as a function on `Sym2 V`. -/
def edgeColor (c : PEC G C) [Inhabited C] (e : Sym2 V) : C :=
  Sym2.lift ⟨fun u v => (c.col u v).getD default, fun u v => by simp only [c.col_symm u v]⟩ e

omit [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C] in
@[simp] lemma edgeColor_mk (c : PEC G C) [Inhabited C] (u v : V) :
    c.edgeColor s(u, v) = (c.col u v).getD default := rfl

/-- A total proper partial colouring gives a colouring of the line graph. -/
noncomputable def lineGraphColoring [Inhabited C] (c : PEC G C)
    (htot : ∀ u v, G.Adj u v → c.col u v ≠ none) : (G.lineGraph).Coloring C :=
  Coloring.mk (fun e => c.edgeColor e.1) (by
    rintro ⟨e₁, he₁⟩ ⟨e₂, he₂⟩ hadj
    rw [lineGraph_adj_iff_exists] at hadj
    obtain ⟨hne, v, hv₁, hv₂⟩ := hadj
    obtain ⟨u, rfl⟩ := Sym2.mem_iff_exists.1 hv₁
    obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.1 hv₂
    have huv : G.Adj v u := by rwa [SimpleGraph.mem_edgeSet] at he₁
    have hvw : G.Adj v w := by rwa [SimpleGraph.mem_edgeSet] at he₂
    simp only [edgeColor_mk]
    intro hcol
    obtain ⟨γ, hγ⟩ : ∃ γ, c.col v u = some γ := Option.ne_none_iff_exists'.1 (htot v u huv)
    obtain ⟨δ, hδ⟩ : ∃ δ, c.col v w = some δ := Option.ne_none_iff_exists'.1 (htot v w hvw)
    rw [hγ, hδ] at hcol
    simp only [Option.getD_some] at hcol
    subst hcol
    have huw : u = w := c.col_proper hγ hδ
    subst huw
    exact hne (Subtype.ext rfl))

end PEC

/-- **Vizing's theorem (upper bound)**: the line graph of a finite simple graph `G` is
`(Δ(G) + 1)`-colourable, i.e. `G` has a proper edge colouring with `Δ(G) + 1` colours. -/
theorem lineGraph_colorable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : (G.lineGraph).Colorable (G.maxDegree + 1) := by
  classical
  obtain ⟨c, hc⟩ := PEC.exists_total (G := G) (C := Fin (G.maxDegree + 1))
    (by simp)
  exact ⟨c.lineGraphColoring hc⟩

end Vizing
end

namespace SimpleGraph

/-- **Vizing's theorem** (upper bound), edge-chromatic-number form:
`χ'(G) ≤ Δ(G) + 1`, phrased via the line graph. -/
theorem lineGraph_chromaticNumber_le_maxDegree_succ {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.lineGraph).chromaticNumber ≤ (G.maxDegree : ℕ∞) + 1 := by
  have h : (G.lineGraph).Colorable (G.maxDegree + 1) := Vizing.lineGraph_colorable G
  have := h.chromaticNumber_le
  rwa [Nat.cast_add, Nat.cast_one] at this

end SimpleGraph



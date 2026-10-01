import BoundedCliqueGap.THPartition

/-
`BoundedCliqueGap.THForeign` — declaration-level extract of the Route B
triangle-packing development.  Only the declarations in the constant cone of
`BoundedCliqueGap.chordal_gap_linear_cliqueFree` were kept (plus the few that
the retained sources need in order to elaborate); the module documentation
below is the original one and may advertise results that were pruned away.
-/

/-
# TH2 — the foreign mass: what the packing-side recursion still has to pay

`BoundedCliqueGap/THPartition.lean` reduced the hub interface to the **foreign mass**:

  `value ≤ ν₃(hub) + 10·(n − |S₀|) + foreignMass`.

This module estimates that mass from the *edge capacities* of the packing —
again purely on the packing side, no dual telescope:

* `th_mass_le_card_of_edge_count` — a generic counting tool: if every triangle
  of a set `𝒮` of support triangles uses at least `k` edges of a set `E`, then
  `k · (mass of 𝒮) ≤ |E|`;
* `th_foreign_two_glue` — a foreign triangle uses **two** gluing edges of its
  node (own–hole edges), by `th_foreign_shape`;
* **`th_foreignMass_le_glue`** — hence
  `2 · foreignMass ≤ ∑_j |own j| · |hole j|`;
* **`th_gap_bddHole`** — so on the class of subtree representations whose holes
  have at most `d` vertices the whole recursion closes **unconditionally**:
  `value ≤ ν₃(hub) + (10 + d/2)·(n − |S₀|)`.

`BoundedCliqueGap/THObstruction.lean` shows that the hole bound cannot be dropped from
the *last* step: the foreign mass alone is quadratic on an explicit family, so
no linear bound on it exists, and the arbitration of the foreign edge cannot be
done inside this per-node bookkeeping.  That is the honest frontier of the lane.

No `sorry`, no new axioms, no `native_decide`; `#print axioms` at the end.
-/

namespace BoundedCliqueGap

open Finset

/-! ## A generic counting tool -/

section Counting

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

open scoped Classical in
/-- **Mass against edge capacities.**  If each triangle of a family `𝒮` of
support triangles carries at least `k` edges from a set `E` of non-loop edges,
then `k` times the mass of `𝒮` is at most `|E|`: each edge of `E` absorbs total
weight at most `1`. -/
theorem th_mass_le_card_of_edge_count (F : FracPacking G) (S : Finset (Finset V))
    (E : Finset (Sym2 V)) (k : ℚ)
    (hE : ∀ e ∈ E, ¬ e.IsDiag) (hS : ∀ T ∈ S, F.x T ≠ 0)
    (hcnt : ∀ T ∈ S, k ≤ ((E.filter (fun e => e ∈ triEdges T)).card : ℚ)) :
    k * (∑ T ∈ S, F.x T) ≤ (E.card : ℚ) := by
  classical
  have step : ∀ T ∈ S, k * F.x T
      ≤ ∑ e ∈ E.filter (fun e => e ∈ triEdges T), F.x T := by
    intro T hT
    rw [Finset.sum_const, nsmul_eq_mul]
    have := hcnt T hT
    nlinarith [F.nonneg T]
  calc k * (∑ T ∈ S, F.x T) = ∑ T ∈ S, k * F.x T := by rw [Finset.mul_sum]
    _ ≤ ∑ T ∈ S, ∑ e ∈ E.filter (fun e => e ∈ triEdges T), F.x T :=
        Finset.sum_le_sum step
    _ = ∑ e ∈ E, ∑ T ∈ S.filter (fun T => e ∈ triEdges T), F.x T := by
        refine Finset.sum_comm' ?_
        intro T e
        simp only [Finset.mem_filter]
        tauto
    _ ≤ ∑ e ∈ E, (1 : ℚ) := by
        refine Finset.sum_le_sum (fun e he => ?_)
        refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun T _ _ => F.nonneg T))
          (F.edge_le_one e (hE e he))
        intro T hT
        rw [Finset.mem_filter] at hT
        exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hT.2, hS T hT.1⟩
    _ = (E.card : ℚ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]

end Counting

/-! ## The foreign mass is paid by the gluing edges -/

section Foreign

variable {n t : ℕ} {par : ℕ → ℕ} {rt : Fin n → ℕ} {sub : Fin n → Finset ℕ}
  {S0 : Finset (Fin n)}

open scoped Classical in
/-- All gluing edges of the tree, over all nodes below `r`. -/
noncomputable def thGlue (sub : Fin n → Finset ℕ) (rt : Fin n → ℕ) (S0 : Finset (Fin n))
    (t r : ℕ) : Finset (Sym2 (Fin n ⊕ Fin t)) :=
  (Finset.range r).biUnion (fun j => treeGlueEdgeSet sub rt S0 t j)

lemma th_mem_thGlue {r j : ℕ} (hj : j < r) {e : Sym2 (Fin n ⊕ Fin t)}
    (he : e ∈ treeGlueEdgeSet sub rt S0 t j) : e ∈ thGlue sub rt S0 t r := by
  classical
  exact Finset.mem_biUnion.2 ⟨j, Finset.mem_range.2 hj, he⟩

/-- A gluing edge joins an own vertex to a hole vertex, so it is not a loop. -/
lemma th_thGlue_not_isDiag {r : ℕ} {e : Sym2 (Fin n ⊕ Fin t)}
    (he : e ∈ thGlue sub rt S0 t r) : ¬ e.IsDiag := by
  classical
  obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.1 he
  simp only [treeGlueEdgeSet, Finset.mem_image, Finset.mem_product] at hj
  obtain ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩ := hj
  have hdisj := treeOwn_disjoint_treeHole (sub := sub) (rt := rt) (S0 := S0) j
  rw [Finset.disjoint_left] at hdisj
  have hxy : x ≠ y := fun hc => by subst hc; exact hdisj hx hy
  simp [Sym2.isDiag_iff_proj_eq, hxy]

/-- **A foreign triangle uses two gluing edges of its node.** -/
lemma th_foreign_two_glue (h : IsSubtreeRep par rt sub) (hS0 : ∀ x ∈ S0, rt x = 0)
    {r : ℕ} (hr : ∀ x, rt x < r) {T : Finset (Fin n ⊕ Fin t)}
    (hT : IsTriangle (treeHubGraph sub S0 t) T)
    (hfor : ∀ j, ¬ IsTriangle (treePiece sub rt S0 t j) T) :
    (2 : ℚ) ≤ (((thGlue sub rt S0 t r).filter (fun e => e ∈ triEdges T)).card : ℚ) := by
  classical
  obtain ⟨a, b, c, hbc, haT, hbT, hcT, ha, hb, hc⟩ :=
    th_foreign_shape h hS0 hT (hfor (thNode rt T))
  set j := thNode (t := t) rt T with hj
  have hjr : j < r := by
    have := ((mem_treeOwn rt S0).1 ha).1
    rw [← this]; exact hr a
  have hab : a ≠ b := by
    have hdisj := treeOwn_disjoint_treeHole (sub := sub) (rt := rt) (S0 := S0) j
    rw [Finset.disjoint_left] at hdisj
    exact fun hcc => by subst hcc; exact hdisj ha hb
  have hac : a ≠ c := by
    have hdisj := treeOwn_disjoint_treeHole (sub := sub) (rt := rt) (S0 := S0) j
    rw [Finset.disjoint_left] at hdisj
    exact fun hcc => by subst hcc; exact hdisj ha hc
  set e1 : Sym2 (Fin n ⊕ Fin t) := s(Sum.inl a, Sum.inl b) with he1
  set e2 : Sym2 (Fin n ⊕ Fin t) := s(Sum.inl a, Sum.inl c) with he2
  have hglue : ∀ y : Fin n, y ∈ treeHole sub rt S0 j →
      (s(Sum.inl a, Sum.inl y) : Sym2 (Fin n ⊕ Fin t)) ∈ treeGlueEdgeSet sub rt S0 t j := by
    intro y hy
    exact Finset.mem_image.2 ⟨(a, y), Finset.mem_product.2 ⟨ha, hy⟩, rfl⟩
  have h1 : e1 ∈ (thGlue sub rt S0 t r).filter (fun e => e ∈ triEdges T) :=
    Finset.mem_filter.2 ⟨th_mem_thGlue hjr (hglue b hb),
      mk_mem_triEdges haT hbT (by simpa using hab)⟩
  have h2 : e2 ∈ (thGlue sub rt S0 t r).filter (fun e => e ∈ triEdges T) :=
    Finset.mem_filter.2 ⟨th_mem_thGlue hjr (hglue c hc),
      mk_mem_triEdges haT hcT (by simpa using hac)⟩
  have hne : e1 ≠ e2 := by
    rw [he1, he2, Ne, Sym2.eq_iff]
    push_neg
    refine ⟨fun _ hcc => ?_, fun hcc => ?_⟩
    · exact hbc (by simpa using hcc)
    · exact absurd (by simpa using hcc : a = c) hac
  have hsub : ({e1, e2} : Finset (Sym2 (Fin n ⊕ Fin t)))
      ⊆ (thGlue sub rt S0 t r).filter (fun e => e ∈ triEdges T) := by
    intro e he
    rcases Finset.mem_insert.1 he with rfl | he'
    · exact h1
    · rw [Finset.mem_singleton.1 he']; exact h2
  have hcard : ({e1, e2} : Finset (Sym2 (Fin n ⊕ Fin t))).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simp [hne]), Finset.card_singleton]
  have := Finset.card_le_card hsub
  rw [hcard] at this
  exact_mod_cast this

open scoped Classical in
/-- **The foreign mass is at most half the number of gluing slots.**  A foreign
triangle spends two own–hole edges of its node, and every edge has capacity
`1`. -/
theorem th_foreignMass_le_glue (h : IsSubtreeRep par rt sub) (hS0 : ∀ x ∈ S0, rt x = 0)
    {r : ℕ} (hr : ∀ x, rt x < r) (F : FracPacking (treeHubGraph sub S0 t)) :
    2 * thForeignMass sub rt S0 t F
      ≤ ∑ j ∈ Finset.range r,
          (((treeOwn rt S0 j).card : ℚ) * ((treeHole sub rt S0 j).card : ℚ)) := by
  classical
  have hmass := th_mass_le_card_of_edge_count F
    (Finset.univ.filter (fun T : Finset (Fin n ⊕ Fin t) => F.x T ≠ 0 ∧
      ∀ j, ¬ IsTriangle (treePiece sub rt S0 t j) T))
    (thGlue sub rt S0 t r) 2
    (fun e he => th_thGlue_not_isDiag he) ?_ ?_
  · refine le_trans hmass ?_
    have hcard : (thGlue sub rt S0 t r).card
        ≤ ∑ j ∈ Finset.range r, (treeGlueEdgeSet sub rt S0 t j).card :=
      Finset.card_biUnion_le
    have hstep : ∀ j ∈ Finset.range r, ((treeGlueEdgeSet sub rt S0 t j).card : ℚ)
        ≤ ((treeOwn rt S0 j).card : ℚ) * ((treeHole sub rt S0 j).card : ℚ) := by
      intro j _
      have := card_treeGlueEdgeSet_le (sub := sub) (rt := rt) (S0 := S0) (t := t) j
      exact_mod_cast this
    have hcardQ : ((thGlue sub rt S0 t r).card : ℚ)
        ≤ ∑ j ∈ Finset.range r, ((treeGlueEdgeSet sub rt S0 t j).card : ℚ) := by
      have : ((thGlue sub rt S0 t r).card : ℚ)
          ≤ ((∑ j ∈ Finset.range r, (treeGlueEdgeSet sub rt S0 t j).card : ℕ) : ℚ) := by
        exact_mod_cast hcard
      rwa [Nat.cast_sum] at this
    exact le_trans hcardQ (Finset.sum_le_sum hstep)
  · intro T hT
    exact ((Finset.mem_filter.1 hT).2).1
  · intro T hT
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT
    exact th_foreign_two_glue h hS0 hr (F.supp T hT.1) hT.2

/-! ## The unconditional bounded-hole regime -/

open scoped Classical in
/-- **The recursion closes unconditionally when the holes are bounded.**  If
every node's hole has at most `d` vertices then the hub gap is at most
`(10 + d/2)·(n − |S₀|)`: the clean mass is paid by the holed-clique bound of
each node, and the foreign mass by the gluing capacity. -/
theorem th_gap_bddHole (h : IsSubtreeRep par rt sub) (hS0 : ∀ x ∈ S0, rt x = 0)
    {r d : ℕ} (hr : ∀ x, rt x < r) (hd : ∀ j < r, (treeHole sub rt S0 j).card ≤ d)
    (F : FracPacking (treeHubGraph sub S0 t)) :
    F.value ≤ (nu3 (treeHubGraph sub S0 t) : ℚ)
      + (10 + (d : ℚ) / 2) * ((n - S0.card : ℕ) : ℚ) := by
  classical
  have hmaster := th_value_le_nu3_add_foreign h hr F
  have hforeign := th_foreignMass_le_glue h hS0 hr F
  have hown : (∑ j ∈ Finset.range r, ((treeOwn rt S0 j).card : ℚ))
      = ((n - S0.card : ℕ) : ℚ) := by
    have := sum_treeOwn_card rt S0 r hr
    exact_mod_cast congrArg (fun k : ℕ => (k : ℚ)) this
  have hbd : ∑ j ∈ Finset.range r,
        (((treeOwn rt S0 j).card : ℚ) * ((treeHole sub rt S0 j).card : ℚ))
      ≤ (d : ℚ) * ((n - S0.card : ℕ) : ℚ) := by
    rw [← hown, Finset.mul_sum]
    refine Finset.sum_le_sum (fun j hjm => ?_)
    have hdj : ((treeHole sub rt S0 j).card : ℚ) ≤ (d : ℚ) := by
      exact_mod_cast hd j (Finset.mem_range.1 hjm)
    have hnn : (0 : ℚ) ≤ ((treeOwn rt S0 j).card : ℚ) := by positivity
    nlinarith
  have : 2 * thForeignMass sub rt S0 t F ≤ (d : ℚ) * ((n - S0.card : ℕ) : ℚ) :=
    le_trans hforeign hbd
  linarith

end Foreign

/-! ## Axiom audit -/

end BoundedCliqueGap

import BoundedCliqueGap.Flower

/-
`BoundedCliqueGap.DualCeiling` — declaration-level extract of the Route B
triangle-packing development.  Only the declarations in the constant cone of
`BoundedCliqueGap.chordal_gap_linear_cliqueFree` were kept (plus the few that
the retained sources need in order to elaborate); the module documentation
below is the original one and may advertise results that were pruned away.
-/

/-
# The weighted (dual) LP ceiling

`value_le_edges_third` and `value_le_card_of_edgeCover` are the two special
cases (all weights `1/3`, all weights `0/1`) of one statement: *any* feasible
solution of the **dual** of the fractional triangle-packing LP bounds the
value of every fractional packing.  A dual solution is a nonnegative weight
`y e` on the edges with `∑_{e ∈ T} y e ≥ 1` for every triangle `T`.

This is the tool rung I1 needs: the flower's LP ceiling is *not* obtainable
from a uniform weight (which reproduces `|E|/3`), but is obtained from a
one-parameter family of non-uniform weights which charge the hub more and the
cross edges of the port-rich territories less.

The file also provides the small counting helpers used to evaluate `∑ y`:
`pairEdges` (the edge slots of the image of an injection, with its exact
`C(n,2)` count) and the subadditivity of a sum over unions.
-/

namespace BoundedCliqueGap

open Finset

/-! ## Subadditivity of a sum of nonnegative terms over unions -/

variable {ι : Type*} [DecidableEq ι]

lemma sumQ_union_le (A B : Finset ι) (y : ι → ℚ) (hy : ∀ i, 0 ≤ y i) :
    ∑ i ∈ A ∪ B, y i ≤ ∑ i ∈ A, y i + ∑ i ∈ B, y i := by
  have h := Finset.sum_union_inter (s₁ := A) (s₂ := B) (f := y)
  have h2 : 0 ≤ ∑ i ∈ A ∩ B, y i := Finset.sum_nonneg (fun i _ => hy i)
  linarith

lemma sumQ_biUnion_le {κ : Type*} [DecidableEq κ] (s : Finset κ) (f : κ → Finset ι)
    (y : ι → ℚ) (hy : ∀ i, 0 ≤ y i) :
    ∑ i ∈ s.biUnion f, y i ≤ ∑ k ∈ s, ∑ i ∈ f k, y i := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert k s hk ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert hk]
      exact le_trans (sumQ_union_le _ _ y hy) (by linarith)

/-! ## The dual ceiling -/

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

open scoped Classical in
/-- **The weighted LP ceiling (LP duality).**  If `y` is a nonnegative weight
on the edges of `G` such that every triangle of `G` carries total weight at
least `1`, then every fractional triangle packing has value at most the total
weight `∑_{e ∈ E(G)} y e`. -/
theorem value_le_weight_sum [Fintype G.edgeSet] (y : Sym2 V → ℚ)
    (hy : ∀ e ∈ G.edgeFinset, 0 ≤ y e)
    (hcov : ∀ T, IsTriangle G T → 1 ≤ ∑ e ∈ triEdges T, y e)
    (F : FracPacking G) :
    F.value ≤ ∑ e ∈ G.edgeFinset, y e := by
  classical
  set A := univ.filter (fun T : Finset V => F.x T ≠ 0) with hA
  have step : ∀ T ∈ A, F.x T
      ≤ ∑ e ∈ G.edgeFinset.filter (fun e => e ∈ triEdges T), y e * F.x T := by
    intro T hT
    have hT0 : F.x T ≠ 0 := by
      simp only [hA, Finset.mem_filter, Finset.mem_univ, true_and] at hT; exact hT
    have htri : IsTriangle G T := F.supp T hT0
    have hsub : G.edgeFinset.filter (fun e => e ∈ triEdges T) = triEdges T := by
      ext e
      simp only [Finset.mem_filter, and_iff_right_iff_imp]
      intro he
      exact triEdges_subset_edgeFinset htri he
    rw [hsub, ← Finset.sum_mul]
    have := hcov T htri
    nlinarith [F.nonneg T]
  calc F.value = ∑ T ∈ A, F.x T := rfl
    _ ≤ ∑ T ∈ A, ∑ e ∈ G.edgeFinset.filter (fun e => e ∈ triEdges T), y e * F.x T :=
        Finset.sum_le_sum step
    _ = ∑ e ∈ G.edgeFinset, ∑ T ∈ A.filter (fun T => e ∈ triEdges T), y e * F.x T := by
        refine Finset.sum_comm' ?_
        intro T e
        simp only [Finset.mem_filter]
        tauto
    _ ≤ ∑ e ∈ G.edgeFinset, y e := by
        refine Finset.sum_le_sum (fun e he => ?_)
        rw [← Finset.mul_sum]
        have h1 : ∑ T ∈ A.filter (fun T => e ∈ triEdges T), F.x T ≤ 1 := by
          have hnd : ¬ e.IsDiag := by
            rw [SimpleGraph.mem_edgeFinset] at he
            exact G.not_isDiag_of_mem_edgeSet he
          refine le_trans (le_of_eq ?_) (F.edge_le_one e hnd)
          refine Finset.sum_congr ?_ (fun _ _ => rfl)
          ext T
          simp only [hA, Finset.mem_filter, Finset.mem_univ, true_and]
          tauto
        have h0 : 0 ≤ y e := hy e he
        nlinarith

/-! ## The edge slots of the image of an injection -/

open scoped Classical in
/-- The edge slots `s(f a, f b)`, `a ≠ b`, of the image of an injection. -/
noncomputable def pairEdges {α β : Type*} [Fintype α] [DecidableEq α] [DecidableEq β]
    (f : α → β) : Finset (Sym2 β) :=
  ((⊤ : SimpleGraph α).edgeFinset).image (Sym2.map f)

open scoped Classical in
lemma mem_pairEdges_iff {α β : Type*} [Fintype α] [DecidableEq α] [DecidableEq β]
    {f : α → β} {e : Sym2 β} :
    e ∈ pairEdges f ↔ ∃ a b : α, a ≠ b ∧ e = s(f a, f b) := by
  classical
  simp only [pairEdges, Finset.mem_image]
  constructor
  · rintro ⟨g, hg, rfl⟩
    rw [SimpleGraph.mem_edgeFinset] at hg
    induction g with
    | _ a b => exact ⟨a, b, by simpa using hg, by simp⟩
  · rintro ⟨a, b, hab, rfl⟩
    exact ⟨s(a, b), by simpa using hab, by simp⟩

open scoped Classical in
lemma card_pairEdges {α β : Type*} [Fintype α] [DecidableEq α] [DecidableEq β]
    {f : α → β} (hf : Function.Injective f) :
    (pairEdges f).card = (Fintype.card α).choose 2 := by
  classical
  rw [pairEdges, Finset.card_image_of_injective _ (Sym2.map.injective hf),
    SimpleGraph.card_edgeFinset_top_eq_card_choose_two]

/-! ## Axiom audit -/

end BoundedCliqueGap

import BoundedCliqueGap.SteinerTools

/-
`BoundedCliqueGap.Transport` — declaration-level extract of the Route B
triangle-packing development.  Only the declarations in the constant cone of
`BoundedCliqueGap.chordal_gap_linear_cliqueFree` were kept (plus the few that
the retained sources need in order to elaborate); the module documentation
below is the original one and may advertise results that were pruned away.
-/

/-
# Transporting packings along a graph isomorphism

The rung H1 flower theorem is stated on the concrete vertex type
`Fin κ ⊕ Fin t`.  To apply it to a *graph* that happens to look like a flower
we need to move fractional packings and `ν₃` across an isomorphism.  This file
supplies that: `FracPacking.equivMap` (transport of a fractional packing, with
`value_equivMap` saying the value is unchanged), `nu3_equiv` (`ν₃` is an
isomorphism invariant), and `gap_transfer`, which moves a gap bound from one
graph to any isomorphic one.
-/

namespace BoundedCliqueGap

open Finset

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

omit [Fintype V] in
/-- Membership in `triEdges`, in unpacked form. -/
lemma mk_mem_triEdges_iff {T : Finset V} {a b : V} :
    s(a, b) ∈ triEdges T ↔ a ∈ T ∧ b ∈ T ∧ a ≠ b := by
  simp only [triEdges, Finset.mem_filter, Finset.mk_mem_sym2_iff,
    Sym2.isDiag_iff_proj_eq]
  tauto

omit [Fintype V] [Fintype W] in
/-- `triEdges` commutes with relabelling. -/
lemma mk_mem_triEdges_image (g : V ≃ W) (T : Finset V) (a b : W) :
    s(a, b) ∈ triEdges (T.image g) ↔ s(g.symm a, g.symm b) ∈ triEdges T := by
  simp only [mk_mem_triEdges_iff, Finset.mem_image]
  constructor
  · rintro ⟨⟨u, hu, rfl⟩, ⟨v, hv, rfl⟩, hne⟩
    refine ⟨by simpa using hu, by simpa using hv, ?_⟩
    simpa using fun h => hne (by rw [h])
  · rintro ⟨ha, hb, hne⟩
    exact ⟨⟨g.symm a, ha, by simp⟩, ⟨g.symm b, hb, by simp⟩,
      fun h => hne (by rw [h])⟩

variable {G : SimpleGraph V} {H : SimpleGraph W}

/-- Transport of a fractional packing along an isomorphism. -/
noncomputable def FracPacking.equivMap (e : V ≃ W)
    (he : ∀ u v, G.Adj u v ↔ H.Adj (e u) (e v)) (F : FracPacking G) : FracPacking H where
  x := fun T => F.x (T.image e.symm)
  nonneg := fun T => F.nonneg _
  supp := by
    intro T hT
    have h := F.supp _ hT
    refine ⟨?_, ?_⟩
    · have := h.1
      rwa [Finset.card_image_of_injective _ e.symm.injective] at this
    · intro u hu v hv huv
      have hu' : e.symm u ∈ T.image e.symm := Finset.mem_image_of_mem _ hu
      have hv' : e.symm v ∈ T.image e.symm := Finset.mem_image_of_mem _ hv
      have hne : e.symm u ≠ e.symm v := fun hc => huv (e.symm.injective hc)
      have := h.2 _ hu' _ hv' hne
      have h2 := (he (e.symm u) (e.symm v)).1 this
      simpa using h2
  edge_le_one := by
    intro f hf
    induction f with
    | _ a b =>
      have hf' : ¬ (s(e.symm a, e.symm b) : Sym2 V).IsDiag := by
        simp only [Sym2.isDiag_iff_proj_eq] at hf ⊢
        exact fun hc => hf (by simpa using congrArg e hc)
      have hbase := F.edge_le_one _ hf'
      refine le_trans (le_of_eq ?_) hbase
      refine Finset.sum_nbij' (i := fun T => T.image e.symm) (j := fun T => T.image e)
        ?_ ?_ ?_ ?_ ?_
      · intro T hT
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT ⊢
        refine ⟨?_, hT.2⟩
        exact (mk_mem_triEdges_image e.symm T (e.symm a) (e.symm b)).2 (by simpa using hT.1)
      · intro T hT
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT ⊢
        refine ⟨?_, ?_⟩
        · have := (mk_mem_triEdges_image e T a b).2 (by simpa using hT.1)
          simpa using this
        · simpa [Finset.image_image] using hT.2
      · intro T _
        simp [Finset.image_image]
      · intro T _
        simp [Finset.image_image]
      · intro T _
        rfl

@[simp] lemma FracPacking.value_equivMap (e : V ≃ W)
    (he : ∀ u v, G.Adj u v ↔ H.Adj (e u) (e v)) (F : FracPacking G) :
    (F.equivMap e he).value = F.value := by
  classical
  refine Finset.sum_nbij' (i := fun T => T.image e.symm) (j := fun T => T.image e)
    ?_ ?_ ?_ ?_ ?_
  · intro T hT
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT ⊢
    exact hT
  · intro T hT
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT ⊢
    simpa [FracPacking.equivMap, Finset.image_image] using hT
  · intro T _
    simp [Finset.image_image]
  · intro T _
    simp [Finset.image_image]
  · intro T _
    rfl

/-- `ν₃` is an isomorphism invariant. -/
theorem nu3_equiv (e : V ≃ W) (he : ∀ u v, G.Adj u v ↔ H.Adj (e u) (e v)) :
    nu3 G = nu3 H := by
  refine le_antisymm (nu3_le_of_embedding e.toEmbedding (fun u v h => (he u v).1 h)) ?_
  refine nu3_le_of_embedding e.symm.toEmbedding (fun u v h => ?_)
  exact (he (e.symm u) (e.symm v)).2 (by simpa using h)

/-- **Transport of a gap bound along an isomorphism.** -/
theorem gap_transfer (e : V ≃ W) (he : ∀ u v, G.Adj u v ↔ H.Adj (e u) (e v)) (c : ℚ)
    (h : ∀ F : FracPacking H, F.value ≤ (nu3 H : ℚ) + c) (F : FracPacking G) :
    F.value ≤ (nu3 G : ℚ) + c := by
  have h1 := h (F.equivMap e he)
  rw [FracPacking.value_equivMap] at h1
  rw [nu3_equiv e he]
  exact h1

/-! ## Axiom audit -/

end BoundedCliqueGap

/-
# Transport of the edge-set calculus along an injective map of vertex types.

`BKLO.Core` transports triangle-decomposability along an injective relabelling `ℕ → ℕ`, and
`BKLO.TransportV` along a placement `ℕ → V`.  The core-absorber construction of
`BKLO.CoreAbsorbers` needs the same statements for an injective map between two *arbitrary* vertex
types (concretely `↥S → V`, moving the absorbers built inside the host `S` back to the ambient
vertex type).
-/
import BKLO.TransportV

open Finset

namespace BKLO

variable {W V : Type*} [DecidableEq W] [DecidableEq V]

omit [DecidableEq W] [DecidableEq V] in
theorem sym2_isDiag_map {f : W → V} (hf : Function.Injective f) {e : Sym2 W} :
    (Sym2.map f e).IsDiag ↔ e.IsDiag := by
  induction e using Sym2.ind with
  | _ x y => simp [Sym2.isDiag_iff_proj_eq, hf.eq_iff]

theorem cliqueEdges_image_of_injective {f : W → V} (hf : Function.Injective f) (t : Finset W) :
    cliqueEdges (t.image f) = (cliqueEdges t).image (Sym2.map f) := by
  ext e
  induction e using Sym2.ind with
  | _ x y =>
    constructor
    · intro he
      rw [mem_cliqueEdgesV] at he
      obtain ⟨hmem, hne⟩ := he
      obtain ⟨a, ha, hax⟩ := Finset.mem_image.1 (hmem x (by simp))
      obtain ⟨b, hb, hby⟩ := Finset.mem_image.1 (hmem y (by simp))
      subst hax
      subst hby
      refine Finset.mem_image.2 ⟨s(a, b), mem_cliqueEdgesV.2 ⟨?_, ?_⟩, by simp⟩
      · rintro z hz
        simp only [Sym2.mem_iff] at hz
        rcases hz with rfl | rfl <;> assumption
      · rw [← sym2_isDiag_map hf (e := s(a, b))]
        simpa using hne
    · intro he
      obtain ⟨e', he', heq⟩ := Finset.mem_image.1 he
      rw [mem_cliqueEdgesV] at he'
      rw [mem_cliqueEdgesV]
      refine ⟨?_, ?_⟩
      · intro z hz
        rw [← heq] at hz
        obtain ⟨w, hw, rfl⟩ := Sym2.mem_map.1 hz
        exact Finset.mem_image_of_mem f (he'.1 w hw)
      · rw [← heq, sym2_isDiag_map hf]
        exact he'.2

/-- Triangle-decomposability transports along an injective map of vertex types. -/
theorem TriDecomp.mapInj {f : W → V} (hf : Function.Injective f) {E : Finset (Sym2 W)}
    (h : TriDecomp E) : TriDecomp (E.image (Sym2.map f)) := by
  classical
  obtain ⟨P, hc, hd, he⟩ := h
  refine ⟨P.image (fun t => t.image f), ?_, ?_, ?_⟩
  · rintro t ht
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 ht
    rw [Finset.card_image_of_injective _ hf, hc s hs]
  · rintro t ht t' ht' hne
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 ht
    obtain ⟨s', hs', rfl⟩ := Finset.mem_image.1 ht'
    have hss' : s ≠ s' := by rintro rfl; exact hne rfl
    rw [cliqueEdges_image_of_injective hf, cliqueEdges_image_of_injective hf]
    exact (Finset.disjoint_image (Sym2.map.injective hf)).2 (hd s hs s' hs' hss')
  · rw [← he]
    simp only [famEdges]
    ext e
    simp only [Finset.mem_biUnion, Finset.mem_image]
    constructor
    · rintro ⟨t, ⟨s, hs, rfl⟩, hmem⟩
      rw [cliqueEdges_image_of_injective hf] at hmem
      obtain ⟨e', he', rfl⟩ := Finset.mem_image.1 hmem
      exact ⟨e', ⟨s, hs, he'⟩, rfl⟩
    · rintro ⟨e', ⟨s, hs, he'⟩, rfl⟩
      exact ⟨s.image f, ⟨s, hs, rfl⟩, by
        rw [cliqueEdges_image_of_injective hf]; exact Finset.mem_image_of_mem _ he'⟩

/-- Absorbers transport along an injective map of vertex types. -/
theorem IsAbsorber.mapInj {f : W → V} (hf : Function.Injective f) {A H : Finset (Sym2 W)}
    (h : IsAbsorber A H) : IsAbsorber (A.image (Sym2.map f)) (H.image (Sym2.map f)) := by
  classical
  obtain ⟨hd, hA, hAH⟩ := h
  refine ⟨(Finset.disjoint_image (Sym2.map.injective hf)).2 hd, hA.mapInj hf, ?_⟩
  have := hAH.mapInj hf
  rwa [Finset.image_union] at this

end BKLO

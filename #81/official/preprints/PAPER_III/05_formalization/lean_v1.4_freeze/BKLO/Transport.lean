/-
# Transporting finite gadgets onto arbitrary vertices.

The explicit finite absorbers of `BKLO.Gadgets` are verified by `decide` on the concrete vertex set
`{0, 1, …, k-1}` and then *transported* onto an arbitrary list of `k` distinct naturals along an
injective relabelling `f : ℕ → ℕ`.  This file provides the relabelling (`exists_inj_map`) and the
fact that all the notions involved — `pathEdges`, `cycEdges`, `supp`, `Covers`, `IsAbsorber` —
commute with it.
-/
import BKLO.Cycles
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Tactic.NormNum

open Finset

namespace BKLO

/-- Any list of distinct naturals is the image of an initial segment under an injective map. -/
theorem exists_inj_map (d : List ℕ) (hnd : d.Nodup) :
    ∃ f : ℕ → ℕ, Function.Injective f ∧ (List.range d.length).map f = d := by
  classical
  set B : ℕ := d.sum + 1 with hB
  have hle : ∀ x ∈ d, x < B := by
    intro x hx
    have : x ≤ d.sum := List.single_le_sum (by intro y _; exact Nat.zero_le y) x hx
    omega
  refine ⟨fun i => if h : i < d.length then d[i] else B + i, ?_, ?_⟩
  · intro i j hij
    by_cases hi : i < d.length <;> by_cases hj : j < d.length
    · simp only [dif_pos hi, dif_pos hj] at hij
      exact hnd.getElem_inj_iff.1 hij
    · simp only [dif_pos hi, dif_neg hj] at hij
      exact absurd (hij ▸ hle d[i] (List.getElem_mem hi)) (by omega)
    · simp only [dif_neg hi, dif_pos hj] at hij
      exact absurd (hij ▸ hle d[j] (List.getElem_mem hj)) (by omega)
    · simp only [dif_neg hi, dif_neg hj] at hij
      omega
  · refine List.ext_getElem (by simp) ?_
    intro n h1 h2
    simp only [List.getElem_map, List.getElem_range]
    rw [dif_pos h2]

theorem edgeList_map {f : ℕ → ℕ} : ∀ l : List ℕ,
    edgeList (l.map f) = (edgeList l).map (Sym2.map f)
  | [] => rfl
  | [_] => rfl
  | a :: b :: t => by
    simp only [List.map_cons, edgeList_cons₂, Sym2.map_pair_eq]
    congr 1
    exact edgeList_map (b :: t)

theorem pathEdges_map {f : ℕ → ℕ} (l : List ℕ) :
    pathEdges (l.map f) = (pathEdges l).image (Sym2.map f) := by
  rw [pathEdges, pathEdges, edgeList_map]
  ext e
  simp

theorem cycEdges_map {f : ℕ → ℕ} : ∀ l : List ℕ,
    cycEdges (l.map f) = (cycEdges l).image (Sym2.map f)
  | [] => by simp [cycEdges]
  | a :: t => by
    show pathEdges (f a :: (t.map f ++ [f a])) = _
    rw [cycEdges_cons, ← pathEdges_map]
    congr 1
    simp

theorem supp_image_map {f : ℕ → ℕ} (E : Finset (Sym2 ℕ)) :
    supp (E.image (Sym2.map f)) = (supp E).image f := by
  ext v
  constructor
  · intro hv
    obtain ⟨e, he, hve⟩ := mem_supp.1 hv
    obtain ⟨e', he', rfl⟩ := Finset.mem_image.1 he
    rw [Finset.mem_image]
    induction e' using Sym2.ind with
    | _ x y =>
      simp only [Sym2.map_pair_eq, Sym2.mem_iff] at hve
      rcases hve with rfl | rfl
      · exact ⟨x, mem_supp.2 ⟨_, he', by simp⟩, rfl⟩
      · exact ⟨y, mem_supp.2 ⟨_, he', by simp⟩, rfl⟩
  · intro hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hv
    obtain ⟨e, he, hue⟩ := mem_supp.1 hu
    refine mem_supp.2 ⟨Sym2.map f e, Finset.mem_image_of_mem _ he, ?_⟩
    induction e using Sym2.ind with
    | _ x y =>
      simp only [Sym2.mem_iff] at hue
      rcases hue with rfl | rfl <;> simp

theorem Covers.map {f : ℕ → ℕ} (hf : Function.Injective f) {T C : Finset (Sym2 ℕ)}
    (h : Covers T C) : Covers (T.image (Sym2.map f)) (C.image (Sym2.map f)) := by
  obtain ⟨hd, hdec⟩ := h
  refine ⟨(Finset.disjoint_image (Sym2.map.injective hf)).2 hd, ?_⟩
  have := TriDecomp.map hf hdec
  rwa [Finset.image_union] at this

theorem IsAbsorber.map {f : ℕ → ℕ} (hf : Function.Injective f) {A H : Finset (Sym2 ℕ)}
    (h : IsAbsorber A H) : IsAbsorber (A.image (Sym2.map f)) (H.image (Sym2.map f)) := by
  obtain ⟨hd, hA, hAH⟩ := h
  refine ⟨(Finset.disjoint_image (Sym2.map.injective hf)).2 hd, TriDecomp.map hf hA, ?_⟩
  have := TriDecomp.map hf hAH
  rwa [Finset.image_union] at this

end BKLO

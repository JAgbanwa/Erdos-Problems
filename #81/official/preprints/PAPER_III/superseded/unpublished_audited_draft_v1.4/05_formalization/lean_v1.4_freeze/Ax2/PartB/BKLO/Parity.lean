/-
  Part B (Phase 2) — parity obstruction: a graph covered by an edge-disjoint family of
  triangles has all even degrees. This is why a triangle-absorber can only absorb a leftover
  with all-even degrees (triangle-divisible), NOT merely one with `3 ∣ |L|` — it corrects the
  `TriangleAbsorber` definition (see `Defs`). Proof by Aristotle.
-/
import Ax2.PartB.BKLO.Defs

namespace Ax2.BKLO

open Finset SimpleGraph Ax2

variable {V : Type*} [DecidableEq V]

theorem coveredEdges_degree_even (P : Finset (Finset V))
    (hcard : ∀ t ∈ P, t.card = 3) (hdisj : EdgeDisjoint P) (v : V) :
    Even ((coveredEdges P).filter (fun e => v ∈ e)).card := by
  -- First, show that (triEdges t).filter (v ∈ ·) has card 2 when v ∈ t and t.card = 3
  have h_triEdges : ∀ t ∈ P, v ∈ t → ((triEdges t).filter (fun e => v ∈ e)).card = 2 := by
    intro t ht hv
    -- When t has 3 elements and v ∈ t, t = {x, y, z} for distinct x, y, z
    have htcard := hcard t ht
    obtain ⟨x, y, z, hxy, hx, hy, ht_eq⟩ := Finset.card_eq_three.mp htcard
    rw [ht_eq] at hv ⊢
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · unfold triEdges; simp (config := { decide := true }) [Finset.sym2_insert]
      simp [Finset.filter_insert, hy, hxy, hx]
      simp [Finset.filter_singleton]
      rw [card_pair (by simp; constructor <;> intros <;> tauto)]
    · unfold triEdges; simp (config := { decide := true }) [Finset.sym2_insert]
      simp [Finset.filter_insert, hx, hxy, hy]
      simp [Finset.filter_singleton, hxy.symm]
      rw [card_pair (by simp; constructor <;> intros <;> tauto)]
    · unfold triEdges; simp (config := { decide := true }) [Finset.sym2_insert]
      simp [Finset.filter_insert, hy, hxy, hx]
      simp [Finset.filter_singleton, hx.symm, hy.symm]
      rw [card_pair (by simp; constructor <;> intros <;> tauto)]
  -- Now show the degree is even by partitioning edges by triangle
  rw [coveredEdges]
  -- Rewrite the filter of a biUnion as a biUnion of filters (when disjoint)
  have h_filter_biUnion : {e ∈ P.biUnion triEdges | v ∈ e} = 
      (P.filter (fun t => v ∈ t)).biUnion (fun t => (triEdges t).filter (fun e => v ∈ e)) := by
    ext e
    simp [Finset.mem_biUnion, Finset.mem_filter]
    constructor
    · rintro ⟨⟨a, ha, he⟩, hv⟩
      have hv' : v ∈ a := by
        rw [triEdges] at he
        simp at he
        exact he.1 v hv
      exact ⟨a, ⟨ha, hv'⟩, he, hv⟩
    · rintro ⟨a, ⟨ha, _⟩, he, hv⟩
      exact ⟨⟨a, ha, he⟩, hv⟩
  rw [h_filter_biUnion]
  -- The biUnion is disjoint because triEdges are edge-disjoint
  have h_disj : ∀ t₁ ∈ P.filter (fun t => v ∈ t), ∀ t₂ ∈ P.filter (fun t => v ∈ t), 
      t₁ ≠ t₂ → Disjoint ((triEdges t₁).filter (fun e => v ∈ e)) ((triEdges t₂).filter (fun e => v ∈ e)) := by
    intro t₁ ht₁ t₂ ht₂ hne
    simp at ht₁ ht₂
    exact (hdisj t₁ ht₁.1 t₂ ht₂.1 hne).mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have h_even : Even (∑ t ∈ (P.filter (fun t => v ∈ t)), ((triEdges t).filter (fun e => v ∈ e)).card) := by
    rw [Finset.sum_congr rfl (fun t ht => h_triEdges t (by simp [Finset.mem_filter] at ht; exact ht.1) (by simp [Finset.mem_filter] at ht; exact ht.2))]
    use (P.filter (fun t => v ∈ t)).card
    simp [Finset.sum_const, smul_eq_mul]
    ring
  convert h_even using 1
  rw [card_biUnion h_disj]

end Ax2.BKLO

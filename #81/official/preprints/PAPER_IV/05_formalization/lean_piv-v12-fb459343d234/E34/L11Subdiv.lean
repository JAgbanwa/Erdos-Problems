import E34.L11Claim5

/-!
# E34 — Lemma 11: the subdivided tree

Every edge `c → par c` of `Γ` is subdivided by `B + 1` new nodes `(c, 0), …, (c, B)`
(from `c` towards `par c`).  The nodes are `SNode K B = Fin K ⊕ (Fin K × Fin (B+1))`; the tree
is transported to `Fin (card (SNode K B))` by `Fintype.equivFin` (`subdiv Γ B`).

`subdiv_isSub` : a set of nodes closed under the parent map below a node `t` of minimal height
is a subtree of `subdiv Γ B`.
-/

namespace E34

open Finset

variable {K : ℕ}

/-- Nodes of the subdivided tree. -/
abbrev SNode (K B : ℕ) := Fin K ⊕ (Fin K × Fin (B + 1))

namespace RTree

variable (Γ : RTree K) (B : ℕ)

/-- Parent map of the subdivided tree. -/
def sPar : SNode K B → SNode K B
  | Sum.inl g => if g = Γ.root then Sum.inl Γ.root else Sum.inr (g, 0)
  | Sum.inr (c, j) => if h : j.val < B then Sum.inr (c, ⟨j.val + 1, by omega⟩)
      else Sum.inl (Γ.par c)

/-- Height in the subdivided tree. -/
def sH : SNode K B → ℕ
  | Sum.inl g => (B + 2) * Γ.h g
  | Sum.inr (c, j) => (B + 2) * Γ.h (Γ.par c) + (B + 1 - j.val)

theorem par_eq_self_iff (g : Fin K) : Γ.par g = g ↔ g = Γ.root := by
  constructor
  · intro h
    by_contra hg
    have := Γ.h_par g hg
    rw [h] at this; exact lt_irrefl _ this
  · rintro rfl; exact Γ.par_root

theorem h_par_le (g : Fin K) : Γ.h (Γ.par g) ≤ Γ.h g := by
  by_cases hg : g = Γ.root
  · subst hg; rw [Γ.par_root]
  · exact (Γ.h_par g hg).le

theorem sH_sPar (a : SNode K B) (ha : a ≠ Sum.inl Γ.root) : Γ.sH B (Γ.sPar B a) < Γ.sH B a := by
  rcases a with g | ⟨c, j⟩
  · have hg : g ≠ Γ.root := fun h => ha (h ▸ rfl)
    simp only [sPar, hg, if_false, sH]
    have := Γ.h_par g hg
    have : (B + 2) * (Γ.h (Γ.par g) + 1) ≤ (B + 2) * Γ.h g := Nat.mul_le_mul_left _ this
    simp only [Fin.val_zero, Nat.sub_zero]
    rw [Nat.mul_add, Nat.mul_one] at this
    omega
  · simp only [sPar]
    split_ifs with hj
    · simp only [sH]; omega
    · simp only [sH]; omega

/-- The subdivided tree, transported to `Fin _`. -/
noncomputable def subdiv : RTree (Fintype.card (SNode K B)) where
  par := fun i => Fintype.equivFin _ (Γ.sPar B ((Fintype.equivFin _).symm i))
  root := Fintype.equivFin _ (Sum.inl Γ.root)
  h := fun i => Γ.sH B ((Fintype.equivFin _).symm i)
  par_root := by simp [sPar]
  h_par := by
    intro x hx
    simp only [Equiv.symm_apply_apply]
    apply Γ.sH_sPar
    intro h
    apply hx
    rw [← h, Equiv.apply_symm_apply]

/-- A set closed under the parent map below `t`, with `t` of minimal height, is a subtree of the
subdivided tree. -/
theorem subdiv_isSub (S : Finset (SNode K B)) (t : SNode K B) (ht : t ∈ S)
    (hcl : ∀ a ∈ S, a ≠ t → Γ.sPar B a ∈ S ∧ Γ.sH B t < Γ.sH B a) :
    (Γ.subdiv B).IsSub (S.map (Fintype.equivFin _).toEmbedding) := by
  refine ⟨Fintype.equivFin _ t, (Γ.subdiv B).isSubAt_of_closed _ _ ?_ ?_⟩
  · exact mem_map_of_mem _ ht
  · intro x hx hxt
    rw [mem_map] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    have hat : a ≠ t := fun h => hxt (by rw [h]; rfl)
    obtain ⟨h1, h2⟩ := hcl a ha hat
    refine ⟨?_, ?_⟩
    · show Fintype.equivFin _ (Γ.sPar B ((Fintype.equivFin _).symm (Fintype.equivFin _ a))) ∈ _
      rw [Equiv.symm_apply_apply]
      exact mem_map_of_mem _ h1
    · show Γ.sH B ((Fintype.equivFin _).symm (Fintype.equivFin _ t)) <
        Γ.sH B ((Fintype.equivFin _).symm (Fintype.equivFin _ a))
      rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
      exact h2

end RTree

end E34

import PaperII.FiniteCover

/-!
# Paper II — Relabeling invariance of the cover minimum `tauStar`

If two cover systems `A : CoverSystem ι κ` and `A' : CoverSystem ι' κ'` correspond under a
coordinate equivalence `σ : ι ≃ ι'` and a constraint equivalence `π : κ ≃ κ'` with
`A'.support (π k) = (A.support k).map σ`, then `tauStar A' = tauStar A`.

This is the reusable core of the isomorphism-invariance of `τ₃*` (and hence `Φ_τ`): a graph
isomorphism induces such `σ` (on edge coordinates) and `π` (on triangles). Proof: transport a
feasible cover along `σ`; cost and feasibility are preserved in both directions, so the two
minima bound each other.
-/

open scoped BigOperators

namespace PaperII

section Relabel

variable {ι κ ι' κ' : Type*}
variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable [Fintype ι'] [DecidableEq ι'] [Fintype κ'] [DecidableEq κ']

/-- Transporting a feasible cover of `A` along `σ` yields a feasible cover of `A'` of equal cost.
    (`x ↦ x ∘ σ.symm`.) -/
theorem feasible_transport (A : CoverSystem ι κ) (A' : CoverSystem ι' κ')
    (σ : ι ≃ ι') (π : κ ≃ κ')
    (hsupp : ∀ k, A'.support (π k) = (A.support k).map σ.toEmbedding)
    {x : ι → ℝ} (hx : x ∈ FeasibleCover A) :
    (fun i' => x (σ.symm i')) ∈ FeasibleCover A' ∧
      coverCost (fun i' => x (σ.symm i')) = coverCost x := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- box
    intro i'; exact hx.1 (σ.symm i')
  · -- cover: reduce a constraint of `A'` (index `π k`) to the matching constraint of `A`
    intro k'
    obtain ⟨k, rfl⟩ := π.surjective k'
    rw [hsupp k, Finset.sum_map]
    simp only [Equiv.coe_toEmbedding, Equiv.symm_apply_apply]
    exact hx.2 k
  · -- cost is preserved by reindexing along `σ`
    unfold coverCost
    exact Equiv.sum_comp σ.symm x

/-- Relabeling invariance of the cover minimum. -/
theorem tauStar_congr (A : CoverSystem ι κ) (A' : CoverSystem ι' κ')
    (σ : ι ≃ ι') (π : κ ≃ κ')
    (hsupp : ∀ k, A'.support (π k) = (A.support k).map σ.toEmbedding) :
    tauStar A' = tauStar A := by
  -- The reverse correspondence, via the inverse equivalences.
  have hsupp' : ∀ k', A.support (π.symm k') = (A'.support k').map σ.symm.toEmbedding := by
    intro k'
    have := hsupp (π.symm k')
    rw [Equiv.apply_symm_apply] at this
    rw [this, Finset.map_map]
    ext i; simp
  refine le_antisymm ?_ ?_
  · -- tauStar A' ≤ cost of the transported optimal cover of A = tauStar A
    obtain ⟨hmem, hcost⟩ := feasible_transport A A' σ π hsupp (optimalCover_mem A)
    calc tauStar A' ≤ coverCost (fun i' => (optimalCover A) (σ.symm i')) := tauStar_le_cost A' hmem
      _ = coverCost (optimalCover A) := hcost
      _ = tauStar A := rfl
  · -- symmetric direction
    obtain ⟨hmem, hcost⟩ := feasible_transport A' A σ.symm π.symm hsupp' (optimalCover_mem A')
    calc tauStar A ≤ coverCost (fun i => (optimalCover A') (σ.symm.symm i)) := tauStar_le_cost A hmem
      _ = coverCost (optimalCover 
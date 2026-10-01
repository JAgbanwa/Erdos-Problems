import PaperIV.SplitTriangleFactor

/-!
# Odd cores: the same construction, with a linear residue

`PaperIV.SplitTriangleFactor` builds an explicit triangle packing of a complete split
graph whose core has **even** size.  This module covers odd cores by the cheapest exact
device: a packing of the split graph on a *sub-core* is literally a packing of the
split graph on the whole core, because the split graph is monotone in its core.

Concretely, for `#Core = 2n+3` and `#Hosts ≤ 2n+1` one drops one core vertex and runs
the even construction on the remaining `2n+2` core vertices.  The result is a literal
`K3` packing of the full split graph with

* `h(n+1)` triangles, `totalGain = 2h(n+1)`, `3h(n+1)` covered edges, and
* exactly `(2n+3)(n+1) - h*n` uncovered edges.

For the maximal host set `h = 2n+1` this residue is `4n+3 = 2k-3` with `k = #Core`:
linear in the size of the core, as required.  The uncovered edges are precisely the
edges at the dropped core vertex together with the unused core factors.
-/

namespace PaperIV.SplitTriangleFactorOdd

open Finset PaperIV.Model PaperIV.SplitUniformIncidence PaperIV.SplitEdgeCount
open PaperIV.PhysicalCompletion PaperIV.SplitTriangleFactor

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Monotonicity of the split graph in its core -/

theorem splitGraph_mono {Core Core' Hosts : Finset V} (h : Core' ⊆ Core) :
    splitGraph Core' Hosts ≤ splitGraph Core Hosts := by
  intro x y hxy
  obtain ⟨hne, hcase⟩ := hxy
  refine ⟨hne, ?_⟩
  rcases hcase with ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩
  · exact Or.inl ⟨h hx, h hy⟩
  · exact Or.inr (Or.inl ⟨h hx, hy⟩)
  · exact Or.inr (Or.inr ⟨hx, h hy⟩)

theorem isPiece_mono {Core Core' Hosts : Finset V} (hsub : Core' ⊆ Core) {s : Finset V}
    (hs : IsPiece (splitGraph Core' Hosts) s) : IsPiece (splitGraph Core Hosts) s :=
  ⟨hs.clique.mono (splitGraph_mono hsub), hs.kind⟩

theorem isK34Packing_mono {Core Core' Hosts : Finset V} (hsub : Core' ⊆ Core)
    {P : Finset (Finset V)} (hP : IsK34Packing (splitGraph Core' Hosts) P) :
    IsK34Packing (splitGraph Core Hosts) P :=
  { pieces := fun s hs => isPiece_mono hsub (hP.pieces s hs)
    edgeDisjoint := hP.edgeDisjoint
    big := hP.big }

/-! ## The odd-core packing -/

theorem choose_two_odd (n : ℕ) : (2 * n + 3).choose 2 = (2 * n + 3) * (n + 1) := by
  have h := PaperIV.SplitUniformIncidence.mul_pred_eq_two_mul_choose_two (2 * n + 3)
  have h2 : (2 * n + 3) * (2 * n + 3 - 1) = 2 * ((2 * n + 3) * (n + 1)) := by
    have hsub : 2 * n + 3 - 1 = 2 * n + 2 := by omega
    rw [hsub]; ring
  omega

/-- **Odd cores.**  For a complete split graph with a core of odd size `k = 2n+3` and at
most `2n+1` hosts there is an explicit `K3` packing of `h(n+1)` triangles leaving
exactly `(2n+3)(n+1) - h*n` edges uncovered; for the maximal host set `h = 2n+1` this is
`2k-3`, linear in the core size. -/
theorem exists_split_triangle_packing_odd {Core Hosts : Finset V} (hd : Disjoint Core Hosts)
    {n : ℕ} (hk : Core.card = 2 * n + 3) (hh : Hosts.card ≤ 2 * n + 1) :
    ∃ P : Finset (Finset V),
      IsK34Packing (splitGraph Core Hosts) P ∧
      (∀ s ∈ P, s.card = 3) ∧
      P.card = Hosts.card * (n + 1) ∧
      totalGain P = 2 * (Hosts.card * (n + 1)) ∧
      (coveredEdges P).card = 3 * (Hosts.card * (n + 1)) ∧
      (graphEdges (splitGraph Core Hosts) \ coveredEdges P).card
        = (2 * n + 3) * (n + 1) - Hosts.card * n := by
  -- drop one core vertex
  obtain ⟨Core', hsub, hcard'⟩ : ∃ Core' ⊆ Core, Core'.card = 2 * n + 2 :=
    Finset.exists_subset_card_eq (by omega)
  have hd' : Disjoint Core' Hosts := Finset.disjoint_of_subset_left hsub hd
  obtain ⟨P, hK34, hthree, hcard, hgain, hcov, -, -⟩ :=
    exists_split_triangle_packing hd' hcard' hh
  have hbig : IsK34Packing (splitGraph Core Hosts) P := isK34Packing_mono hsub hK34
  refine ⟨P, hbig, hthree, hcard, hgain, hcov, ?_⟩
  have hsubE : coveredEdges P ⊆ graphEdges (splitGraph Core Hosts) :=
    hbig.toIsPacking.coveredEdges_subset
  rw [Finset.card_sdiff_of_subset hsubE, card_graphEdges_splitGraph hd, hcov, hk,
    choose_two_odd n]
  -- `(2n+3)(n+1) + (2n+3)h - 3h(n+1) = (2n+3)(n+1) - h*n`
  have hle : Hosts.card * n ≤ (2 * n + 3) * (n + 1) := by
    calc Hosts.card * n ≤ (2 * n + 1) * n := Nat.mul_le_mul_right _ hh
      _ ≤ (2 * n + 3) * (n + 1) := Nat.mul_le_mul (by omega) (by omega)
  have hexp : (2 * n + 3) * Hosts.card + Hosts.card * n = 3 * (Hosts.card * (n + 1)) := by
    ring
  omega

end PaperIV.SplitTriangleFactorOdd

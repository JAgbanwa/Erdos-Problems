/-
# The packing reservoir: what is proved, and what is left.

`BKLO.PackingReservoirExistence` (`BKLO/PackingAbsorb.lean`) asks, for every `γ > 0` and every
leftover degree bound `D`, for an edge-disjoint triangle family `P` in a large dense host with

1. `Δ(famEdges P) ≤ γ|S|` — sparsity, and
2. *usage closure*: every even leftover `H ⊆ E \ famEdges P` of maximum degree `≤ D` with
   `3 ∣ |H|` is absorbed by a **subfamily**: `famEdges Q ∪ H` is triangle-decomposable for some
   `Q ⊆ P`.

Clause 1 — together with the pair-covering property that any apex-type absorption needs — is
proved: `BKLO.exists_sparse_pairCovering_packing` (`BKLO/TriangleCompletion.lean`) produces a
triangle packing of maximum degree at most `γ|S|` in which *every* pair of vertices of `S` has at
least `K` common reserved neighbours, for any prescribed constant `K`.  It is built by the greedy
hub-star iteration of `BKLO/GreedyPairCover.lean` (a deterministic averaging argument, one hub star
per round, the total covering deficiency dropping by a constant factor each round) followed by the
greedy triangle completion of `BKLO/TriangleCompletion.lean`.

This file records the resulting reduction: clause 2, for pair-covering packings, is the *only*
thing still missing.  It is isolated as `BKLO.PackingUsageClosure`, and
`BKLO.packingReservoirExistence_of_usageClosure` derives `PackingReservoirExistence` — hence
`BKLO.BoundedLeftoverCoverDown` and the target `BKLO.AbsorberDenseK3BoundedLeftover` — from it.
The remaining statement is purely local: no density, no sparsity, no thresholds, only the
combinatorics of covering a bounded-degree even graph by apex triangles whose reserved legs close
up into whole triangles of the packing.  `BKLO.usageClosure_of_residual_triDecomp` puts it in the
form in which it should be attacked: find a subfamily `X ⊆ P` and an apex assignment `f` for `H`
with all legs inside `X` such that the residual `famEdges X \ apexEdges H f` is
triangle-decomposable.

*A caveat on the hypotheses of `PackingUsageClosure`.*  Pair covering is what makes the apexes
exist at all, and (`BKLO.exists_pasch_partner`) it also supplies the transversal triangles that can
consume a reserved edge without touching the leftover.  It is however not clear that it suffices:
covering one leftover edge removes one edge from each of two distinct reserved triangles, and
repairing those two residual edges by transversal triangles touches four further triangles, so the
naive repair never terminates.  `BKLO/PackingExample.lean` exhibits a leftover `6`-cycle that *is*
absorbed with every reserved edge used, but the reserved triangles there are placed by hand, in a
position adapted to the cycle.  A reservoir carrying designed re-decomposable clusters (rather
than a generic pair-covering packing) may therefore be needed; the construction of
`BKLO/TriangleCompletion.lean` is the natural place to add such structure.

Everything in this file is `sorry`-free.
-/
import BKLO.TriangleCompletion

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-- **The usage-closure gap.**

For every leftover degree bound `D` there is a covering multiplicity `K` such that: whenever `P` is
an edge-disjoint family of triangles inside a host `E ⊆ cliqueEdges S` in which every pair of
vertices of `S` has at least `K` common `famEdges P`-neighbours, every even `H ⊆ E \ famEdges P`
with `Δ(H) ≤ D` and `3 ∣ |H|` is absorbed by a subfamily of `P`.

This is the second clause of `BKLO.PackingReservoirExistence`, and the only part of it that is not
proved.  Note that the arithmetic is consistent: covering each edge of `H` by an apex triangle
consumes `2|H|` reserved edges, and `3 ∣ |H|` is exactly what makes `2|H|` a multiple of `3`. -/
def PackingUsageClosure : Prop :=
  ∀ D : ℕ, ∃ K : ℕ,
    ∀ {V : Type} [DecidableEq V] (E : Finset (Sym2 V)) (S : Finset V) (P : Finset (Finset V)),
      E ⊆ cliqueEdges S → TriFamilyIn E P →
      (∀ e ∈ cliqueEdges S, K ≤ (apexSet (famEdges P) S e).card) →
      ∀ H : Finset (Sym2 V), H ⊆ E \ famEdges P → EvenDegrees H → (∀ v : V, edeg H v ≤ D) →
        3 ∣ H.card → ∃ Q : Finset (Finset V), Q ⊆ P ∧ TriDecomp (famEdges Q ∪ H)

/-! ### Two elementary facts about the gap -/

/-- A leftover that is already triangle-decomposable needs no reservoir at all. -/
theorem usageClosure_of_triDecomp {P : Finset (Finset V)} {H : Finset (Sym2 V)}
    (hH : TriDecomp H) : ∃ Q : Finset (Finset V), Q ⊆ P ∧ TriDecomp (famEdges Q ∪ H) := by
  refine ⟨∅, Finset.empty_subset _, ?_⟩
  simpa [famEdges] using hH

/-- Every edge of a triangle packing lies in exactly one of its triangles. -/
theorem triFamily_unique_triangle {E : Finset (Sym2 V)} {P : Finset (Finset V)}
    (hP : TriFamilyIn E P) {t t' : Finset V} (ht : t ∈ P) (ht' : t' ∈ P) {e : Sym2 V}
    (het : e ∈ cliqueEdges t) (het' : e ∈ cliqueEdges t') : t = t' := by
  by_contra hne
  exact (Finset.disjoint_left.1 (hP.2.2 t ht t' ht' hne)) het het'

/-- **Pair covering produces Pasch configurations.**  If every pair of vertices of `S` has at least
four common reserved neighbours, then every reserved edge `ab` — say of the reserved triangle `t` —
is the side of a *transversal* triangle `{a, b, w}` whose three edges lie in three pairwise
distinct triangles of the packing.  These are exactly the triangles that can consume a reserved
edge without using any edge of the leftover. -/
theorem exists_pasch_partner {E : Finset (Sym2 V)} {S : Finset V} {P : Finset (Finset V)} {K : ℕ}
    (hK : 4 ≤ K) (hP : TriFamilyIn E P)
    (hcov : ∀ e ∈ cliqueEdges S, K ≤ (apexSet (famEdges P) S e).card)
    {t : Finset V} (ht : t ∈ P) {a b : V} (hab : s(a, b) ∈ cliqueEdges t)
    (habS : s(a, b) ∈ cliqueEdges S) :
    ∃ w ∈ S, w ∉ t ∧ s(a, w) ∈ famEdges P ∧ s(b, w) ∈ famEdges P ∧
      ∀ t₁ ∈ P, ∀ t₂ ∈ P, s(a, w) ∈ cliqueEdges t₁ → s(b, w) ∈ cliqueEdges t₂ →
        t₁ ≠ t ∧ t₂ ≠ t ∧ t₁ ≠ t₂ := by
  classical
  have hcard : K ≤ (apexSet (famEdges P) S s(a, b)).card := hcov _ habS
  have ht3 : t.card = 3 := hP.1 t ht
  have hne : (apexSet (famEdges P) S s(a, b) \ t).Nonempty := by
    refine Finset.card_pos.1 ?_
    have h1 : (apexSet (famEdges P) S s(a, b)).card
        ≤ (apexSet (famEdges P) S s(a, b) \ t).card + t.card :=
      Finset.card_le_card_sdiff_add_card
    omega
  obtain ⟨w, hw⟩ := hne
  rw [Finset.mem_sdiff, apexSet, Finset.mem_filter] at hw
  obtain ⟨⟨hwS, hwapex⟩, hwt⟩ := hw
  have haw : s(a, w) ∈ famEdges P := hwapex a (by simp)
  have hbw : s(b, w) ∈ famEdges P := hwapex b (by simp)
  refine ⟨w, hwS, hwt, haw, hbw, ?_⟩
  intro t₁ ht₁ t₂ ht₂ h₁ h₂
  have hnot₁ : t₁ ≠ t := by
    rintro rfl
    exact hwt ((mem_cliqueEdgesV.1 h₁).1 w (by simp))
  have hnot₂ : t₂ ≠ t := by
    rintro rfl
    exact hwt ((mem_cliqueEdgesV.1 h₂).1 w (by simp))
  refine ⟨hnot₁, hnot₂, ?_⟩
  rintro rfl
  have hat₁ : a ∈ t₁ := (mem_cliqueEdgesV.1 h₁).1 a (by simp)
  have hbt₁ : b ∈ t₁ := (mem_cliqueEdgesV.1 h₂).1 b (by simp)
  have hnd : ¬ (s(a, b) : Sym2 V).IsDiag := (mem_cliqueEdgesV.1 hab).2
  have habt₁ : s(a, b) ∈ cliqueEdges t₁ := by
    refine mem_cliqueEdgesV.2 ⟨?_, hnd⟩
    intro u hu
    simp only [Sym2.mem_iff] at hu
    rcases hu with rfl | rfl
    · exact hat₁
    · exact hbt₁
  exact hnot₁ (triFamily_unique_triangle hP ht₁ ht habt₁ hab)

/-- **Usage closure from a decomposable residual.**  Suppose the leftover `H` is covered by apex
triangles whose reserved legs all lie in a subfamily `X ⊆ P`, and suppose the *residual* — the
edges of `X` not used by the covering — is itself triangle-decomposable.  Then `X` absorbs `H`.

This is the exact shape of the remaining combinatorial task: choose the apexes (pair covering makes
them plentiful) and a subfamily `X` of the packing so that `famEdges X \ apexEdges H f`
decomposes into triangles.  Each apex triangle takes two edges of `X` away from two *different*
triangles of the packing (both legs in one triangle would make the covered edge itself reserved),
so the residual is never empty; the covering triangles of the residual are either transversal
triangles of three reserved edges from three distinct members of `P`
(`BKLO.exists_pasch_partner` shows pair covering provides candidates for these) or triangles using
edges of `H` — and it is the *global* closing-up of the residual that is missing. -/
theorem usageClosure_of_residual_triDecomp {H : Finset (Sym2 V)} {P X : Finset (Finset V)}
    {f : Sym2 V → V} (hXP : X ⊆ P) (hHP : Disjoint (famEdges P) H)
    (hass : IsApexAssignment H f) (hA : apexEdges H f ⊆ famEdges X)
    (hres : TriDecomp (famEdges X \ apexEdges H f)) :
    ∃ Q : Finset (Finset V), Q ⊆ P ∧ TriDecomp (famEdges Q ∪ H) :=
  ⟨X, hXP, triDecomp_union_of_apexAssignment hass
    (Finset.disjoint_of_subset_left (famEdges_mono hXP) hHP) hA hres⟩

/-! ### The reduction -/

/-- **The packing reservoir from usage closure.**  The sparse pair-covering triangle packing of
`BKLO.exists_sparse_pairCovering_packing` supplies everything except the usage-closure clause. -/
theorem packingReservoirExistence_of_usageClosure (h : PackingUsageClosure) :
    PackingReservoirExistence := by
  intro γ hγ D
  obtain ⟨K, hK⟩ := h D
  obtain ⟨n₀, hres⟩ := exists_sparse_pairCovering_packing hγ K
  refine ⟨n₀, ?_⟩
  intro V _ E S hn hES _ hdeg
  obtain ⟨P, hP, hPdeg, hPcov⟩ := hres E S hn hES hdeg
  exact ⟨P, hP, hPdeg, fun H hHE hHeven hHdeg hHdvd => hK E S P hES hP hPcov H hHE hHeven hHdeg hHdvd⟩

/-- **The bounded-leftover absorber from usage closure.**  Chaining the reduction above with
`BKLO.absorberDenseK3BoundedLeftover_of_packingReservoir`. -/
theorem absorberDenseK3BoundedLeftover_of_usageClosure (h : PackingUsageClosure) :
    AbsorberDenseK3BoundedLeftover :=
  absorberDenseK3BoundedLeftover_of_packingReservoir (packingReservoirExistence_of_usageClosure h)

end BKLO

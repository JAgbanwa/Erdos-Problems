/-
# Where the repaired cover-down input really sits.

`BKLO/CoverDownRefutation.lean` refutes the §10 input `CoverDownK3` as stated, and
`BKLO/CoverDownRepaired.lean` gives the repaired interface `CoverDownK3Div` (the same statement
with the two vortex levels required to induce triangle-divisible edge sets).

This file locates the repaired interface precisely: it is **implied by the triangle decomposition
theorem for dense divisible graphs itself**.  Concretely, `TriDecompDense` below — "every
triangle-divisible edge set spanned by a large vertex set `S` with minimum degree at least
`(9/10 + ε)|S|` decomposes into edge-disjoint triangles" — gives `CoverDownK3Div` in four lines of
mathematics:

* the required remainder is forced to be *all* of `F ∩ cliqueEdges W'` (up to `γ|W'|` per vertex),
  so one may simply take the remainder to be exactly `F ∩ cliqueEdges W'`;
* `F \ cliqueEdges W'` is then triangle-divisible — this is exactly what the two divisibility
  hypotheses of `CoverDownK3Div` are for — and, since `|W'| ≤ |W|/K`, it still has minimum degree
  at least `(9/10 + ε)|W|` once `K` is chosen large;
* a triangle decomposition of `F \ cliqueEdges W'` is a family `P` with all four required
  properties, with room to spare (nothing inside `W'` is touched at all).

The consequence is a statement about the *architecture* of the project rather than about
combinatorics: `CoverDownK3` is not a §10 cover-down lemma at all.  Its conclusion demands that
every edge of `F` outside the next vortex level be covered *exactly*, and `W'` is a `1/K` fraction
of `W`; so the input is at least as strong as an (almost complete, exact) triangle decomposition of
a dense divisible graph, which is the very theorem the project uses it to prove.  It therefore
cannot be discharged from the nibble (`FracToApprox`) and Dirac (`PerfectMatchingDirac`) alone: a
nibble leaves a sparse leftover spread over all of `W`, and pushing that leftover inside `W'` needs
each leftover edge to have many common neighbours inside `W'`, which the interface's hypotheses do
not provide (with `c` just above `9/10` and `|W| = K²|W'|`, a pair of vertices of `W \ W'` may have
no common neighbour in `W'` at all).

Everything here is `sorry`-free.
-/
import BKLO.CoverDownRepaired
import BKLO.SetGraph

open Finset

namespace BKLO

/-- **The triangle decomposition theorem for dense divisible graphs, in edge-set language.**  For
every `ε > 0` there is an `n₀` such that every triangle-divisible edge set spanned by a vertex set
`S` of size at least `n₀`, with minimum degree at least `(9/10 + ε)|S|` on `S`, is the edge set of
an edge-disjoint family of triangles. -/
def TriDecompDense : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
    ∀ {V : Type} [DecidableEq V] (S : Finset V) (E : Finset (Sym2 V)),
      n₀ ≤ S.card → E ⊆ cliqueEdges S → TriDivisible E →
      (∀ v ∈ S, (9 / 10 + ε) * (S.card : ℝ) ≤ (edeg E v : ℝ)) →
      ∃ P : Finset (Finset V), TriFamilyIn E P ∧ E ⊆ famEdges P

variable {V : Type} [DecidableEq V]

/-- Removing from `F` the edges inside `W'` is the same as removing `F ∩ cliqueEdges W'`. -/
theorem sdiff_cliqueEdges_eq (F : Finset (Sym2 V)) (W' : Finset V) :
    F \ (F ∩ cliqueEdges W') = F \ cliqueEdges W' := by
  ext e
  simp only [Finset.mem_sdiff, Finset.mem_inter]
  tauto

/-- **The repaired cover-down input follows from the decomposition theorem for dense divisible
graphs.**  The witness is the trivial one: cover *everything* outside `W'`, and leave the whole of
`F ∩ cliqueEdges W'` behind. -/
theorem coverDownK3Div_of_triDecompDense (h : TriDecompDense) : CoverDownK3Div := by
  classical
  intro c γ hc hγ
  -- the density slack, split in two: one half is spent on the edges inside `W'`
  set ε : ℝ := (c - 9 / 10) / 2 with hε
  have hεpos : 0 < ε := by rw [hε]; linarith only [hc]
  obtain ⟨n₁, hn₁⟩ := h ε hεpos
  obtain ⟨k, hk⟩ := exists_nat_gt (1 / ε)
  refine ⟨max 2 k, max n₁ 1, le_max_left _ _, ?_⟩
  intro V _ W W' W'' F hn₀ hW'W hW''W' hKW' _ _ hFW hFdiv hFW'div _ hdeg
  set K : ℕ := max 2 k with hK
  -- the graph to be decomposed: everything outside the next level
  set G : Finset (Sym2 V) := F \ cliqueEdges W' with hG
  have hGF : G ⊆ F := Finset.sdiff_subset
  have hGW : G ⊆ cliqueEdges W := hGF.trans hFW
  have hGdiv : TriDivisible G := by
    rw [hG, ← sdiff_cliqueEdges_eq]
    exact TriDivisible.sdiff Finset.inter_subset_left hFdiv hFW'div
  -- the minimum degree survives the removal, because `|W'| ≤ |W|/K` is a small fraction
  have hn : 1 ≤ W.card := le_trans (le_max_right n₁ 1) hn₀
  have hsmall : (W'.card : ℝ) ≤ ε * (W.card : ℝ) := by
    have hKr : (1 : ℝ) / ε < (K : ℝ) := by
      have : (k : ℝ) ≤ (K : ℝ) := by exact_mod_cast Nat.le_max_right 2 k
      linarith
    have hεK : (1 : ℝ) ≤ ε * (K : ℝ) := by
      rw [div_lt_iff₀ hεpos] at hKr
      linarith
    have hm : (0 : ℝ) ≤ (W'.card : ℝ) := by positivity
    have hKm : (K : ℝ) * (W'.card : ℝ) ≤ (W.card : ℝ) := by exact_mod_cast hKW'
    nlinarith
  have hGdeg : ∀ v ∈ W, (9 / 10 + ε) * (W.card : ℝ) ≤ (edeg G v : ℝ) := by
    intro v hv
    have h1 : edeg F v ≤ edeg G v + edeg (cliqueEdges W') v :=
      edeg_le_edeg_sdiff_add_edeg F (cliqueEdges W') v
    have h2 : edeg (cliqueEdges W') v ≤ W'.card := edeg_cliqueEdges_le W' v
    have h3 : (edeg F v : ℝ) ≤ (edeg G v : ℝ) + (W'.card : ℝ) := by
      have : (edeg F v : ℝ) ≤ (edeg G v : ℝ) + (edeg (cliqueEdges W') v : ℝ) := by
        exact_mod_cast h1
      have h2' : ((edeg (cliqueEdges W') v : ℕ) : ℝ) ≤ (W'.card : ℝ) := by exact_mod_cast h2
      linarith
    have h4 := hdeg v hv
    have hcε : c = 9 / 10 + 2 * ε := by rw [hε]; ring
    rw [hcε] at h4
    linarith
  -- decompose it
  obtain ⟨P, hP, hPcov⟩ :=
    hn₁ W G (le_trans (le_max_left n₁ 1) hn₀) hGW hGdiv hGdeg
  have hPG : famEdges P ⊆ G := famEdges_subset_of_triFamilyIn hP
  -- nothing inside `W'` has been touched
  have hkeep : F ∩ cliqueEdges W' ⊆ F \ famEdges P := by
    intro e he
    obtain ⟨heF, heW'⟩ := Finset.mem_inter.1 he
    refine Finset.mem_sdiff.2 ⟨heF, fun hmem => ?_⟩
    exact (Finset.mem_sdiff.1 (hPG hmem)).2 heW'
  refine ⟨P, ⟨hP.1, fun t ht => (hP.2.1 t ht).trans hGF, hP.2.2⟩, ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨heF, heP⟩ := Finset.mem_sdiff.1 he
    by_contra hne
    exact heP (hPcov (Finset.mem_sdiff.2 ⟨heF, hne⟩))
  · exact fun e he =>
      hkeep (Finset.mem_inter.2
        ⟨(Finset.mem_inter.1 he).1, cliqueEdges_mono hW''W' (Finset.mem_inter.1 he).2⟩)
  · intro v _
    have h1 : (edeg (F ∩ cliqueEdges W') v : ℝ) ≤ (edeg (F \ famEdges P) v : ℝ) := by
      exact_mod_cast edeg_mono hkeep v
    have h2 : (0 : ℝ) ≤ γ * (W'.card : ℝ) := by positivity
    linarith

end BKLO

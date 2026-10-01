import A4S1.ApexChordalSharp
import PaperIV.DefectDeletionRoute

/-!
# What remains of the literal order-four A4 target at rooted defect one

The literal target is

`A4Sharp₁ : ∃ N, ∀ n ≥ N, ∀ G : SimpleGraph (Fin n), RootedDefectAt G 1 →`
`  ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ defectTarget 1 n`.

Two sub-classes are now closed unconditionally:

* **apex-chordal graphs** (`G - x` chordal for some `x`), by
  `A4S1.ApexSharp.apex_chordal_sharp`;
* **graphs that are chordal after deleting at most `padBudget 1 n = Q₁(n) - M(n)` edges**,
  by the chordal theorem and padding (`PaperIV.DefectDeletionRoute`).

`ResidualCaseS1` is the literal target restricted to the rooted-defect-one graphs lying in
**neither** class.  It is an open statement, used here only as a hypothesis; it is not
asserted anywhere.  `a4Sharp_one_iff_residual` proves that the full target is *equivalent*
to it, so `ResidualCaseS1` is exactly the remaining gap.
-/

namespace A4S1.DefectOneReduction

open PaperIV.FarRounding
open PaperIV.DefectTargetArithmetic
open PaperIV.RootedSimplicialDefect
open PaperIV.DefectDeletionRoute

/-- The literal order-four A4 target at rooted defect one. -/
def A4Sharp₁ : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    RootedDefectAt G 1 →
      ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ defectTarget 1 n

/-- **The residual case (open).**  The literal target for rooted-defect-one graphs that are
not apex-chordal and are not chordal after deleting at most `padBudget 1 n` edges. -/
def ResidualCaseS1 : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    RootedDefectAt G 1 →
    (∀ x : Fin n, ¬ (G.induce (({x}ᶜ : Finset (Fin n)) : Set (Fin n))).IsChordal) →
    (∀ H : SimpleGraph (Fin n), H ≤ G → H.IsChordal →
        padBudget 1 n < (G.edgeSet \ H.edgeSet).ncard) →
      ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ defectTarget 1 n

/-- **Reduction.**  The residual case implies the full literal target. -/
theorem a4Sharp_one_of_residual (h : ResidualCaseS1) : A4Sharp₁ := by
  classical
  obtain ⟨N₁, hN₁⟩ := h
  obtain ⟨N₂, hN₂⟩ := A4S1.ApexSharp.apex_chordal_sharp
  obtain ⟨N₃, hN₃⟩ := PaperIV.Erdos81Unconditional.erdos81_cliquePartition
  refine ⟨max (max N₁ N₂) (max N₃ 2), ?_⟩
  intro n hn G _ hdef
  have hn₁ : N₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn₂ : N₂ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn₃ : N₃ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hn2 : 2 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  by_cases hapex : ∃ x : Fin n, (G.induce (({x}ᶜ : Finset (Fin n)) : Set (Fin n))).IsChordal
  · obtain ⟨x, hx⟩ := hapex
    exact hN₂ n hn₂ G x hx
  push_neg at hapex
  by_cases hdel : ∃ H : SimpleGraph (Fin n), H ≤ G ∧ H.IsChordal ∧
      (G.edgeSet \ H.edgeSet).ncard ≤ padBudget 1 n
  · obtain ⟨H, hHG, hHch, hHcard⟩ := hdel
    letI : DecidableRel H.Adj := Classical.decRel _
    obtain ⟨QH, hQH4, hQHsize⟩ := hN₃ n hn₃ H hHch
    obtain ⟨Q, hQ4, hQsize⟩ :=
      PaperIV.SubgraphPadding.exists_cliquePartition_of_subgraph G H hHG QH hQH4
    refine ⟨Q, hQ4, ?_⟩
    have hcard : (G.edgeSet \ H.edgeSet).ncard = (G.edgeFinset \ H.edgeFinset).card := by
      have hset : G.edgeSet \ H.edgeSet =
          ((G.edgeFinset \ H.edgeFinset : Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n))) := by
        ext e
        simp
      rw [hset, Set.ncard_coe_finset]
    have hbudget : (G.edgeFinset \ H.edgeFinset).card ≤ padBudget 1 n := by
      rw [← hcard]; exact hHcard
    calc Q.size ≤ QH.size + (G.edgeFinset \ H.edgeFinset).card := hQsize
      _ ≤ PaperIV.targetSize n + padBudget 1 n := Nat.add_le_add hQHsize hbudget
      _ = defectTarget 1 n := targetSize_add_padBudget 1 n hn2
  push_neg at hdel
  exact hN₁ n hn₁ G hdef hapex hdel

/-- The residual case is a special case of the full target. -/
theorem residual_of_a4Sharp_one (h : A4Sharp₁) : ResidualCaseS1 := by
  obtain ⟨N, hN⟩ := h
  exact ⟨N, fun n hn G _ hdef _ _ => hN n hn G hdef⟩

/-- **The exact remaining gap.**  The literal order-four target at rooted defect one is
equivalent to its residual case. -/
theorem a4Sharp_one_iff_residual : A4Sharp₁ ↔ ResidualCaseS1 :=
  ⟨residual_of_a4Sharp_one, a4Sharp_one_of_residual⟩

end A4S1.DefectOneReduction

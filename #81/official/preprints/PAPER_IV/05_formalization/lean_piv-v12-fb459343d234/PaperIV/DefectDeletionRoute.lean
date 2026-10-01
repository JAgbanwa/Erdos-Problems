import PaperIV.SubgraphPadding
import PaperIV.Erdos81Unconditional
import PaperIV.DefectTargetArithmetic
import PaperIV.RootedSimplicialDefect

/-!
# The deletion route to the fixed-defect target, and its exact budget

The chordal theorem of this tree produces clique partitions of order at most
four and size at most `targetSize n`.  Padding (`PaperIV.SubgraphPadding`) turns
a clique partition of a spanning subgraph into one of the whole graph at the
cost of one `K₂` per deleted edge.  Therefore the fixed-defect target for a
given `s` follows from the purely structural statement

> every large graph of rooted simplicial defect `s` becomes chordal after
> deleting at most `defectTarget s n - targetSize n` edges,

which is `ChordalDeletionBudget s` below.  This module proves that implication,
and computes the budget exactly: it is `s·n/3 + O_s(1)`, **not** `s·n`.  That
gap of a factor three is precisely the reason the naive elimination payment (up
to `s` exceptional incidences at each of the `n` elimination steps) does not
close the problem, and why an absorbing ledger is needed.

`ChordalDeletionBudget s` is a hypothesis here, never a conclusion: it is
**open**, and for `s ≥ 1` it is not known to this tree whether it is even true
(the naive elimination deletion does not produce a chordal graph, because the
retained clique of one step can lose internal edges at a later step).  It is
stated because it is a *sufficient* condition of independent interest, and
because stating it makes precise what the deletion route would have to deliver.
-/

namespace PaperIV.DefectDeletionRoute

open PaperIV.FarRounding
open PaperIV.DefectTargetArithmetic
open PaperIV.RootedSimplicialDefect

/-- The number of `K₂` pieces the fixed-defect target can afford above the
chordal target. -/
def padBudget (s n : ℕ) : ℕ := defectTarget s n - PaperIV.targetSize n

/-- The available budget is exactly the chordal target plus the padding. -/
theorem targetSize_add_padBudget (s n : ℕ) (hn : s + 1 ≤ n) :
    PaperIV.targetSize n + padBudget s n = defectTarget s n := by
  have h : PaperIV.targetSize n ≤ defectTarget s n := targetSize_le_defectTarget s n hn
  unfold padBudget
  omega

/-- **The budget is asymptotically `s·n/3`.**  Precisely,
`2·s·n ≤ 6·padBudget s n + 2s² + 2s + 5`, i.e. `padBudget s n ≥ s(n-s-1)/3 - 1`. -/
theorem two_mul_defect_mul_order_le (s n : ℕ) (hn : s + 1 ≤ n) :
    2 * s * n ≤ 6 * padBudget s n + 2 * s * s + 2 * s + 5 := by
  have hchoose0 : 2 * Nat.choose (s + 1) 2 = (s + 1) * s := by
    rw [Nat.choose_two_right, Nat.mul_comm 2,
      Nat.div_mul_cancel (Nat.even_mul_pred_self (s + 1)).two_dvd]
    simp
  have hbud : padBudget s n =
      (n + s) * (n + s + 1) / 6 - Nat.choose (s + 1) 2 - n * (n + 1) / 6 := rfl
  have hle : n * (n + 1) / 6 ≤ (n + s) * (n + s + 1) / 6 - Nat.choose (s + 1) 2 :=
    targetSize_le_defectTarget s n hn
  obtain ⟨A, hA⟩ : ∃ A, A = (n + s) * (n + s + 1) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = n * (n + 1) := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, c = Nat.choose (s + 1) 2 := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P, P = n * s := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = s * s := ⟨_, rfl⟩
  have hexp : A = B + 2 * P + Q + s := by rw [hA, hB, hP, hQ]; ring
  have hchoose : 2 * c = Q + s := by rw [hc, hQ, hchoose0]; ring
  have hgoal : 2 * s * n = 2 * P := by rw [hP]; ring
  have hQgoal : 2 * s * s = 2 * Q := by rw [hQ]; ring
  rw [hbud, ← hA, ← hB, ← hc, hgoal, hQgoal]
  rw [← hA, ← hB, ← hc] at hle
  omega

/-- **The deletion hypothesis.**  Every large graph of rooted defect `s` is
chordal after removing at most `padBudget s n` edges.  Open for `s ≥ 1`. -/
def ChordalDeletionBudget (s : ℕ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    RootedDefectAt G s → ∃ H : SimpleGraph (Fin n), H ≤ G ∧ SimpleGraph.IsChordal H ∧
      (G.edgeSet \ H.edgeSet).ncard ≤ padBudget s n

/-- **The deletion route.**  The deletion hypothesis for `s` implies the
fixed-size target for `s`: pieces of order at most four and at most
`defectTarget s n` of them. -/
theorem cliquePartition_defectTarget_of_chordalDeletionBudget (s : ℕ)
    (h : ChordalDeletionBudget s) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      RootedDefectAt G s →
        ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ defectTarget s n := by
  classical
  obtain ⟨N₁, hN₁⟩ := h
  obtain ⟨N₂, hN₂⟩ := PaperIV.Erdos81Unconditional.erdos81_cliquePartition
  refine ⟨max (max N₁ N₂) (s + 1), ?_⟩
  intro n hn G _ hdef
  have hn₁ : N₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn₂ : N₂ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hns : s + 1 ≤ n := le_trans (le_max_right _ _) hn
  obtain ⟨H, hHG, hHchordal, hHcard⟩ := hN₁ n hn₁ G hdef
  letI : DecidableRel H.Adj := Classical.decRel _
  obtain ⟨QH, hQH4, hQHsize⟩ := hN₂ n hn₂ H hHchordal
  obtain ⟨Q, hQ4, hQsize⟩ :=
    PaperIV.SubgraphPadding.exists_cliquePartition_of_subgraph G H hHG QH hQH4
  refine ⟨Q, hQ4, ?_⟩
  have hcard : (G.edgeSet \ H.edgeSet).ncard = (G.edgeFinset \ H.edgeFinset).card := by
    have hset : G.edgeSet \ H.edgeSet =
        ((G.edgeFinset \ H.edgeFinset : Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n))) := by
      ext e
      simp
    rw [hset, Set.ncard_coe_finset]
  have hbudget : (G.edgeFinset \ H.edgeFinset).card ≤ padBudget s n := by
    rw [← hcard]; exact hHcard
  calc Q.size ≤ QH.size + (G.edgeFinset \ H.edgeFinset).card := hQsize
    _ ≤ PaperIV.targetSize n + padBudget s n := Nat.add_le_add hQHsize hbudget
    _ = defectTarget s n := targetSize_add_padBudget s n hns

end PaperIV.DefectDeletionRoute

import SublinearEdit
import E32.Transfer
import PaperIV.Erdos81Unconditional

/-!
An epsilon-delta, all-defects-at-once order-four bound. Together with s(n)/n -> 0
this yields c4(G_n) <= n^2/6 + o(n^2). It does not assert the sharper ns budget.
We use the existing (nonoptimal) four-per-edit repair; no new repair hypothesis.
-/
namespace PaperIV.SublinearResearch
open Finset PaperIV.FarRounding PaperIV.RootedSimplicialDefect

theorem uniform_sublinear_partition_bound (ε : ℚ) (hε : 0 < ε) :
    ∃ θ : ℚ, 0 < θ ∧ ∃ N : ℕ, ∀ n s : ℕ, N ≤ n →
      (s : ℚ) ≤ θ*n → ∀ G : SimpleGraph (Fin n), ∀ [DecidableRel G.Adj],
      RootedDefectAt G s → ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧
        (Q.size : ℚ) ≤ (n : ℚ)^2/6+ε*(n : ℚ)^2 := by
  classical
  obtain ⟨θ,hθ,Ne,he⟩ := uniform_chordal_edit (ε/8) (by positivity)
  obtain ⟨Nc,hc⟩ := PaperIV.Erdos81Unconditional.erdos81_linear_form
  refine ⟨θ,hθ,max (max Ne Nc) ⌈1/ε⌉₊,?_⟩
  intro n s hn hs G _ hG
  have hNe : Ne ≤ n := (le_max_left _ _).trans ((le_max_left _ _).trans hn)
  have hNc : Nc ≤ n := (le_max_right _ _).trans ((le_max_left _ _).trans hn)
  have hceil : ⌈1/ε⌉₊ ≤ n := (le_max_right _ _).trans hn
  have hrec : 1/ε ≤ (n : ℚ) := (Nat.le_ceil _).trans (by exact_mod_cast hceil)
  have hεn : 1 ≤ (n : ℚ)*ε := (div_le_iff₀ hε).mp hrec
  have hn0 : (0 : ℚ) ≤ n := Nat.cast_nonneg n
  have hscale := mul_le_mul_of_nonneg_left hεn hn0
  obtain ⟨H,hH,hd⟩ := he n s hNe hs G hG
  obtain ⟨QH,hQH,hcost⟩ := hc n hNc H hH
  obtain ⟨Q,hQ,htransfer⟩ := E32.exists_partition_of_edit G H QH hQH
  refine ⟨Q,hQ,?_⟩
  have hid : (symmDiff G.edgeFinset H.edgeFinset).card =
      (G.edgeFinset \ H.edgeFinset).card+(H.edgeFinset \ G.edgeFinset).card :=
    card_union_of_disjoint disjoint_sdiff_sdiff
  rw [E34.ncard_eq_editDist, E34.editDist_eq_card, hid] at hd
  have htransferQ : (Q.size : ℚ) ≤ QH.size+(G.edgeFinset \ H.edgeFinset).card+
      4*(H.edgeFinset \ G.edgeFinset).card := by exact_mod_cast htransfer
  push_cast at hd
  have hnonneg : (0 : ℚ) ≤ (G.edgeFinset \ H.edgeFinset).card := Nat.cast_nonneg _
  nlinarith only [htransferQ,hcost,hd,hscale,hnonneg]

end PaperIV.SublinearResearch
#print axioms PaperIV.SublinearResearch.uniform_sublinear_partition_bound

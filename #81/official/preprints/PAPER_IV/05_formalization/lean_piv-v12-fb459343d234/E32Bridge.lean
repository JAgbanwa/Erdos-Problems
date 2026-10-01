import NormalizedStability
import E32.Main

namespace FixedDefectStability
open Finset PaperIV.FarRounding PaperIV.RootedSimplicialDefect
  PaperIV.DefectTargetArithmetic A4S1.TerminalPacking A4S1.IndepAll

/-- The formerly open E32 terminal is discharged by the retained constructor.
The actual-clique field of IsDefectRoot is preserved, not weakened. -/
theorem retainedTerminal_all (s : ℕ) :
    E32.RetainedTerminalAt s (epsS s) 1 (40000*((s:ℚ)+1)^3)
      ⌈(10:ℚ)^50*((s:ℚ)+1)^8⌉₊ := by
  intro n hn G _ hdef hdeg _ hloc δ hδ _ hlower
  obtain ⟨L⟩ := hloc
  have hnq : (10:ℚ)^50*((s:ℚ)+1)^8 ≤ Fintype.card (Fin n) := by
    rw [Fintype.card_fin]
    exact Nat.ceil_le.1 hn
  have hsz := abs_le.1 L.size_window
  have hmass := L.mass_small
  have h0 : (0:ℚ) ≤ ((PaperIV.RootVocab.outsideEdges G L.core).card:ℚ) := by positivity
  have h1 : (0:ℚ) ≤ (PaperIV.RootVocab.missingIncidences G L.core:ℚ) := by positivity
  have hin : AllInput G L.core s :=
    { rd := hdef
      hn := hnq
      deg := by rw [Fintype.card_fin]; exact hdeg
      clique := L.isClique
      size_lo := by rw [Fintype.card_fin]; linarith
      size_hi := by rw [Fintype.card_fin]; linarith
      miss := by rw [← all_missingIncidences_eq,Fintype.card_fin]; linarith
      out := by rw [← all_card_outsideEdges_eq,Fintype.card_fin]; linarith }
  obtain ⟨C,D,H,hCD,hCH,hDH,hcover,hcl,hDs,h2,hCHcard,hd⟩ :=
    normalized_stability hin δ hδ (by simpa only [Fintype.card_fin] using hlower)
  exact ⟨C,D,H,⟨hCD,hCH,hDH,hcover,hcl,hDs,h2,hCHcard⟩,hd⟩

/-- Quantitative edit stability, same-root partition stability, and eventual
extremal classification, with no remaining retained-terminal assumption. -/
theorem fixed_defect_stability_all (s : ℕ) :
    ∃ γ : ℚ, 0 < γ ∧ ∃ N : ℕ,
      E32.TheoremCPrimeAB s γ (max (40000*((s:ℚ)+1)^3) (2/epsS s)) N ∧
      E32.TheoremCPrimeC s N := by
  exact E32.theoremCPrime_of_retained (epsS_pos (s := s)) (by norm_num)
    (by positivity) (retainedTerminal_all s)

end FixedDefectStability
#print axioms FixedDefectStability.retainedTerminal_all
#print axioms FixedDefectStability.fixed_defect_stability_all

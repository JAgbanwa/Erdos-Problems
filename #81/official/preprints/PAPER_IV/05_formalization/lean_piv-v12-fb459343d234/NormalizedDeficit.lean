import StrictTerminal
import BaselineCapacity

namespace FixedDefectStability
open Finset PaperIV.FarRounding PaperIV.DefectTargetArithmetic
  A4S1.TerminalPacking A4S1.IndepAll

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {A : Finset V} {s : ℕ}

/-- Near optimality pays for all three structural defects simultaneously.
The comparator gap is nonnegative at the integer target, not just asymptotically.
No edit-distance realization is assumed or claimed here. -/
theorem normalized_deficit_budget (h : AllInput G A s) (δ : ℚ)
    (hlower : ∀ Q : CliquePartition G, Q.OrderAtMost 4 →
      (defectTarget s (Fintype.card V) : ℚ) - δ ≤ Q.size) :
    ∃ L : ℕ,
      (L : ℚ) ≤ scW V s / 10^13 + 1 ∧
      0 ≤ (defectTarget s (Fintype.card V) : ℚ) -
        terminalBaseline s (pCore G A s).card (pHost G A s).card (pT G A s).card ∧
      (pT G A s).card * scW V s / 800 ≤ residualCredit G A s L ∧
      (defectTarget s (Fintype.card V) : ℚ) -
        terminalBaseline s (pCore G A s).card (pHost G A s).card (pT G A s).card +
      ((pCore G A s).card * (pHost G A s).card -
        (crossCount G (pCore G A s) (pHost G A s) : ℚ)) +
      (inEdges G (pHost G A s)).card / (2000 * ((s : ℚ)+1)^2) +
      residualCredit G A s L ≤ δ := by
  obtain ⟨Q,L,hQ,hL,hcredit,hpaid⟩ := normalized_retained h
  have hSlo := h.card_core_lo
  have hHlo := h.card_host_lo
  have hv := h.v_pos
  have hvw := h.v_le_w
  have hwn := h.w_le_n
  have hSw := h.S_le_w'
  have hS1 := S_ge_one (s := s)
  have hm : s+2 ≤ (pCore G A s).card + (pHost G A s).card := by
    have : ((s+2 : ℕ) : ℚ) ≤ (pCore G A s).card + (pHost G A s).card := by
      push_cast
      nlinarith
    exact_mod_cast this
  have htot := card_total (G := G) (A := A) (s := s)
  have hbase := terminalBaseline_le s (pCore G A s).card
    (pHost G A s).card (pT G A s).card hm
  rw [htot] at hbase
  refine ⟨L, hL, sub_nonneg.mpr hbase, hcredit, ?_⟩
  have hlow := hlower Q hQ
  unfold terminalBaseline
  linarith only [hpaid, hlow]

end FixedDefectStability
#print axioms FixedDefectStability.normalized_deficit_budget

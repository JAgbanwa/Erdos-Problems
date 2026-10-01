import StrictTerminal

namespace FixedDefectStability
open Finset PaperIV.FarRounding A4S1.TerminalPacking A4S1.IndepAll

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {A : Finset V} {s : ℕ}

/-- The actual excess of the core is paid by retained credit and exceptional incidences. -/
theorem core_excess_le_residual (h : AllInput G A s) (L : ℕ)
    (hL : (L : ℚ) ≤ scW V s / 10^13 + 1) :
    (inEdges G (pCore G A s)).card - ((pCore G A s).card.choose 2 : ℚ) -
      ((s+1).choose 2 : ℚ) + (s : ℚ)*(pCore G A s).card ≤
    residualCredit G A s L + (Fintype.card V : ℚ)*(pT G A s).card := by
  have hT := h.card_T
  have hwn := h.w_le_n
  have hSS := h.S_le_w
  have hS2 : (1 : ℚ) ≤ ((s : ℚ)+1)^2 := one_le_pow₀ (S_ge_one (s := s))
  have hbig : (10 : ℚ)^50 ≤ scW V s := by nlinarith only [hSS,hS2]
  have htot : ((pCore G A s).card : ℚ)+(pHost G A s).card+(pT G A s).card =
      Fintype.card V := by exact_mod_cast (card_total (G := G) (A := A) (s := s))
  have hsmall : 2*((L : ℚ)+(pT G A s).card) ≤
      (((pCore G A s).card : ℚ)+(pHost G A s).card+s)/3 := by
    have hs : (0 : ℚ) ≤ s := Nat.cast_nonneg _
    linarith only [hL,hT,hwn,hbig,htot,hs]
  have hp := mul_le_mul_of_nonneg_left hsmall
    (show (0 : ℚ) ≤ (pT G A s).card by positivity)
  have hdeg : ∑ v ∈ pT G A s, G.degree v ≤ (pT G A s).card * Fintype.card V := by
    calc _ ≤ ∑ _v ∈ pT G A s, Fintype.card V :=
            sum_le_sum (fun v _ => (G.degree_lt_card_verts v).le)
         _ = _ := by simp
  have hdegq : ((∑ v ∈ pT G A s, G.degree v : ℕ) : ℚ) ≤
      ((pT G A s).card : ℚ)*Fintype.card V := by exact_mod_cast hdeg
  have hmin : (0 : ℚ) ≤ ((∑ v ∈ pT G A s,
      min ((pCore G A s).filter (G.Adj v)).card ((pHost G A s).filter (G.Adj v)).card : ℕ) : ℚ) :=
    Nat.cast_nonneg _
  unfold residualCredit
  nlinarith only [hp,hdegq,hmin]

end FixedDefectStability
#print axioms FixedDefectStability.core_excess_le_residual

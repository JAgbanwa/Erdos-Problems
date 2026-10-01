import StrictConstructor
import StrictParams
import StrictBudget
import A4S1.IndepAllMain

namespace FixedDefectStability
open Finset PaperIV.FarRounding A4S1.TerminalPacking A4S1.IndepAll

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {A : Finset V} {s : ℕ}

/-- Explicit retained slack; its nonnegativity is proved from AllInput, not assumed. -/
def residualCredit (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) (s L : ℕ) : ℚ :=
  (inEdges G (pCore G A s)).card -
    ((pCore G A s).card.choose 2 : ℕ) - ((s + 1).choose 2 : ℕ) +
    (s : ℚ) * (pCore G A s).card -
    (((∑ v ∈ pT G A s, G.degree v : ℕ) : ℚ) -
      2 * ((∑ v ∈ pT G A s,
        min ((pCore G A s).filter (G.Adj v)).card
            ((pHost G A s).filter (G.Adj v)).card : ℕ) : ℚ) +
      2 * (pT G A s).card * (L + (pT G A s).card) -
      (pT G A s).card * (((pCore G A s).card : ℚ) + (pHost G A s).card + s) / 3)

/-- A literal physical partition with three retained defect payments.
This is a normalized graph theorem, not an assertion of global stability. -/
theorem normalized_retained (h : AllInput G A s) :
    ∃ (Q : CliquePartition G) (L : ℕ), Q.OrderAtMost 4 ∧
      (L : ℚ) ≤ scW V s / 10^13 + 1 ∧
      (pT G A s).card * scW V s / 800 ≤ residualCredit G A s L ∧
      (Q.size : ℚ) +
        ((pCore G A s).card * (pHost G A s).card -
          (crossCount G (pCore G A s) (pHost G A s) : ℚ)) +
        (inEdges G (pHost G A s)).card / (2000 * ((s : ℚ) + 1)^2) +
        residualCredit G A s L ≤
      (pCore G A s).card * (pHost G A s).card -
        (((pCore G A s).card.choose 2 : ℕ) : ℚ) - (((s + 1).choose 2 : ℕ) : ℚ) +
        (s : ℚ) * (pCore G A s).card +
        (pT G A s).card * (((pCore G A s).card : ℚ) + (pHost G A s).card + s) / 3 := by
  obtain ⟨k,q,σ,τ,D,L,hσ,hτ,hΔ,hck,hθ,hq,hb,hD,hL,hLq,hkn,hgap⟩ := h.params_strict
  have hn0 := h.n_pos
  have hv := h.v_pos
  have hvw := h.v_le_w
  have hwn := h.w_le_n
  have hSlo := h.card_core_lo
  have hSw := h.S_le_w'
  have hS1 := S_ge_one (s := s)
  have hSpos : 0 < (pCore G A s).card := by
    have : (0 : ℚ) < (pCore G A s).card := by nlinarith
    exact_mod_cast this
  have hk : 0 < k := lt_of_lt_of_le hSpos hck
  have hσ' : ∀ v ∈ pHost G A s, ((pCore G A s).filter fun u => ¬ G.Adj v u).card +
      (pT G A s).card ≤ σ := fun v hv => by have := hσ v hv; omega
  have hτ' : ∀ u ∈ pCore G A s, ((pHost G A s).filter fun v => ¬ G.Adj u v).card +
      (pT G A s).card ≤ τ := fun u hu => by have := hτ u hu; omega
  obtain ⟨Q,hQ4,z,hz,hQ⟩ := constructor_retained (pCore G A s) (pHost G A s) (pT G A s)
    core_host_disjoint core_T_disjoint host_T_disjoint cover k q σ τ D hk
    hσ' hτ' hΔ hck hθ hq hb hD
  have hsq : Nat.sqrt D ≤ L := (Nat.sqrt_lt.2 hL).le
  have herror : 2 * (pT G A s).card * ((pT G A s).card + Nat.sqrt D) ≤
      2 * (pT G A s).card * (L + (pT G A s).card) :=
    Nat.mul_le_mul_left _ (by omega)
  have hraw : (Q.size : ℚ) + (inEdges G (pCore G A s)).card +
      2 * ((∑ v ∈ pT G A s, min ((pCore G A s).filter (G.Adj v)).card
        ((pHost G A s).filter (G.Adj v)).card : ℕ) : ℚ) + z ≤
      crossCount G (pCore G A s) (pHost G A s) +
      ((∑ v ∈ pT G A s, G.degree v : ℕ) : ℚ) +
      2 * (pT G A s).card * (L + (pT G A s).card) := by
    exact_mod_cast (show Q.size + (inEdges G (pCore G A s)).card +
      2 * ∑ v ∈ pT G A s, min ((pCore G A s).filter (G.Adj v)).card
        ((pHost G A s).filter (G.Adj v)).card + z ≤
      crossCount G (pCore G A s) (pHost G A s) +
      ∑ v ∈ pT G A s, G.degree v +
      2 * (pT G A s).card * (L + (pT G A s).card) by omega)
  have hzq : ((2 * ((pCore G A s).card - 2 * σ) - k : ℕ) : ℚ) *
      (inEdges G (pHost G A s)).card ≤ (k : ℚ) * z := by exact_mod_cast hz
  have hknq : (k : ℚ) ≤ Fintype.card V := by exact_mod_cast hkn
  have hscale := scW_mul (V := V) (s := s)
  have hpaid : (inEdges G (pHost G A s)).card /
      (2000 * ((s : ℚ) + 1)^2) ≤ (z : ℚ) := by
    apply (div_le_iff₀ (by positivity)).2
    have p1 := mul_le_mul_of_nonneg_right hgap
      (show (0 : ℚ) ≤ (inEdges G (pHost G A s)).card by positivity)
    have p2 := mul_le_mul_of_nonneg_right hknq (show (0 : ℚ) ≤ z by positivity)
    rw [← hscale] at p2
    have hw0 : 0 < scW V s := hv.trans_le hvw
    have hp : scW V s * (inEdges G (pHost G A s)).card ≤
        scW V s * ((z : ℚ) * (2000 * ((s : ℚ) + 1)^2)) := by
      nlinarith only [p1, p2, hzq]
    exact le_of_mul_le_mul_left hp hw0
  refine ⟨Q,L,hQ4,hLq,?_,?_⟩
  · have hbgt := h.hkey_strict L hLq
    unfold residualCredit
    push_cast at hbgt ⊢
    linarith only [hbgt]
  · unfold residualCredit
    linarith only [hraw, hpaid]

end FixedDefectStability
#print axioms FixedDefectStability.normalized_retained

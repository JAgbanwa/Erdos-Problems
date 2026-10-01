import A4S1.IndepAllMain

/-!
# The constructor's net budget, attached to its physical partition

Additive publication interface for Appendix E.1. No construction, threshold,
or existing theorem is changed. The two bounds below concern the SAME partition.
The normalized input is a genuine hypothesis of this local theorem, not a new
unconditional graph theorem. Its existence is discharged by the existing route.
-/

namespace PaperIV.Editorial.ConstructorBudget

open Finset PaperIV.FarRounding PaperIV.DefectTargetArithmetic
  A4S1.TerminalPacking A4S1.IndepAll

/-- Cancel the realized absorption credit against the joint budget.
All subtractions are avoided, so no truncated natural subtraction is hidden. -/
theorem cancel_budget (pieces c b s t dg mn L eC : ℕ)
    (hphysical : pieces + eC + 2 * mn ≤ c * b + dg + 2 * t * (L + t))
    (hbudget : (dg : ℚ) + 2 * t * (L + t) + c.choose 2 + (s + 1).choose 2 ≤
      eC + 2 * mn + s * c + t * ((c + b + s : ℕ) : ℚ) / 3) :
    (pieces : ℚ) + c.choose 2 + (s + 1).choose 2 ≤
      c * (b + s) + t * ((c + b + s : ℕ) : ℚ) / 3 := by
  have hphysicalQ : (pieces : ℚ) + eC + 2 * mn ≤
      c * b + dg + 2 * t * (L + t) := by exact_mod_cast hphysical
  nlinarith

/-- One literal partition witnesses both the net budget and the sharp target.
Here `pCore`, `pHost`, and `pT` are the actual normalized vertex sets. -/
theorem partition_with_net_budget
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {A : Finset V} {s : ℕ}
    (h : AllInput G A s) :
    ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧
      ((Q.size : ℚ) + (pCore G A s).card.choose 2 + (s + 1).choose 2 ≤
        (pCore G A s).card * ((pHost G A s).card + (s : ℚ)) +
          (pT G A s).card *
            (((pCore G A s).card + (pHost G A s).card + s : ℕ) : ℚ) / 3) ∧
      Q.size ≤ defectTarget s (Fintype.card V) := by
  obtain ⟨k, q, σ, τ, D, L, hσ, hτ, hΔ, hck, hθ, hq, hb, hD, hL, hLq⟩ := h.params
  have htot := card_total (G := G) (A := A) (s := s)
  have hSlo := h.card_core_lo
  have hHlo := h.card_host_lo
  have hv := h.v_pos
  have hvw := h.v_le_w
  have hwn := h.w_le_n
  have hSw := h.S_le_w'
  have hS1 := (S_ge_one (s := s))
  have hS3 : 3 ≤ (pCore G A s).card := by
    have : (3 : ℚ) ≤ (pCore G A s).card := by nlinarith
    exact_mod_cast this
  have hm : s + 2 ≤ (pCore G A s).card + (pHost G A s).card := by
    have : ((s + 2 : ℕ) : ℚ) ≤ (pCore G A s).card + (pHost G A s).card := by
      push_cast
      nlinarith
    exact_mod_cast this
  have hσ' : ∀ v ∈ pHost G A s, ((pCore G A s).filter fun u => ¬ G.Adj v u).card +
      (pT G A s).card ≤ σ := fun v hv => by have := hσ v hv; omega
  have hτ' : ∀ u ∈ pCore G A s, ((pHost G A s).filter fun v => ¬ G.Adj u v).card +
      (pT G A s).card ≤ τ := fun u hu => by have := hτ u hu; omega
  have hk : 0 < k := by omega
  obtain ⟨Q, hQ4, hQ⟩ := A4S1.Indep.caseA_indep (pCore G A s) (pHost G A s) (pT G A s)
    core_host_disjoint core_T_disjoint host_T_disjoint cover k q σ τ D hk
    hσ' hτ' hΔ hck hθ hq hb hD
  have hsq : Nat.sqrt D ≤ L := (Nat.sqrt_lt.2 hL).le
  have hQ' : Q.size + (inEdges G (pCore G A s)).card +
      2 * ∑ w ∈ pT G A s, min ((pCore G A s).filter (G.Adj w)).card
        ((pHost G A s).filter (G.Adj w)).card ≤
      (pCore G A s).card * (pHost G A s).card + ∑ w ∈ pT G A s, G.degree w +
        2 * (pT G A s).card * (L + (pT G A s).card) := by
    have : 2 * (pT G A s).card * ((pT G A s).card + Nat.sqrt D) ≤
        2 * (pT G A s).card * (L + (pT G A s).card) :=
      Nat.mul_le_mul_left _ (by omega)
    omega
  have hbudget := h.hkey L hLq
  refine ⟨Q, hQ4, cancel_budget _ _ _ _ _ _ _ _ _ hQ' hbudget, ?_⟩
  rw [← htot]
  exact own_final_all _ _ _ _ _ _ _ _ _ hm hQ' hbudget

end PaperIV.Editorial.ConstructorBudget

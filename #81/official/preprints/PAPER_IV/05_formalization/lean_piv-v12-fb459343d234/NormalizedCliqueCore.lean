import LargeCliqueCore
import A4S1.IndepAllObstr

namespace FixedDefectStability
open Finset A4S1.TerminalPacking A4S1.IndepAll

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {A : Finset V} {s : ℕ}

/-- The normalized core admits a clique of G. The vertices additionally moved
to the exterior have their full |V|-per-vertex cost paid by core excess. -/
theorem normalized_clique_core (h : AllInput G A s) :
    ∃ C ⊆ pCore G A s, G.IsClique (C : Set V) ∧ ∃ r : ℕ,
      r ≤ s ∧ C.card+s+r=(pCore G A s).card ∧
      2 ≤ C.card ∧ 2*C.card+s ≤ Fintype.card V ∧
      r*Fintype.card V ≤
        16*s*((inEdges G (pCore G A s)).card-((pCore G A s).card-s).choose 2) := by
  have hc := h.card_core_lo
  have hchi := h.card_core_hi
  have hw := h.S_le_w
  have hw' := h.S_le_w'
  have hvw := h.v_le_w
  have hwn := h.w_le_n
  have hv0 := h.v_pos
  have hlarge : 20*(s+1)^2 ≤ (pCore G A s).card := by
    have hh : (20 : ℚ)*((s : ℚ)+1)^2 ≤ (pCore G A s).card := by
      nlinarith only [hc,hw,hvw,hwn,hv0]
    exact_mod_cast hh
  have hncore : Fintype.card V ≤ 4*(pCore G A s).card := by
    have hh : (Fintype.card V : ℚ) ≤ 4*(pCore G A s).card := by
      linarith only [hc,hvw,hwn,hv0]
    exact_mod_cast hh
  have hwindow : 2*(pCore G A s).card+s ≤ Fintype.card V := by
    have hh : (2 : ℚ)*(pCore G A s).card+s ≤ Fintype.card V := by
      linarith only [hchi,hw',hwn,hv0,hvw]
    exact_mod_cast hh
  obtain ⟨C,hC,hcl,r,hrs,hcard,hpaid⟩ := exists_clique_core_with_shift (G := G)
    s (pCore G A s) hlarge h.no_core_pairs
  refine ⟨C,hC,hcl,r,hrs,hcard,?_,?_,?_⟩
  · nlinarith only [hlarge,hrs,hcard,Nat.zero_le s]
  · omega
  · have hm := Nat.mul_le_mul_left r hncore
    nlinarith only [hm,hpaid]

end FixedDefectStability
#print axioms FixedDefectStability.normalized_clique_core

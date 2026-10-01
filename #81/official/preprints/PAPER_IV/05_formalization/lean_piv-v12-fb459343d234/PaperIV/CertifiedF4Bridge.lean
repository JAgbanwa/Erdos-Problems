import PaperIV.VertexCopyWBridge

/-! # Certified rational optima and the invariant real defect -/

namespace PaperIV.CertifiedF4Bridge

open PaperIV.FarRounding
open PaperIV.VertexCopyMonotone PaperIV.VertexCopyGate PaperIV.VertexCopyWBridge

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A rational primal/dual certificate identifies the real optimum used by
the symmetrization invariant. -/
theorem optVal_eq_certified {w : ℚ} (hw : CertifiedFractionalOptimum G w) :
    optVal G = (w : ℝ) := by
  obtain ⟨xopt, hxopt⟩ := exists_fracPacking_value_eq_optVal G
  have hup : optVal G ≤ (w : ℝ) := by
    rw [← hxopt]
    exact certified_real_le hw xopt
  obtain ⟨xw, hxw⟩ := exists_real_fracPacking_value_eq hw
  have hlo : (w : ℝ) ≤ optVal G := by
    rw [← hxw]
    exact le_optVal xw
  exact le_antisymm hup hlo

/-- Consequently the invariant `F4'` is exactly the cast of the certified
rational edge-minus-optimum value. -/
theorem F4'_eq_edge_sub_certified {w : ℚ}
    (hw : CertifiedFractionalOptimum G w) :
    F4' G = ((G.edgeFinset.card : ℚ) - w : ℚ) := by
  rw [F4'_eq G, F4, optVal_eq_certified hw]
  norm_cast

end PaperIV.CertifiedF4Bridge

import A4S1.IndepAllArith

namespace FixedDefectStability
open PaperIV.FarRounding PaperIV.DefectTargetArithmetic A4S1.IndepAll

/-- The rational comparator before restoring exceptional vertices. -/
def terminalBaseline (s c b t : ℕ) : ℚ :=
  (c : ℚ)*b - (c.choose 2 : ℕ) - ((s+1).choose 2 : ℕ) +
    (s : ℚ)*c + (t : ℚ)*((c : ℚ)+b+s)/3

/-- The comparator is below the actual integer target, including floor effects. -/
theorem terminalBaseline_le (s c b t : ℕ) (hm : s+2 ≤ c+b) :
    terminalBaseline s c b t ≤ (defectTarget s (c+b+t) : ℚ) := by
  have hbase := own_targetSize_ge (c+b+s) c (by omega)
  rw [show c+b+s-c = b+s by omega] at hbase
  have hsub : targetSize (c+b+s) ≤ defectTarget s (c+b) + (s+1).choose 2 := by
    unfold defectTarget
    omega
  have hbase' : (c : ℚ)*((b : ℚ)+s) ≤
      (c.choose 2 : ℕ) + (targetSize (c+b+s) : ℕ) := by exact_mod_cast hbase
  have hsub' : (targetSize (c+b+s) : ℚ) ≤
      (defectTarget s (c+b) : ℕ) + ((s+1).choose 2 : ℕ) := by exact_mod_cast hsub
  have hadd := own_defectTarget_add s (c+b) t hm
  have hadd' : (defectTarget s (c+b) : ℚ) +
      (t : ℚ)*(((c+b+s+2)/3 : ℕ) : ℚ) ≤ (defectTarget s (c+b+t) : ℕ) := by
    exact_mod_cast hadd
  have h3 := own_three_div (c+b+s)
  have h3' : (c : ℚ)+b+s ≤ 3*(((c+b+s+2)/3 : ℕ) : ℚ) := by exact_mod_cast h3
  have hp := mul_le_mul_of_nonneg_left h3' (show (0 : ℚ) ≤ t by positivity)
  unfold terminalBaseline
  nlinarith only [hbase', hsub', hadd', hp]

end FixedDefectStability
#print axioms FixedDefectStability.terminalBaseline_le

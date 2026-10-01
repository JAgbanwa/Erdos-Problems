import E32Bridge
import E34.L11Main

/-! Explicit parameters for fixed-defect linear stability. This assembles the
retained constructor of FixedDefect, the explicit E33/E34 localization and far
rounding, and E32's deletion induction. No localization or terminal is left as
an unproved input. The formulas are enormous; no practical bound is claimed.
-/
namespace PaperIV.SublinearResearch.FixedExplicit
open Finset PaperIV.FarRounding PaperIV.RootedSimplicialDefect
open PaperIV.DefectTargetArithmetic A4S1.IndepAll

def terminalConstant (s : ℕ) : ℚ := 40000*((s : ℚ)+1)^3
def stabilityConstant (s : ℕ) : ℚ := max (terminalConstant s) (2/epsS s)
def terminalGamma (s : ℕ) : ℚ := min 1 (E33.etaNF s/4)
def stabilityGamma (s : ℕ) : ℚ := min (terminalGamma s) (epsS s/4)/2

noncomputable def sharpThreshold (s : ℕ) : ℕ := E33.Fexp E34.NeditE s
noncomputable def minimumDegreeThreshold (s : ℕ) : ℕ :=
  ⌈(10 : ℚ)^50*((s : ℚ)+1)^8⌉₊ + E33.NLoc E34.NeditE s (epsS s) +
    E18.NfarE (E33.etaNF s) + s + 5
noncomputable def deletionBase (s : ℕ) : ℕ :=
  minimumDegreeThreshold s + sharpThreshold s + s + 3 +
    ⌈1/epsS s⌉₊ + ⌈stabilityConstant s⌉₊ + 1
noncomputable def stabilityThreshold (s : ℕ) : ℕ :=
  2*deletionBase s + sharpThreshold s + s + 4

theorem terminalGamma_pos (s : ℕ) : 0 < terminalGamma s :=
  lt_min (by norm_num) (div_pos (E33.etaNF_pos s) (by norm_num))

theorem stabilityGamma_pos (s : ℕ) : 0 < stabilityGamma s := by
  exact div_pos (lt_min (terminalGamma_pos s) (div_pos (epsS_pos (s := s))
    (by norm_num))) (by norm_num)

theorem theoremC_explicit_at (s : ℕ) : E32.TheoremCAt s (sharpThreshold s) := by
  intro n hn G _ hG
  exact E34.theoremC_fully_explicit_final s n hn G hG

theorem minimumDegree_stability_explicit (s : ℕ) :
    E32.MinDegEditStable s (epsS s) (terminalGamma s) (terminalConstant s)
      (minimumDegreeThreshold s) := by
  classical
  intro n hn G _ hG hdeg δ hδ0 hδ hlow
  have hn' := hn
  unfold minimumDegreeThreshold at hn'
  obtain ⟨w,hw⟩ := PaperIV.CertifiedOptimumExistence.exists_certifiedFractionalOptimum G
  have hδeta : δ ≤ E33.etaNF s/4*(n : ℚ)^2 :=
    hδ.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _))
  have hnear : (n : ℚ)^2/6-E33.etaNF s*(n : ℚ)^2 ≤ (G.edgeFinset.card : ℚ)-w := by
    by_contra hfar
    obtain ⟨Q,hQ,hsize⟩ := E33.farSlack_explicit (E33.etaNF s) (E33.etaNF_pos s)
      n (by omega) G w hw (lt_of_not_ge hfar)
    have hl := hlow Q hQ
    have ht := PaperIV.FarSlackQuantitative.sq_div_six_le_targetSize (n := n) (by omega)
    have htarget : (PaperIV.targetSize n : ℚ) ≤ defectTarget s n := by
      exact_mod_cast targetSize_le_defectTarget s n (by omega)
    have hnpos : (0 : ℚ) < n := by exact_mod_cast (show 0 < n by omega)
    have hp := mul_pos (E33.etaNF_pos s) (sq_pos_of_pos hnpos)
    nlinarith
  have hηloc : E33.etaNF s ≤ E33.etaLoc s (epsS s) := min_le_left _ _
  have hηeps : E33.etaNF s ≤ epsS s := min_le_right _ _
  have hloc := E33.marginLoc_explicit E34.NeditE E34.editApproxExplicit_final s
    (epsS_pos (s := s)) (E33.epsS_le_two s) n (by omega) G hG w hw
    (by nlinarith [mul_le_mul_of_nonneg_right hηloc (sq_nonneg (n : ℚ))])
  have hnearQ : (n : ℚ)^2/6-epsS s*(n : ℚ)^2 ≤ (G.edgeFinset.card : ℚ)-w := by
    nlinarith [mul_le_mul_of_nonneg_right hηeps (sq_nonneg (n : ℚ))]
  have hnearR : (n : ℝ)^2/6-(epsS s : ℝ)*(n : ℝ)^2 ≤ PaperIV.VertexCopyGate.F4' G := by
    rw [PaperIV.CertifiedF4Bridge.F4'_eq_edge_sub_certified hw]
    have hh : (((n : ℚ)^2/6-epsS s*(n : ℚ)^2 : ℚ) : ℝ) ≤
        (((G.edgeFinset.card : ℚ)-w : ℚ) : ℝ) := by exact_mod_cast hnearQ
    push_cast at hh ⊢
    exact hh
  have hδone : δ ≤ 1*(n : ℚ)^2 :=
    hδ.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _))
  exact FixedDefectStability.retainedTerminal_all s n (by omega) G hG hdeg
    hnearR hloc δ hδ0 hδone hlow

/-- The explicit threshold hidden by the existential wrapper in E32. -/
theorem edit_stability_explicit (s : ℕ) :
    E32.EditStable s (stabilityGamma s) (stabilityConstant s) (2*deletionBase s) := by
  have hε := epsS_pos (s := s)
  have hγ := terminalGamma_pos s
  have hK : (0 : ℚ) ≤ terminalConstant s := by unfold terminalConstant; positivity
  have hNε : 1 ≤ epsS s*(deletionBase s : ℚ) := by
    have h1 : 1/epsS s ≤ (⌈1/epsS s⌉₊ : ℚ) := Nat.le_ceil _
    have h2 : (⌈1/epsS s⌉₊ : ℚ) ≤ deletionBase s := by
      exact_mod_cast (show ⌈1/epsS s⌉₊ ≤ deletionBase s by unfold deletionBase; omega)
    have h3 := (div_le_iff₀ hε).mp (h1.trans h2)
    linarith
  have hNK : max (terminalConstant s) (2/epsS s)+1 ≤ (deletionBase s : ℚ) := by
    have h1 : stabilityConstant s ≤ (⌈stabilityConstant s⌉₊ : ℚ) := Nat.le_ceil _
    have h2 : (⌈stabilityConstant s⌉₊ : ℚ)+1 ≤ deletionBase s := by
      exact_mod_cast (show ⌈stabilityConstant s⌉₊+1 ≤ deletionBase s by unfold deletionBase; omega)
    change stabilityConstant s+1 ≤ _
    linarith
  have hall := E32.stableAt_all s hε hγ hK (minimumDegree_stability_explicit s)
    (theoremC_explicit_at s) (deletionBase s)
    (by unfold deletionBase; omega) (by unfold deletionBase; omega)
    (by unfold deletionBase; omega) hNε hNK
  intro n hn G _ hG δ hδ0 hδ hlow
  apply hall n (by omega) G hG δ hδ0 _ hlow
  have hnN : 2*(deletionBase s : ℚ) ≤ n := by exact_mod_cast hn
  have hγ0 : 0 ≤ min (terminalGamma s) (epsS s/4) :=
    le_min hγ.le (by positivity)
  calc
    δ ≤ min (terminalGamma s) (epsS s/4)/2*(n : ℚ)^2 := hδ
    _ = min (terminalGamma s) (epsS s/4)*(n : ℚ)*((n : ℚ)/2) := by ring
    _ ≤ min (terminalGamma s) (epsS s/4)*(n : ℚ)*((n : ℚ)-deletionBase s) := by
      apply mul_le_mul_of_nonneg_left (by linarith)
      positivity

/-- Linear edit stability, simultaneous partition stability and classification
with explicit gamma(s), N(s) and the original stability constant. -/
theorem fixed_defect_stability_explicit (s : ℕ) :
    E32.TheoremCPrimeAB s (stabilityGamma s) (stabilityConstant s) (stabilityThreshold s) ∧
      E32.TheoremCPrimeC s (stabilityThreshold s) := by
  constructor
  · intro n hn
    exact E32.theoremCPrimeAB_of_editStable (edit_stability_explicit s) n
      (by unfold stabilityThreshold at hn; omega)
  · exact E32.theoremCPrimeC_of_editStable (stabilityGamma_pos s).le
      (edit_stability_explicit s) (theoremC_explicit_at s)

/-- The edit bound and baseline deficit hold for the same literal defect root,
now above a named explicit threshold and with a named positive deficit window. -/
theorem fixed_defect_edit_and_size_explicit (s n : ℕ) (hn : stabilityThreshold s ≤ n)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : RootedDefectAt G s)
    (δ : ℚ) (hδ0 : 0 ≤ δ) (hδ : δ ≤ stabilityGamma s*(n : ℚ)^2)
    (hlow : ∀ Q : CliquePartition G, Q.OrderAtMost 4 →
      (defectTarget s n : ℚ)-δ ≤ Q.size) :
    ∃ C D H : Finset (Fin n), E32.IsDefectRoot G s C D H ∧
      (E32.rootEdit G C D H : ℚ) ≤ stabilityConstant s*δ ∧
      0 ≤ (defectTarget s n : ℚ)-E32.rootBaseline C D H ∧
      (defectTarget s n : ℚ)-E32.rootBaseline C D H ≤ (1+4*stabilityConstant s)*δ := by
  obtain ⟨C,D,H,hR,hedit,_⟩ := (fixed_defect_stability_explicit s).1 n hn G hG δ hδ0 hδ hlow
  have hsum := hR.card_sum
  have h2 := hR.two_le
  have hbase := (E32.rootBaseline_le_and_eq_iff hsum hR.core_le_hosts
    (show s+2 ≤ n by omega)).1
  have hB : E32.rootBaseline C D H ≤ defectTarget s n := by
    simpa only [E32.rootBaseline,hR.card_def] using hbase
  have hBq : (E32.rootBaseline C D H : ℚ) ≤ defectTarget s n := by exact_mod_cast hB
  obtain ⟨Q,hQ4,hQ⟩ := E32.exists_partition_near_root G hR
  have hl := hlow Q hQ4
  have hQq : (Q.size : ℚ) ≤ E32.rootBaseline C D H+4*(E32.rootEdit G C D H : ℚ) := by
    exact_mod_cast hQ
  exact ⟨C,D,H,hR,hedit,sub_nonneg.mpr hBq,by nlinarith only [hl,hQq,hedit]⟩

end PaperIV.SublinearResearch.FixedExplicit
#print axioms PaperIV.SublinearResearch.FixedExplicit.fixed_defect_stability_explicit
#print axioms PaperIV.SublinearResearch.FixedExplicit.fixed_defect_edit_and_size_explicit

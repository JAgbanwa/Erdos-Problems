import FixedDefectPieceEdges
import ExtremalEditStability

/-! Publication interfaces: real deficits and a single root carrying all
finite stability conclusions. No constants or thresholds are changed. -/
namespace PaperIV.SublinearResearch
attribute [local instance] Classical.propDecidable
open Finset PaperIV.FarRounding PaperIV.RootedSimplicialDefect
  PaperIV.DefectTargetArithmetic PaperIV.RootVocab PaperIV.RootPartitionStability
  PaperIV.GraphFamilyDistance PaperIV.SplitUniformIncidence

/-- Integer partition costs allow rounding the deficit down, not up. -/
theorem lower_bound_floor_deficit {a b : ℕ} {δ : ℝ}
    (h : (a : ℝ)-δ ≤ b) : (a : ℚ)-(⌊δ⌋ : ℚ) ≤ b := by
  have hz : (a : ℤ)-(b : ℤ) ≤ ⌊δ⌋ := by
    apply Int.le_floor.mpr
    push_cast
    linarith
  have hq : (a : ℚ)-(b : ℚ) ≤ (⌊δ⌋ : ℚ) := by exact_mod_cast hz
  linarith

/-- One literal root simultaneously controls edits, its baseline, and both
the number and edge mass of noncanonical pieces in every unrestricted
partition. Both deficit parameters are real. -/
theorem fixed_defect_joint_stability_real (s n : ℕ)
    (hn : FixedExplicit.stabilityThreshold s ≤ n)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : RootedDefectAt G s)
    (δ : ℝ) (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ (FixedExplicit.stabilityGamma s : ℝ)*(n : ℝ)^2)
    (hlow : ∀ Q : CliquePartition G, Q.OrderAtMost 4 →
      (defectTarget s n : ℝ)-δ ≤ Q.size) :
    ∃ C D H : Finset (Fin n), E32.IsDefectRoot G s C D H ∧
      (E32.rootEdit G C D H : ℝ) ≤ (FixedExplicit.stabilityConstant s : ℝ)*δ ∧
      0 ≤ (defectTarget s n : ℝ)-E32.rootBaseline C D H ∧
      (defectTarget s n : ℝ)-E32.rootBaseline C D H ≤
        (1+4*(FixedExplicit.stabilityConstant s : ℝ))*δ ∧
      ∀ (Q : CliquePartition G) (τ : ℝ), (Q.size : ℝ) ≤ defectTarget s n+τ →
        ((Q.pieces.filter fun K => ¬ E32.IsCanonicalPiece C D H K).card : ℝ) ≤
          τ+(1+7*(FixedExplicit.stabilityConstant s : ℝ))*δ ∧
        (defectNoncanonicalEdgeMass C D H Q : ℝ) ≤
          10*τ+10*(1+7*(FixedExplicit.stabilityConstant s : ℝ))*δ := by
  classical
  let d : ℚ := ⌊δ⌋
  have hd0 : 0 ≤ d := by
    dsimp [d]
    exact_mod_cast (Int.floor_nonneg.mpr hδ0)
  have hdle : (d : ℝ) ≤ δ := by simpa [d] using Int.floor_le δ
  have hd : d ≤ FixedExplicit.stabilityGamma s*(n : ℚ)^2 := by
    exact_mod_cast (hdle.trans hδ)
  obtain ⟨C,D,H,hR,he,hlo,hhi⟩ :=
    FixedExplicit.fixed_defect_edit_and_size_explicit s n hn G hG d hd0 hd
      (fun Q hQ => lower_bound_floor_deficit (hlow Q hQ))
  have hA0 : (0 : ℝ) ≤ (FixedExplicit.stabilityConstant s : ℝ) := by
    have hq : (0 : ℚ) ≤ FixedExplicit.stabilityConstant s := by
      unfold FixedExplicit.stabilityConstant FixedExplicit.terminalConstant
      exact le_trans (by positivity) (le_max_left _ _)
    exact_mod_cast hq
  have heR : (E32.rootEdit G C D H : ℝ) ≤
      (FixedExplicit.stabilityConstant s : ℝ)*(d : ℝ) := by exact_mod_cast he
  have hloR : (0 : ℝ) ≤ (defectTarget s n : ℝ)-E32.rootBaseline C D H := by
    exact_mod_cast hlo
  have hhiR : (defectTarget s n : ℝ)-E32.rootBaseline C D H ≤
      (1+4*(FixedExplicit.stabilityConstant s : ℝ))*(d : ℝ) := by exact_mod_cast hhi
  have he' := heR.trans (mul_le_mul_of_nonneg_left hdle hA0)
  have hhi' := hhiR.trans (mul_le_mul_of_nonneg_left hdle (by positivity))
  refine ⟨C,D,H,hR,he',hloR,hhi',?_⟩
  intro Q τ hQ
  have hc : ((Q.pieces.filter fun K => ¬ E32.IsCanonicalPiece C D H K).card : ℝ) ≤
      (Q.size : ℝ)-E32.rootBaseline C D H+3*E32.rootEdit G C D H := by
    exact_mod_cast E32.noncanonical_card_le hR Q
  have hb : (defectNoncanonicalEdgeMass C D H Q : ℝ) ≤
      10*((Q.size : ℝ)-E32.rootBaseline C D H+3*E32.rootEdit G C D H) := by
    unfold defectNoncanonicalEdgeMass
    push_cast
    exact_mod_cast E32.noncanonical_edge_mass_le hR Q
  constructor <;> nlinarith only [hc,hb,hQ,he',hhi']

/-- Distance to the optimal-size extremal family, also for real deficits.
The square-root term is retained: it is not a linear edit bound. -/
theorem fixed_defect_exact_extremal_edit_real (s n : ℕ)
    (hn : FixedExplicit.stabilityThreshold s ≤ n)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : RootedDefectAt G s)
    (δ : ℝ) (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ (FixedExplicit.stabilityGamma s : ℝ)*(n : ℝ)^2)
    (hlow : ∀ Q : CliquePartition G, Q.OrderAtMost 4 →
      (defectTarget s n : ℝ)-δ ≤ Q.size) :
    ∃ T : SimpleGraph (Fin n), ∃ _inst : DecidableRel T.Adj,
      E32.IsAdmissibleExtremal T s ∧
        (PaperIV.EditMetric.editDist G.edgeFinset T.edgeFinset : ℝ) ≤
          (FixedExplicit.stabilityConstant s : ℝ)*δ + (n : ℝ)*
            Real.sqrt ((1+4*(FixedExplicit.stabilityConstant s : ℝ))*δ) := by
  let d : ℚ := ⌊δ⌋
  have hd0 : 0 ≤ d := by
    dsimp [d]
    exact_mod_cast (Int.floor_nonneg.mpr hδ0)
  have hdle : (d : ℝ) ≤ δ := by simpa [d] using Int.floor_le δ
  have hd : d ≤ FixedExplicit.stabilityGamma s*(n : ℚ)^2 := by
    exact_mod_cast (hdle.trans hδ)
  obtain ⟨T,inst,hT,hb⟩ := fixed_defect_exact_extremal_edit s n hn G hG d hd0 hd
    (fun Q hQ => lower_bound_floor_deficit (hlow Q hQ))
  refine ⟨T,inst,hT,hb.trans ?_⟩
  have hA0 : (0 : ℝ) ≤ (FixedExplicit.stabilityConstant s : ℝ) := by
    have hq : (0 : ℚ) ≤ FixedExplicit.stabilityConstant s := by
      unfold FixedExplicit.stabilityConstant FixedExplicit.terminalConstant
      exact le_trans (by positivity) (le_max_left _ _)
    exact_mod_cast hq
  exact add_le_add (mul_le_mul_of_nonneg_left hdle hA0)
    (mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hdle (by positivity)))
      (Nat.cast_nonneg n))

/-- The chordal constants 16, 48 and 480 hold on one root, for real
deficits and every unrestricted partition, at the original threshold. -/
theorem chordal_joint_stability_real :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ G : SimpleGraph (Fin n), ∀ [DecidableRel G.Adj],
      IsChordal G → ∀ δ : ℝ, 0 ≤ δ →
      δ ≤ (PaperIV.IntegralStability.gamma : ℝ)*(n : ℝ)^2 →
      (∀ Q : CliquePartition G, Q.OrderAtMost 4 → (PaperIV.targetSize n : ℝ)-δ ≤ Q.size) →
      ∃ R : Finset (Fin n), G.IsClique (R : Set (Fin n)) ∧
        2 ≤ R.card ∧ R.card ≤ (Finset.univ \ R).card ∧
        (PaperIV.EditMetric.editDist G.edgeFinset
          (graphEdgeSupport (splitGraph R (Finset.univ \ R))) : ℝ) ≤ 16*δ ∧
        0 ≤ (PaperIV.targetSize n : ℝ)-(PaperIV.splitBaseline n R.card : ℝ) ∧
        (PaperIV.targetSize n : ℝ)-(PaperIV.splitBaseline n R.card : ℝ) +
          (outsideEdges G R).card/16+(missingIncidences G R : ℝ)/2 ≤ δ ∧
        ∀ (Q : CliquePartition G) (τ : ℝ), (Q.size : ℝ) ≤ PaperIV.targetSize n+τ →
          ((noncanonicalPieces R Q).card : ℝ) ≤ τ+48*δ ∧
          (noncanonicalEdgeMass R Q : ℝ) ≤ 10*τ+480*δ := by
  obtain ⟨N,hN⟩ := PaperIV.IntegralStability.chordal_linear_stability_sixteen
  refine ⟨N,?_⟩
  intro n hn G _ hG δ hδ0 hδ hlow
  let d : ℚ := ⌊δ⌋
  have hd0 : 0 ≤ d := by
    dsimp [d]
    exact_mod_cast (Int.floor_nonneg.mpr hδ0)
  have hdle : (d : ℝ) ≤ δ := by simpa [d] using Int.floor_le δ
  have hd : d ≤ PaperIV.IntegralStability.gamma*(n : ℚ)^2 := by
    exact_mod_cast (hdle.trans hδ)
  obtain ⟨R,hR,h2,hh,hbase,_,hreserve,hedit⟩ := hN n hn G hG d hd0 hd
    (fun Q hQ => lower_bound_floor_deficit (hlow Q hQ))
  have hbaseR : (0 : ℝ) ≤ (PaperIV.targetSize n : ℝ)-(PaperIV.splitBaseline n R.card : ℝ) := by
    exact_mod_cast (sub_nonneg.mpr hbase)
  have hresR : (PaperIV.targetSize n : ℝ)-(PaperIV.splitBaseline n R.card : ℝ) +
      (outsideEdges G R).card/16+(missingIncidences G R : ℝ)/2 ≤ (d : ℝ) := by
    have hh := hreserve
    have hc : (((PaperIV.targetSize n : ℚ)-PaperIV.splitBaseline n R.card +
        ((outsideEdges G R).card : ℚ)/16+(missingIncidences G R : ℚ)/2 : ℚ) : ℝ) ≤
        (d : ℝ) := by exact_mod_cast hh
    simpa only [Rat.cast_add, Rat.cast_sub, Rat.cast_div, Rat.cast_natCast,
      Rat.cast_ofNat] using hc
  have heR : (PaperIV.EditMetric.editDist G.edgeFinset
      (graphEdgeSupport (splitGraph R (Finset.univ \ R))) : ℝ) ≤ 16*(d : ℝ) := by
    exact_mod_cast hedit
  refine ⟨R,hR,h2,hh,heR.trans (by linarith),hbaseR,hresR.trans hdle,?_⟩
  intro Q τ hQ
  let t : ℚ := (Q.size : ℚ)-PaperIV.splitBaseline n R.card
  have hQt : (Q.size : ℚ) ≤ PaperIV.splitBaseline (Fintype.card (Fin n)) R.card+t := by
    simp [t]
  have hc := card_noncanonicalPieces_le R hR Q t hQt
  have hb := noncanonicalEdgeMass_le R hR Q t hQt
  have hcR : ((noncanonicalPieces R Q).card : ℝ) ≤
      (Q.size : ℝ)-(PaperIV.splitBaseline n R.card : ℝ)+
        missingIncidences G R+3*(outsideEdges G R).card := by
    dsimp [t] at hc
    exact_mod_cast hc
  have hbR : (noncanonicalEdgeMass R Q : ℝ) ≤
      10*((Q.size : ℝ)-(PaperIV.splitBaseline n R.card : ℝ)+
        missingIncidences G R+3*(outsideEdges G R).card) := by
    dsimp [t] at hb
    exact_mod_cast hb
  have hm : (0 : ℝ) ≤ (outsideEdges G R).card := Nat.cast_nonneg _
  have hA : (0 : ℝ) ≤ missingIncidences G R := Nat.cast_nonneg _
  constructor <;> nlinarith only [hcR,hbR,hQ,hresR,hdle,hbaseR,hm,hA]

end PaperIV.SublinearResearch
